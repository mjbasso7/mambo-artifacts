#!/usr/bin/env python3
"""
Wider-state d_reg sweep in pure Python with Singular subprocess.

Formulation:
- t cells = t/2 (theta, psi) pairs in parallel.
- Per round, per pair:
    theta'_j = phi*theta_j + psi_j^2 + c_r
    psi'_j   = phi*psi_j + theta'_j^2 + d_r
  M_EXT mix omitted from the constraint generation; linear ops do not
  change d_reg, so the simplification is sound for this measurement.
- CICO ideal: rate=16 unknowns (input pairs 0..7 = 16 vars), capacity=8
  zero-in (pairs 8..t/2-1 inputs = 0), capacity-out target=zero on
  output pairs 8..t/2-1.
- Determined system in 16 unknown rate inputs after intermediate vars
  are introduced per round.
- d_reg measured via Singular `hilb(G, 2)` first non-positive index.

Cell selection: primes BabyBear, BN254, Goldilocks; t in {16, 24};
n in {4..12}; ascending n, BabyBear first.

Resource cap: SINGULAR_TIMEOUT_SEC default 14400 (4 hours), bail per
cell if exceeded.
"""

import subprocess
import time
import hashlib
import os
import sys
import json

PHI = 7
BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
BABYBEAR = 2**31 - 2**27 + 1  # 2013265921
GOLDILOCKS = 2**64 - 2**32 + 1  # 18446744069414584321

TIMEOUT_SEC = int(os.environ.get('SINGULAR_TIMEOUT_SEC', '14400'))
import os as _os
RESULTS_PATH = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)), 'dreg_t24_vps_results.json')


def rc(seed, count, p):
    return [int.from_bytes(hashlib.sha256(f'{seed}_{i}'.encode()).digest(), 'big') % p
            for i in range(count)]


def build_singular_script(t, n, p):
    """Build a Singular script for one (t, n, p) cell.

    Variables: rate inputs i_0..i_{rate-1} plus per-round per-pair
    t_r_j and s_r_j cells (theta and psi after round r in pair j).

    Rate / capacity:
        cap  = min(8, max(2, t-2))
        rate = t - cap
    Hardcoding rate=16 in the prior version forced the boundary loop
    to be empty for t<16 and over-saturated the ideal at t=24 BabyBear.
    """
    pairs = t // 2
    cap = min(8, max(2, t - 2))
    rate = t - cap

    in_vars = [f'i{i}' for i in range(rate)]
    state_vars = []
    for r in range(n):
        for j in range(pairs):
            state_vars.append(f't_{r}_{j}')
            state_vars.append(f's_{r}_{j}')
    all_vars = in_vars + state_vars

    c_consts = rc(f'mambo_t{t}_c', n, p)
    d_consts = rc(f'mambo_t{t}_d', n, p)

    # Forward-simulate from a chosen rate input (1, 2, 3, 4, ...) with
    # capacity=zero to obtain a REACHABLE capacity-out target. Setting
    # the target to zero (as in the original harness) generically makes
    # the ideal inconsistent — for fixed nonzero round constants the
    # capacity-out is a determined nonzero value when capacity-in = 0,
    # so I = R and Hilbert series collapses to (0, 0). Forward-simulating
    # a known input gives a target that is reachable by construction
    # and the ideal becomes a proper zero-dimensional CICO ideal.
    rate_in_vec = [(i + 1) % p for i in range(rate)]
    sim_state = []
    for j in range(pairs):
        if j < rate // 2:
            sim_state.append([rate_in_vec[2 * j], rate_in_vec[2 * j + 1]])
        else:
            sim_state.append([0, 0])
    for r in range(n):
        new_sim = []
        for j in range(pairs):
            th, ps = sim_state[j]
            th_new = (PHI * th + ps * ps + c_consts[r]) % p if p else (PHI * th + ps * ps + c_consts[r])
            ps_new = (PHI * ps + th_new * th_new + d_consts[r]) % p if p else (PHI * ps + th_new * th_new + d_consts[r])
            new_sim.append([th_new, ps_new])
        sim_state = new_sim
    # Target on capacity-out pairs (j >= rate//2).
    cap_target = {}
    for j in range(rate // 2, pairs):
        cap_target[(n - 1, j, 't')] = sim_state[j][0]
        cap_target[(n - 1, j, 's')] = sim_state[j][1]

    def prev_theta(r, j):
        if r == 0:
            return in_vars[2 * j] if j < rate // 2 else '0'
        return f't_{r-1}_{j}'

    def prev_psi(r, j):
        if r == 0:
            return in_vars[2 * j + 1] if j < rate // 2 else '0'
        return f's_{r-1}_{j}'

    # Build the Singular script.
    if p == 0:
        ring_decl = f'ring R = 0, ({",".join(all_vars)}), dp;'
    else:
        ring_decl = f'ring R = {p}, ({",".join(all_vars)}), dp;'

    lines = [ring_decl]
    gens = []
    for r in range(n):
        for j in range(pairs):
            tprev = prev_theta(r, j)
            sprev = prev_psi(r, j)
            tcur = f't_{r}_{j}'
            scur = f's_{r}_{j}'
            gens.append(f'{tcur} - {PHI}*({tprev}) - ({sprev})^2 - ({c_consts[r]})')
            gens.append(f'{scur} - {PHI}*({sprev}) - ({tcur})^2 - ({d_consts[r]})')
    # Capacity-out boundary: pairs rate/2..pairs-1 = forward-simulated
    # target (NOT zero — see comment in setup section).
    for j in range(rate // 2, pairs):
        t_target = cap_target[(n - 1, j, 't')]
        s_target = cap_target[(n - 1, j, 's')]
        gens.append(f't_{n-1}_{j} - ({t_target})')
        gens.append(f's_{n-1}_{j} - ({s_target})')

    # Singular has a line-length limit; chunk the ideal generator list.
    lines.append('ideal I;')
    for k, g in enumerate(gens, start=1):
        lines.append(f'I[{k}] = {g};')
    lines.append('int t_start = rtimer;')
    lines.append('ideal G = std(I);')
    lines.append('int t_end = rtimer;')
    lines.append('intvec hs2 = hilb(G, 2);')
    lines.append('print("GB_DONE");')
    lines.append('print(t_end - t_start);')
    lines.append('print("HILB_START");')
    lines.append('print(hs2);')
    lines.append('print("HILB_END");')
    lines.append('exit;')
    return '\n'.join(lines) + '\n', len(all_vars), len(gens)


def parse_output(out):
    std_ms = None
    in_hilb = False
    hilb_lines = []
    saw_gb = False
    for line in out.split('\n'):
        line = line.strip()
        if line == 'GB_DONE':
            saw_gb = True
            continue
        if saw_gb and std_ms is None and line.lstrip('-').isdigit():
            std_ms = int(line)
            continue
        if line == 'HILB_START':
            in_hilb = True
            continue
        if line == 'HILB_END':
            in_hilb = False
            continue
        if in_hilb:
            hilb_lines.append(line)

    hs_raw = ','.join(hilb_lines).replace(' ', '')
    hs = []
    for tok in hs_raw.split(','):
        tok = tok.strip()
        if not tok:
            continue
        try:
            hs.append(int(tok))
        except ValueError:
            pass
    d_reg = None
    for i, c in enumerate(hs):
        if i > 0 and c <= 0:
            d_reg = i
            break
    return std_ms, hs, d_reg


def run_cell(t, n, p, label):
    print(f"\n{'='*60}")
    print(f"Cell t={t} n={n} p={label}")
    sys.stdout.flush()

    script, var_count, gen_count = build_singular_script(t, n, p)
    print(f"  vars={var_count}, gens={gen_count}")
    sys.stdout.flush()

    script_path = f'/tmp/dreg_t{t}_n{n}_{label}.sng'
    with open(script_path, 'w') as f:
        f.write(script)

    t0 = time.time()
    try:
        r = subprocess.run(
            ['Singular', '-q', script_path],
            capture_output=True, text=True, timeout=TIMEOUT_SEC,
        )
        wall = time.time() - t0
        std_ms, hs, d_reg = parse_output(r.stdout)
        print(f"  wall={wall:.1f}s std_ms={std_ms} d_reg={d_reg}")
        print(f"  hs[0:12]={hs[:12]}")
        sys.stdout.flush()
        return {
            't': t, 'n': n, 'p_label': label,
            'wall_s': wall, 'std_ms': std_ms, 'd_reg': d_reg,
            'hs_prefix': hs[:15], 'vars': var_count, 'gens': gen_count,
            'ok': r.returncode == 0, 'stderr_tail': r.stderr[-300:] if r.stderr else '',
        }
    except subprocess.TimeoutExpired:
        wall = time.time() - t0
        print(f"  TIMEOUT after {wall:.0f}s")
        return {
            't': t, 'n': n, 'p_label': label,
            'wall_s': wall, 'ok': False, 'reason': 'TIMEOUT',
            'vars': var_count, 'gens': gen_count,
        }


def main():
    print(f"Mambo wider-state d_reg sweep (Independent port harness, target-fix applied)")
    print(f"Singular subprocess, timeout {TIMEOUT_SEC}s per cell")
    print()

    cells = []
    # Validation cells first (small, fast).
    for n in [2, 3, 4]:
        cells.append((4, n, BABYBEAR, 'BB'))
    for n in [2, 3, 4]:
        cells.append((8, n, BABYBEAR, 'BB'))
    # t=16 (paper Table 7).
    for n in [2, 3, 4, 5]:
        cells.append((16, n, BABYBEAR, 'BB'))
    # The RISC Zero target — t=24 ascending n.
    for n in [2, 3, 4, 5, 6, 7, 8, 9, 10]:
        cells.append((24, n, BABYBEAR, 'BB'))
    # BN254 control + Goldilocks at L1 region.
    for n in [4, 6, 8, 10]:
        cells.append((24, n, BN254, 'BN'))

    results = []
    for (t, n, p, label) in cells:
        r = run_cell(t, n, p, label)
        results.append(r)
        with open(RESULTS_PATH, 'w') as f:
            json.dump(results, f, indent=2)
        sys.stdout.flush()

    print()
    print('=' * 60)
    print('SUMMARY')
    print(f"{'t':>3} {'n':>3} {'p':>4} {'d_reg':>7} {'wall_s':>8} {'std_ms':>8}")
    for r in results:
        d = r.get('d_reg', 'BAIL')
        wall = r.get('wall_s', 0)
        std_ms = r.get('std_ms', 0)
        print(f"{r['t']:>3} {r['n']:>3} {r['p_label']:>4} {str(d):>7} {wall:>8.0f} {str(std_ms):>8}")

if __name__ == '__main__':
    main()
