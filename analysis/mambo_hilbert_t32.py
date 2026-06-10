#!/usr/bin/env python3
"""
Mambo t=32 (super-wide state) Hilbert-series / regularity-degree analysis.

Mirrors mambo_hilbert_series.py but for state width T=32. The wider-state
variant is not yet locked in the security analysis; this script measures the
degree of regularity d_reg under the semi-regularity heuristic so we can
cite t=32 tier round counts (n=5 STANDARD / n=7 HIGH / n=9 MAXIMUM) with
empirical evidence rather than pure D_I-tightness arithmetic.

Over a t=T state, each round introduces T new state variables and T
squaring-coupled constraints:
  x_1^{(r+1)} = phi * x_1^{(r)} + x_T^{(r)}^2 + c_{r,1}
  x_i^{(r+1)} = phi * x_i^{(r)} + x_{i-1}^{(r+1)}^2 + c_{r,i}   for i in 2..T

Total: T*(N+1) variables, T*N constraints (plus a target boundary).

For T=32 even n=2 is a 96-variable / 64-constraint system — substantially
heavier than T=2 at the same n. Singular's standard-basis computation
typically dominates wall-time; we cap each n at 30 minutes.
"""

import subprocess
import time
import hashlib
import sys


BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
PHI = 7
T = int(__import__('os').environ.get('MAMBO_T', '32'))
TIMEOUT_SEC = int(__import__('os').environ.get('MAMBO_TIMEOUT_SEC', '1800'))


def rc(seed, n_total):
    out = []
    for i in range(n_total):
        h = hashlib.sha256(f"{seed}_{i}".encode()).digest()
        out.append(int.from_bytes(h, "big") % BN254)
    return out


def forward_simulate(n, rcs, initial_state):
    state = list(initial_state)
    for r in range(n):
        new_state = [0] * T
        new_state[0] = (PHI * state[0] + state[T - 1] * state[T - 1] + rcs[r * T + 0]) % BN254
        for i in range(1, T):
            new_state[i] = (PHI * state[i] + new_state[i - 1] * new_state[i - 1] + rcs[r * T + i]) % BN254
        state = new_state
    return state


def build_script(n, rcs, initial_state, target_state):
    """Standard-basis + Hilbert series Singular script for T=32.

    Classical algebraic cryptanalysis setup: attacker knows one field element
    of the output (x{n}_0 = target) and wants to solve for unknown initial
    state. All other positions are free variables. This matches the D_I
    attack model on the Mambo primitive.
    """
    vars_by_round = []
    for r in range(n + 1):
        row = [f"x{r}_{i}" for i in range(T)]
        vars_by_round.append(row)
    all_vars = ",".join(v for row in vars_by_round for v in row)

    lines = [
        f"ring R = 0, ({all_vars}), dp;",
    ]

    gens = []

    # Forward constraints — no boundary pins on initial or intermediate state.
    # All (theta, psi)-style state variables are unknowns; constraints relate
    # adjacent rounds.
    for r in range(n):
        c0 = rcs[r * T + 0]
        gens.append(f"x{r+1}_0 - {PHI}*x{r}_0 - x{r}_{T-1}^2 - {c0}")
        for i in range(1, T):
            c_i = rcs[r * T + i]
            gens.append(f"x{r+1}_{i} - {PHI}*x{r}_{i} - x{r+1}_{i-1}^2 - {c_i}")

    # Boundary: only pin one output value at x{n}_0 (single-element leak).
    # This is the minimal D_I attack setup.
    gens.append(f"x{n}_0 - {target_state[0]}")

    lines.append("ideal I = " + ", ".join(gens) + ";")
    lines.append("int t_start = rtimer;")
    lines.append("ideal G = std(I);")
    lines.append("int t_end = rtimer;")
    lines.append("intvec hs2 = hilb(G, 2);")
    lines.append('print("STD_MS"); print(t_end - t_start);')
    lines.append('print("HILB_START");')
    lines.append('print(hs2);')
    lines.append('print("HILB_END");')
    lines.append("exit;")
    return "\n".join(lines) + "\n"


def run_one(n):
    rcs = rc("mambo_t32_bn254", n * T)
    # Seed a specific (deterministic) initial state so the target is reproducible.
    initial = [((12345678901234567 * (i + 1)) % BN254) for i in range(T)]
    target = forward_simulate(n, rcs, initial)
    script = build_script(n, rcs, initial, target)
    script_path = f"/tmp/mambo_hilb_t32_n{n}.sng"
    with open(script_path, "w") as f:
        f.write(script)

    t0 = time.time()
    try:
        r = subprocess.run(
            ["Singular", "-q", script_path],
            capture_output=True, text=True, timeout=TIMEOUT_SEC,
        )
        wall = time.time() - t0
        out = r.stdout.strip()
        std_ms = None
        hilb_lines = []
        in_hilb = False
        for line in out.split("\n"):
            line = line.strip()
            if line == "STD_MS":
                continue
            if line.isdigit() and std_ms is None:
                std_ms = int(line)
                continue
            if line == "HILB_START":
                in_hilb = True
                continue
            if line == "HILB_END":
                in_hilb = False
                continue
            if in_hilb:
                hilb_lines.append(line)

        hs_raw = ",".join(hilb_lines).replace(" ", "")
        hs = []
        for tok in hs_raw.split(","):
            tok = tok.strip()
            if tok == "":
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
        return {
            "n": n,
            "wall_s": wall,
            "std_ms": std_ms,
            "hs_prefix": hs[:15],
            "d_reg": d_reg,
            "vars": T * (n + 1),
            "constraints": T * n + 1,
            "ok": r.returncode == 0,
            "stderr": r.stderr[:200],
        }
    except subprocess.TimeoutExpired:
        return {
            "n": n,
            "wall_s": TIMEOUT_SEC,
            "ok": False,
            "stderr": "TIMEOUT",
            "vars": T * (n + 1),
            "constraints": T * n + 1,
        }


def main():
    print(f"Mambo t={T} Hilbert series at BN254 (p ~ 2^254), phi = {PHI}")
    print(f"Singular standard-basis + hilb() method, timeout {TIMEOUT_SEC}s per n")
    print()
    print(f"{'n':>3}  {'vars':>5}  {'cons':>5}  {'wall_s':>8}  {'std_ms':>8}  {'d_reg':>6}  {'hs[0:12]'}")
    for n in range(2, 6):
        r = run_one(n)
        if not r.get("ok"):
            print(f"{n:>3}  {r.get('vars', '-'):>5}  {r.get('constraints','-'):>5}  -  FAIL: {r.get('stderr','?')[:80]}")
            break
        print(f"{r['n']:>3}  {r['vars']:>5}  {r['constraints']:>5}  {r['wall_s']:>8.2f}  "
              f"{(r['std_ms'] if r['std_ms'] is not None else -1):>8}  "
              f"{(r['d_reg'] if r['d_reg'] is not None else -1):>6}  "
              f"{r['hs_prefix']}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
