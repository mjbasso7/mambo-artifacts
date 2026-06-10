#!/usr/bin/env python3
"""
Mambo Gröbner basis computation at BN254 scalar field.

Uses Singular (the GB engine that SageMath also uses under the hood).
BN254 is the scalar field of the BN254 pairing curve, a common ZK field.

p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
  ~ 2^254

The Mambo CICO setup:
- Unknowns: theta_1, ..., theta_{n-1}, psi_0, ..., psi_{n-1}
- theta_0 = 0 (fixed), theta_n = target (known)
- For each round i:
    theta_{i+1} - phi*theta_i - psi_i^2 - c_i = 0
    psi_{i+1} - phi*psi_i - theta_{i+1}^2 - d_i = 0

Runs at n = 2, 3, 4, 5, 6 until timeout. Records wall-clock and GB size.
"""
import subprocess
import time
import hashlib
import sys
import os

BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
PHI = 7
TIMEOUT_SEC = 600  # 10 min per config


def rc(seed, n):
    """Derive round constants deterministically."""
    out = []
    for i in range(n):
        h = hashlib.sha256(f"{seed}_{i}".encode()).digest()
        out.append(int.from_bytes(h, "big") % BN254)
    return out


def forward_simulate(n, c_vals, d_vals, psi_0):
    """Forward Mambo from (0, psi_0) to get target theta_n."""
    theta, psi = 0, psi_0
    for i in range(n):
        theta_new = (PHI * theta + psi * psi + c_vals[i]) % BN254
        psi_new = (PHI * psi + theta_new * theta_new + d_vals[i]) % BN254
        theta, psi = theta_new, psi_new
    return theta


def build_script(n, c_vals, d_vals, target_theta_n):
    """Build a Singular script for GB computation."""
    # Variables: t0, t1, ..., tn, s0, s1, ..., sn
    vars_t = ",".join(f"t{i}" for i in range(n + 1))
    vars_s = ",".join(f"s{i}" for i in range(n + 1))
    all_vars = f"{vars_t},{vars_s}"

    # Use lex order so that the GB computation is forced to eliminate
    # all variables in favor of s0 — this is what turns the trivial DP
    # forward-simulation GB into a genuine elimination with degree blow-up.
    lines = [
        f"ring R = (integer, {BN254}), ({all_vars}), lp;",
    ]
    # Build ideal
    gen_list = [f"t0", f"t{n} - {target_theta_n}"]
    for i in range(n):
        gen_list.append(f"t{i+1} - {PHI}*t{i} - s{i}^2 - {c_vals[i]}")
        gen_list.append(f"s{i+1} - {PHI}*s{i} - t{i+1}^2 - {d_vals[i]}")
    ideal_str = "ideal I = " + ", ".join(gen_list) + ";"
    lines.append(ideal_str)
    lines.append("int t_start = rtimer;")
    lines.append("ideal G = groebner(I);")
    lines.append("int t_end = rtimer;")
    lines.append('print("GB_MS");')
    lines.append("print(t_end - t_start);")
    lines.append('print("GB_SIZE");')
    lines.append("print(size(G));")
    lines.append("exit;")
    return "\n".join(lines) + "\n"


def run_one(n):
    """Run GB at round count n. Return (wall_s, gb_ms, gb_size, ok)."""
    c_vals = rc("mambo_bn254_c", n)
    d_vals = rc("mambo_bn254_d", n)
    # Pick an arbitrary psi_0 to simulate forward
    psi_0 = 12345678901234567890
    target = forward_simulate(n, c_vals, d_vals, psi_0)

    script = build_script(n, c_vals, d_vals, target)
    script_path = f"/tmp/mambo_gb_n{n}.sng"
    with open(script_path, "w") as f:
        f.write(script)

    t0 = time.time()
    try:
        r = subprocess.run(
            ["Singular", "-q", script_path],
            capture_output=True, text=True, timeout=TIMEOUT_SEC,
        )
        wall = time.time() - t0
        out = r.stdout.strip().split("\n")
        gb_ms, gb_size = None, None
        for i, line in enumerate(out):
            if line == "GB_MS" and i + 1 < len(out):
                gb_ms = int(out[i + 1])
            if line == "GB_SIZE" and i + 1 < len(out):
                gb_size = int(out[i + 1])
        if r.returncode != 0:
            return wall, gb_ms, gb_size, False, r.stderr[:200]
        return wall, gb_ms, gb_size, True, ""
    except subprocess.TimeoutExpired:
        return TIMEOUT_SEC, None, None, False, f"TIMEOUT at {TIMEOUT_SEC}s"


def main():
    print(f"Mambo Gröbner basis at BN254 (p ~ 2^254), phi = {PHI}")
    print(f"Singular engine (same backend as SageMath)")
    print(f"Timeout per n: {TIMEOUT_SEC}s")
    print()
    print(f"{'n':>3}  {'vars':>5}  {'eqs':>5}  {'wall_s':>10}  {'gb_ms':>10}  {'gb_size':>8}  status")
    for n in range(2, 9):
        n_vars = 2 * (n + 1)
        n_eqs = 2 + 2 * n
        wall, gb_ms, gb_size, ok, err = run_one(n)
        status = "OK" if ok else f"FAIL: {err[:80]}"
        print(f"{n:>3}  {n_vars:>5}  {n_eqs:>5}  {wall:>10.2f}  "
              f"{(gb_ms if gb_ms is not None else -1):>10}  "
              f"{(gb_size if gb_size is not None else -1):>8}  {status}")
        sys.stdout.flush()
        if not ok and "TIMEOUT" in err:
            break


if __name__ == "__main__":
    main()
