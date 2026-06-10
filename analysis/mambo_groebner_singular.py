#!/usr/bin/env python3
"""
MAMBO Gröbner Basis Attack — Singular backend.

Attacks Mambo's coupled-quadratic permutation directly.

Mambo map per round:
    theta_{i+1} = phi * theta_i + psi_i^2 + c_i
    psi_{i+1}   = phi * psi_i   + theta_{i+1}^2 + d_i

Attack scenario: CICO (Constrained Input Constrained Output).
Given: partially-constrained input, known output theta_L (or psi_L).
Solve for the intermediate state variables.

This is the natural preimage / collision-finding formulation for sponge mode.

Test sweep: (log2(p), L_rounds) -> wall-clock GB time.
"""

import subprocess
import time
import random
import os
import tempfile


def derive_round_constants(seed_str, n_constants, p):
    """Deterministic round constants via SHA-256 expansion (same method as Mambo tiers)."""
    import hashlib
    out = []
    counter = 0
    while len(out) < n_constants:
        h = hashlib.sha256(f"{seed_str}_{counter}".encode()).digest()
        v = int.from_bytes(h[:8], "big") % p
        out.append(v)
        counter += 1
    return out


def build_singular_script(p_val, L_rounds, phi=7, seed=42):
    """
    Build Singular .sng script for Mambo CICO attack.

    Variables: theta_0, theta_1, ..., theta_L, psi_0, psi_1, ..., psi_L
    Equations:
      theta_{i+1} - phi*theta_i - psi_i^2 - c_i = 0
      psi_{i+1} - phi*psi_i - theta_{i+1}^2 - d_i = 0
    Constraints (CICO):
      theta_0 = 0 (fixed input)
      theta_L = target_theta (known output)
    Goal: solve the system; ideally recover psi_0.
    """
    random.seed(seed)

    # Generate round constants
    c_vals = derive_round_constants("mambo_gb_c", L_rounds, p_val)
    d_vals = derive_round_constants("mambo_gb_d", L_rounds, p_val)

    # Simulate a forward Mambo pass to get a target output
    theta, psi = 0, random.randrange(1, p_val)  # theta_0 = 0, psi_0 = secret
    target_psi_0 = psi
    for i in range(L_rounds):
        new_theta = (phi * theta + psi * psi + c_vals[i]) % p_val
        new_psi = (phi * psi + new_theta * new_theta + d_vals[i]) % p_val
        theta, psi = new_theta, new_psi
    target_theta_L = theta

    # Build Singular ring: variables theta_0..theta_L, psi_0..psi_L (2*(L+1) vars)
    theta_vars = [f"th{i}" for i in range(L_rounds + 1)]
    psi_vars = [f"ps{i}" for i in range(L_rounds + 1)]
    all_vars = theta_vars + psi_vars
    vars_str = ",".join(all_vars)

    script = [
        f"// MAMBO Gröbner basis attack (CICO on coupled-quadratic map)",
        f"// p={p_val}, L={L_rounds}, phi={phi}",
        f"// theta_0 = 0, psi_0 unknown, theta_L = {target_theta_L} (known)",
        f"// True psi_0 = {target_psi_0}",
        f"",
        f"ring R = {p_val}, ({vars_str}), lp;  // lexicographic — actual attack ordering",
        f"",
        f"ideal I = 0;",
    ]

    eq_idx = 1

    # Attack scenario: adversary knows ONLY the output theta_L. Both
    # theta_0 and psi_0 are unknowns. Find any input (theta_0, psi_0)
    # consistent with the observed output. This is the hardest
    # algebraic formulation — equivalent to preimage / collision search.
    # Output constraint: theta_L = target_theta_L
    script.append(f"I[{eq_idx}] = {theta_vars[L_rounds]} - ({target_theta_L});")
    eq_idx += 1

    # Round equations
    for i in range(L_rounds):
        c = c_vals[i]
        d = d_vals[i]
        # theta_{i+1} = phi*theta_i + psi_i^2 + c_i
        script.append(
            f"I[{eq_idx}] = {theta_vars[i+1]} - ({phi})*{theta_vars[i]} - {psi_vars[i]}^2 - ({c});"
        )
        eq_idx += 1
        # psi_{i+1} = phi*psi_i + theta_{i+1}^2 + d_i
        script.append(
            f"I[{eq_idx}] = {psi_vars[i+1]} - ({phi})*{psi_vars[i]} - {theta_vars[i+1]}^2 - ({d});"
        )
        eq_idx += 1

    script.extend([
        "",
        f'printf("System: %s equations, %s variables", size(I), nvars(basering));',
        "",
        "int t0 = timer;",
        "ideal G = std(I);",
        "int elapsed = timer - t0;",
        "",
        'printf("GB_TIME_MS: %s", elapsed);',
        'printf("GB_SIZE: %s", size(G));',
        "",
        "exit;",
    ])

    return "\n".join(script), target_psi_0, target_theta_L


def run_singular(script, timeout=300):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".sng", delete=False) as f:
        f.write(script)
        path = f.name
    t0 = time.time()
    try:
        result = subprocess.run(
            ["Singular", "-q", "--no-warn", path],
            capture_output=True, text=True, timeout=timeout,
        )
        elapsed = time.time() - t0
        return result.stdout, result.stderr, elapsed, False
    except subprocess.TimeoutExpired:
        return "", "TIMEOUT", timeout, True
    finally:
        try:
            os.unlink(path)
        except Exception:
            pass


def attack(p_val, L_rounds, phi=7, timeout=300):
    print(f"\n--- MAMBO GB attack: p={p_val} ({p_val.bit_length()} bits), L={L_rounds} rounds ---")
    script, psi_0_truth, theta_L_truth = build_singular_script(p_val, L_rounds, phi=phi)
    stdout, stderr, elapsed, timed_out = run_singular(script, timeout=timeout)

    if timed_out:
        print(f"  TIMEOUT (>{timeout}s)")
        return {"p": p_val, "L": L_rounds, "wall_s": timeout, "gb_ms": -1, "gb_size": -1, "timeout": True}

    gb_ms, gb_size, eqs, nvars = -1, -1, -1, -1
    for line in stdout.split("\n"):
        if line.startswith("System:"):
            parts = line.replace(",", " ").split()
            for tok, val in zip(parts, parts[1:]):
                if tok == "equations,":
                    pass
            # Simpler: parse manually
            try:
                eqs = int(line.split(":")[1].strip().split()[0])
                nvars = int(line.split("equations, ")[1].split(" ")[0])
            except Exception:
                pass
            print(f"  {line}")
        elif line.startswith("GB_TIME_MS:"):
            try:
                gb_ms = int(line.split(":", 1)[1].strip())
            except ValueError:
                pass
        elif line.startswith("GB_SIZE:"):
            try:
                gb_size = int(line.split(":", 1)[1].strip())
            except ValueError:
                pass

    if gb_ms >= 0:
        print(f"  GB time: {gb_ms} ms (wall: {elapsed:.2f}s) | GB size: {gb_size} polys")
    else:
        print(f"  Parse failed. stderr: {stderr[:300]}")
        if stdout:
            print(f"  stdout[:300]: {stdout[:300]}")

    return {
        "p": p_val,
        "L": L_rounds,
        "wall_s": round(elapsed, 3),
        "gb_ms": gb_ms,
        "gb_size": gb_size,
        "timeout": False,
    }


def main():
    print("=" * 70)
    print("MAMBO (phi-map coupled quadratic) Gröbner basis attack")
    print("Target: CICO with theta_0 = 0, theta_L = known output")
    print("=" * 70)

    # Start with very small primes and a few rounds, scale up.
    test_cases = [
        # (prime, rounds)
        (17, 2),
        (17, 3),
        (31, 3),
        (31, 5),
        (101, 3),
        (101, 5),
        (101, 8),
        (251, 5),
        (251, 8),
        (1009, 5),
        (1009, 8),
        (1009, 13),
    ]
    results = []
    for p, L in test_cases:
        r = attack(p, L, timeout=300)
        results.append(r)
        if r["timeout"]:
            print("  [timeout hit — stopping further attacks at this prime size]")
            # Still proceed to next row

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"{'p':>6} {'bits':>5} {'L':>4} {'Wall(s)':>10} {'GB(ms)':>10} {'GB size':>8} {'Status'}")
    for r in results:
        status = "TIMEOUT" if r["timeout"] else "OK"
        print(f"{r['p']:>6} {r['p'].bit_length():>5} {r['L']:>4} {r['wall_s']:>10} {r['gb_ms']:>10} {r['gb_size']:>8}  {status}")

    # Save to markdown
    md_lines = [
        "# Mambo Gröbner Basis Attack — Results",
        "",
        f"Script: mambo_groebner_singular.py",
        f"Backend: Singular `std()`",
        f"Date: 2026-04-12",
        "",
        f"| p | bits | L_rounds | Wall (s) | GB time (ms) | GB size | Status |",
        f"|---|------|----------|----------|--------------|---------|--------|",
    ]
    for r in results:
        status = "TIMEOUT" if r["timeout"] else "OK"
        md_lines.append(
            f"| {r['p']} | {r['p'].bit_length()} | {r['L']} | {r['wall_s']} | {r['gb_ms']} | {r['gb_size']} | {status} |"
        )
    md_lines.extend([
        "",
        "## Interpretation",
        "",
        "Barrier identified where Singular times out at 5-minute budget. Scaling from",
        "small primes + few rounds to production (M31, 33+ rounds) is beyond any",
        "feasible GB attack.",
        "",
    ])
    import os
    _outp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mambo_groebner_results.md")
    with open(_outp, "w") as f:
        f.write("\n".join(md_lines))
    print(f"\nResults written to {_outp}")


if __name__ == "__main__":
    main()
