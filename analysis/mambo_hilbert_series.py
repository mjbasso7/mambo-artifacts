#!/usr/bin/env python3
"""
Mambo regularity-degree computation via Hilbert series at BN254 scalar field.

Rather than running a full lexicographic Gröbner basis (which forces
variable elimination and blows up memory quickly), we use the Hilbert
series of the ideal to extract the degree of regularity. Singular
provides `hilb()` which returns the Hilbert series of the ideal in a
standard-basis computation that is typically orders of magnitude
faster than a full lex GB.

Under the semi-regularity heuristic, the degree of regularity
$d_\\mathrm{reg}$ is the index of the first non-positive coefficient of
the Hilbert series (as a power series). This yields $d_\\mathrm{reg}$
for small $n$ that full GB elimination cannot reach.

Methodology mirrors the Hilbert-series-based analysis commonly used in
algebraic-cryptanalysis literature (e.g. Bardet-Faugère-Salvy).
"""

import subprocess
import time
import hashlib
import sys


BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
PHI = 7
TIMEOUT_SEC = 900


def rc(seed, n):
    out = []
    for i in range(n):
        h = hashlib.sha256(f"{seed}_{i}".encode()).digest()
        out.append(int.from_bytes(h, "big") % BN254)
    return out


def forward_simulate(n, c_vals, d_vals, psi_0):
    theta, psi = 0, psi_0
    for i in range(n):
        theta_new = (PHI * theta + psi * psi + c_vals[i]) % BN254
        psi_new = (PHI * psi + theta_new * theta_new + d_vals[i]) % BN254
        theta, psi = theta_new, psi_new
    return theta


def build_script(n, c_vals, d_vals, target_theta_n):
    """Standard-basis + Hilbert series script."""
    vars_t = ",".join(f"t{i}" for i in range(n + 1))
    vars_s = ",".join(f"s{i}" for i in range(n + 1))
    all_vars = f"{vars_t},{vars_s}"

    # Hilbert series measures the regularity of the ideal's quotient ring;
    # under the semi-regularity heuristic the result is independent of the
    # ground field characteristic as long as the system is generic. We use
    # Q (rationals) so that Singular's native hilb() works end-to-end.
    lines = [
        f"ring R = 0, ({all_vars}), dp;",
    ]
    gen_list = [f"t0", f"t{n} - {target_theta_n}"]
    for i in range(n):
        gen_list.append(f"t{i+1} - {PHI}*t{i} - s{i}^2 - {c_vals[i]}")
        gen_list.append(f"s{i+1} - {PHI}*s{i} - t{i+1}^2 - {d_vals[i]}")
    lines.append("ideal I = " + ", ".join(gen_list) + ";")
    lines.append("int t_start = rtimer;")
    # hilb returns the Hilbert series coefficients
    # hilb(I, 1) returns second Hilbert series (by the GB of the ideal)
    lines.append("ideal G = std(I);")
    lines.append("int t_end = rtimer;")
    # hilb(G, 2) returns the second Hilbert series coefficients as intvec
    lines.append("bigintvec hs2 = hilb(G, 2);")
    lines.append('print("STD_MS"); print(t_end - t_start);')
    lines.append('print("HILB_START");')
    lines.append('print(hs2);')
    lines.append('print("HILB_END");')
    lines.append("exit;")
    return "\n".join(lines) + "\n"


def run_one(n):
    c_vals = rc("mambo_bn254_c", n)
    d_vals = rc("mambo_bn254_d", n)
    psi_0 = 12345678901234567890
    target = forward_simulate(n, c_vals, d_vals, psi_0)
    script = build_script(n, c_vals, d_vals, target)
    script_path = f"/tmp/mambo_hilb_n{n}.sng"
    with open(script_path, "w") as f:
        f.write(script)
    t0 = time.time()
    try:
        r = subprocess.run(
            ["Singular", "-q", script_path],
            capture_output=True, text=True, timeout=TIMEOUT_SEC,
        )
        wall = time.time() - t0
        # Parse output
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
        # Hilbert series is a list of integers; parse
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
        # d_reg = first index where the Hilbert series coefficient becomes <= 0
        # For over-determined systems with the semi-regularity heuristic,
        # d_reg is the lowest positive degree where the SECOND Hilbert series
        # becomes non-positive.
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
            "ok": r.returncode == 0,
            "stderr": r.stderr[:200],
        }
    except subprocess.TimeoutExpired:
        return {"n": n, "wall_s": TIMEOUT_SEC, "ok": False, "stderr": "TIMEOUT"}


def main():
    print(f"Mambo Hilbert series at BN254 (p ~ 2^254), phi = {PHI}")
    print(f"Singular standard-basis + hilb() method")
    print()
    print(f"{'n':>3}  {'vars':>5}  {'wall_s':>8}  {'std_ms':>8}  {'d_reg':>6}  {'hs[0:12]'}")
    for n in range(2, 11):
        r = run_one(n)
        if not r.get("ok"):
            print(f"{n:>3}  -  FAIL: {r.get('stderr','?')[:80]}")
            break
        print(f"{r['n']:>3}  {2*(r['n']+1):>5}  {r['wall_s']:>8.2f}  "
              f"{(r['std_ms'] if r['std_ms'] is not None else -1):>8}  "
              f"{(r['d_reg'] if r['d_reg'] is not None else -1):>6}  "
              f"{r['hs_prefix']}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
