#!/usr/bin/env sage
"""Reproduce the paper's Prop 5.3 hilb(G, 2) computation byte-for-byte,
using the determined-system formulation from the paper.

Paper's variable layout (different from my earlier guess):
  t0, t1, ..., tn   (n+1 vars, = theta_0, ..., theta_n)
  s0, s1, ..., sn   (n+1 vars, = psi_0, ..., psi_n)
  total = 2(n+1) = 2n+2

Paper's generators:
  t0                                    (theta_0 = 0, CICO input bit)
  tn - target_theta                     (theta_n = target)
  t_{i+1} - PHI*t_i - s_i^2 - c_i       (propagation of theta, QUADRATIC in s_i)
  s_{i+1} - PHI*s_i - t_{i+1}^2 - d_i   (propagation of psi, QUADRATIC in t_{i+1})

Total: 2 linear + 2n quadratic = 2n+2 gens.

After eliminating t0 and tn via the 2 linear eqs, we're left with
2n quadratic eqs in 2n unknowns. Semi-regular prediction:
  hilb(G, 2) numerator = (1+z)^{2n}
  d_reg = 2n + 1

Paper claims d_reg = 2n — one less, the 'non-generic syzygy' from Remark 5.4.
"""
from sage.all import *
from sage.interfaces.singular import singular
import hashlib
import time

BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
PHI = 7


def rc(seed, n):
    return [int.from_bytes(hashlib.sha256(f'{seed}_{i}'.encode()).digest(), 'big') % BN254
            for i in range(n)]


def forward_simulate(n, c, d, psi_0):
    theta, psi = 0, psi_0
    for i in range(n):
        theta = (PHI * theta + psi * psi + c[i]) % BN254
        psi = (PHI * psi + theta * theta + d[i]) % BN254
    return theta


def parse_intvec(s):
    s = str(s).strip().strip('"').strip()
    parts = [p.strip() for p in s.split(',') if p.strip()]
    out = []
    for p in parts:
        try:
            out.append(int(p))
        except ValueError:
            break
    return out


def run_n(n):
    print(f"\n{'='*70}")
    print(f"n = {n}  (paper's formulation)")
    print('='*70)
    c = rc('mambo_bn254_c', n)
    d = rc('mambo_bn254_d', n)
    psi_0 = 12345678901234567890
    target = forward_simulate(n, c, d, psi_0)

    vars_t = [f't{i}' for i in range(n + 1)]
    vars_s = [f's{i}' for i in range(n + 1)]
    all_vars = vars_t + vars_s

    singular.eval(f'ring Rpaper_n{n} = 0, ({",".join(all_vars)}), dp;')
    singular.eval('ideal I;')
    # I[1] = t0, I[2] = t_n - target
    singular.eval(f'I[1] = t0;')
    singular.eval(f'I[2] = t{n} - {target};')
    k = 3
    for i in range(n):
        singular.eval(f'I[{k}] = t{i+1} - {PHI}*t{i} - s{i}^2 - {c[i]};')
        k += 1
        singular.eval(f'I[{k}] = s{i+1} - {PHI}*s{i} - t{i+1}^2 - {d[i]};')
        k += 1

    size_I = int(singular.eval('size(I);').strip())
    n_vars = int(singular.eval('nvars(basering);').strip())
    print(f"  gens: {size_I}   vars: {n_vars}")

    t0 = time.time()
    singular.eval('ideal G = std(I);')
    dt = time.time() - t0
    gb_size = int(singular.eval('size(G);').strip())
    dim_I = int(singular.eval('dim(G);').strip())
    print(f"  groebner   {dt:6.2f}s   GB size = {gb_size}   dim(R/I) = {dim_I}")

    t0 = time.time()
    h2_str = singular.eval('string(hilb(G, 2));')
    coeffs = parse_intvec(h2_str)
    print(f"  hilb(G,2)  {time.time()-t0:6.2f}s")
    print(f"  raw: {h2_str.strip()}")
    print(f"  parsed ({len(coeffs)} coeffs): {coeffs}")

    Z = PolynomialRing(ZZ, 'z').gen()
    semi = ((1 + Z)**(2*n)).list()
    L = max(len(coeffs), len(semi))
    coeffs_p = coeffs + [0] * (L - len(coeffs))
    semi_p = semi + [0] * (L - len(semi))
    first_nonpos = None
    for dd in range(1, L):
        if coeffs_p[dd] <= 0:
            first_nonpos = dd
            break
    print(f"\n  {'deg':>4} | {'observed':>10} | {'semi-reg':>10} | {'gap':>6}")
    for dd in range(L):
        gap = semi_p[dd] - coeffs_p[dd]
        mark = ''
        if dd == first_nonpos:
            mark = '   <-- d_reg'
        print(f"  {dd:>4} | {coeffs_p[dd]:>10} | {semi_p[dd]:>10} | {gap:>+6}{mark}")
    print(f"\n  observed d_reg = {first_nonpos}")
    print(f"  paper claims   = {2*n}")
    print(f"  semi-reg value = {2*n + 1}")
    if first_nonpos == 2*n:
        print(f"  MATCHES PAPER ✓")
    elif first_nonpos == 2*n + 1:
        print(f"  MATCHES SEMI-REGULAR (no extra syzygy at this n)")
    else:
        print(f"  NEITHER — investigate")


if __name__ == '__main__':
    for n in [2, 3, 4, 5, 6, 7, 8]:
        run_n(n)
