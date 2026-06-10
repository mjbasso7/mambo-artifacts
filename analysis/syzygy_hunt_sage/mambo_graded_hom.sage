#!/usr/bin/env sage
"""Homogenize the Mambo paper ideal, then compute clean graded Betti numbers.

Homogenization: add variable h. For each generator, multiply every term
by the appropriate power of h to make it homogeneous of its top degree.
- Linear gens (t_0, t_n - target): stay degree 1, replace any constant
  coefficient c with c*h.
- Quadratic propagation gens t_{i+1} - PHI*t_i - s_i^2 - c_i: this is
  degree 2 in s_i^2 but degree 1 in t_{i+1}, PHI*t_i. After homogenization:
  t_{i+1}*h - PHI*t_i*h - s_i^2 - c_i*h^2

The graded Betti table of R_hom/I_hom reveals exactly where the
non-generic structure compresses the Koszul complex.
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


def run_n(n):
    print(f"\n{'='*70}")
    print(f"n = {n}  (homogenized)")
    print('='*70)
    c = rc('mambo_bn254_c', n)
    d_vals = rc('mambo_bn254_d', n)
    psi_0 = 12345678901234567890
    target = forward_simulate(n, c, d_vals, psi_0)

    names = [f't{i}' for i in range(n+1)] + [f's{i}' for i in range(n+1)] + ['h']
    singular.eval(f'ring Rhn{n} = 0, ({",".join(names)}), dp;')
    singular.eval('ideal I;')
    # Linear: t0 homogeneous degree 1. (t_n - target*h) homogeneous degree 1.
    singular.eval('I[1] = t0;')
    singular.eval(f'I[2] = t{n} - {target}*h;')
    k = 3
    for i in range(n):
        # t_{i+1}*h - PHI*t_i*h - s_i^2 - c_i*h^2  (homogeneous degree 2)
        singular.eval(f'I[{k}] = t{i+1}*h - {PHI}*t{i}*h - s{i}^2 - {c[i]}*h^2;')
        k += 1
        singular.eval(f'I[{k}] = s{i+1}*h - {PHI}*s{i}*h - t{i+1}^2 - {d_vals[i]}*h^2;')
        k += 1

    # Verify homogeneity
    hom_flag = int(singular.eval('homog(I);').strip())
    print(f"  homogeneous? {hom_flag} (1 = yes)")

    hs = singular.eval('string(hilb(std(I), 2));').strip()
    print(f"  hilb(G, 2) = {hs}")

    t0 = time.time()
    singular.eval('resolution F = mres(I, 0);')
    print(f"  mres       {time.time()-t0:6.2f}s")

    length = int(singular.eval('size(F);').strip())
    print(f"  resolution length = {length}")

    # Now for homogeneous ideals, betti(F) is clean
    singular.eval('intmat B = betti(F);')
    nrows = int(singular.eval('nrows(B);').strip())
    ncols = int(singular.eval('ncols(B);').strip())
    print(f"  Betti matrix: {nrows} rows x {ncols} cols")

    # Print
    print(f"\n  Betti table (rows = degree shift d, cols = step i):")
    header = "    d  " + " ".join(f"i={i:>2}" for i in range(ncols))
    print(header)
    for row in range(1, nrows + 1):
        d = row - 1
        vals = []
        for col in range(1, ncols + 1):
            v = int(singular.eval(f'B[{row}, {col}];').strip())
            vals.append(v)
        row_str = "    " + f"{d:>2}  " + " ".join(f"{v:>4}" for v in vals)
        print(row_str)


if __name__ == '__main__':
    for n in [2, 3, 4, 5]:
        run_n(n)
