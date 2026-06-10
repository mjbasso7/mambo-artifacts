#!/usr/bin/env sage
"""Extend d_reg / HS measurement to n=9, 10 on the paper's formulation.
Confirms the (1+z)^(2n-1) affine HS and 2^(2n-1) solution count patterns
hold at the upper bound of what the paper tests."""
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
    print(f"n = {n}")
    print('='*70)
    c = rc('mambo_bn254_c', n)
    d_vals = rc('mambo_bn254_d', n)
    psi_0 = 12345678901234567890
    target = forward_simulate(n, c, d_vals, psi_0)

    names = [f't{i}' for i in range(n+1)] + [f's{i}' for i in range(n+1)]
    singular.eval(f'ring Rn{n} = 0, ({",".join(names)}), dp;')
    singular.eval('ideal I;')
    singular.eval('I[1] = t0;')
    singular.eval(f'I[2] = t{n} - {target};')
    k = 3
    for i in range(n):
        singular.eval(f'I[{k}] = t{i+1} - {PHI}*t{i} - s{i}^2 - {c[i]};')
        k += 1
        singular.eval(f'I[{k}] = s{i+1} - {PHI}*s{i} - t{i+1}^2 - {d_vals[i]};')
        k += 1

    t0 = time.time()
    singular.eval('ideal G = std(I);')
    dt = time.time() - t0
    print(f"  groebner    {dt:6.2f}s")

    t0 = time.time()
    hs = singular.eval('string(hilb(G, 2));').strip()
    print(f"  hilb(G, 2)  {time.time()-t0:6.2f}s")
    print(f"  raw: {hs}")
    coeffs = [int(p.strip()) for p in hs.split(',') if p.strip().lstrip('-').isdigit()]
    solution_count = sum(coeffs)
    print(f"  parsed: {coeffs}")
    print(f"  dim R/I = sum = {solution_count}")
    print(f"  expected 2^(2n-1) = {2**(2*n-1)}")
    print(f"  match: {solution_count == 2**(2*n-1)}")

    # Check pattern (1+z)^(2n-1)
    Z = PolynomialRing(ZZ, 'z').gen()
    pred = ((1 + Z)**(2*n - 1)).list()
    print(f"  (1+z)^(2n-1) = {pred}")
    match = coeffs[:len(pred)] == pred and all(c == 0 for c in coeffs[len(pred):])
    print(f"  matches (1+z)^(2n-1): {match}")


if __name__ == '__main__':
    for n in [6, 7, 8, 9, 10]:
        run_n(n)
