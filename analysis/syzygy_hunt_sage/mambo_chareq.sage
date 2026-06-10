#!/usr/bin/env sage
"""Characteristic-independence check: re-run d_reg over small finite
fields (F_{small p}) to confirm the paper's claim that the Hilbert
series is characteristic-independent.

Paper states: 'the equations contain no characteristic-specific
identities, the Hilbert series is independent of the ground field'.
This script verifies that over F_p for small primes p."""
from sage.all import *
from sage.interfaces.singular import singular
import hashlib
import time

PHI = 7

TEST_PRIMES = [101, 257, 1009, 7919]  # small primes, none divides PHI=7


def rc_over_Fp(seed, n, p):
    return [int.from_bytes(hashlib.sha256(f'{seed}_{i}'.encode()).digest(), 'big') % p
            for i in range(n)]


def forward_Fp(n, c, d, psi_0, p):
    theta, psi = 0, psi_0
    for i in range(n):
        theta = (PHI * theta + psi * psi + c[i]) % p
        psi = (PHI * psi + theta * theta + d[i]) % p
    return theta


def run_p_n(p, n):
    print(f"\n{'='*60}")
    print(f"F_{p}, n = {n}")
    print('='*60)
    c = rc_over_Fp('mambo_bn254_c', n, p)
    d_vals = rc_over_Fp('mambo_bn254_d', n, p)
    psi_0 = 12345 % p
    target = forward_Fp(n, c, d_vals, psi_0, p)

    names = [f't{i}' for i in range(n+1)] + [f's{i}' for i in range(n+1)]
    ring_name = f'Rp{p}n{n}'
    singular.eval(f'ring {ring_name} = {p}, ({",".join(names)}), dp;')
    singular.eval('ideal I;')
    singular.eval('I[1] = t0;')
    singular.eval(f'I[2] = t{n} - {target};')
    k = 3
    for i in range(n):
        singular.eval(f'I[{k}] = t{i+1} - {PHI}*t{i} - s{i}^2 - {c[i]};')
        k += 1
        singular.eval(f'I[{k}] = s{i+1} - {PHI}*s{i} - t{i+1}^2 - {d_vals[i]};')
        k += 1

    singular.eval('ideal G = std(I);')
    hs = singular.eval('string(hilb(G, 2));').strip()
    coeffs = [int(p2.strip()) for p2 in hs.split(',') if p2.strip().lstrip('-').isdigit()]
    total = sum(coeffs)
    print(f"  hilb(G, 2) = {hs}")
    Z = PolynomialRing(ZZ, 'z').gen()
    pred = ((1 + Z)**(2*n - 1)).list()
    match = coeffs[:len(pred)] == pred and all(c2 == 0 for c2 in coeffs[len(pred):])
    print(f"  matches (1+z)^(2n-1): {match}")
    print(f"  dim R/I = {total}  (expected 2^(2n-1) = {2**(2*n-1)})")
    return match


if __name__ == '__main__':
    results = {}
    for p in TEST_PRIMES:
        for n in [2, 3, 4, 5]:
            m = run_p_n(p, n)
            results[(p, n)] = m
    print(f"\n{'='*60}")
    print("SUMMARY")
    print('='*60)
    all_pass = all(results.values())
    for (p, n), m in sorted(results.items()):
        print(f"  F_{p:>5}, n={n}: {'PASS' if m else 'FAIL'}")
    print(f"\n  all match (1+z)^(2n-1): {all_pass}")
