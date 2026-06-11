#!/usr/bin/env python3
"""Generate Mambo t=2 round constants under the canonical DERIVE-FRESH scheme.

Canonical scheme (matches the Python reference in independent_reference.py and
the specification in round_constants.md):
  For a permutation of N rounds:
    flat[j] = SHA-256("Mambo_round_constants" || BE32(j)) mod p   (0 -> 1)
    c_i = flat[i]      for i in 0..N-1
    d_i = flat[N + i]  for i in 0..N-1
  NO cycling. The d-series offset is N, so the constant set is N-DEPENDENT:
  the constants for N=82 are NOT an extension of the constants for N=65.

This module is the single source of truth for the derive-fresh t=2 constants;
the per-field tables are generated/checked against it.
"""
import hashlib

SEED_T2 = b"Mambo_round_constants"

FIELDS = {
    "BN254": 21888242871839275222246405745257275088548364400416034343698204186575808495617,
    "BLS12-381": 52435875175126190479447740508185965837690552500527637822603658699938581184513,
    "Goldilocks": 18446744069414584321,
    "BabyBear": 2013265921,
    "KoalaBear": 2130706433,
    "Stark": 3618502788666131213697322783095070105623107215331596699973092056135872020481,
    "Mersenne31": 2147483647,
}

# Deployed t=2 L1 cell (+25% margin over the analysis-minimum N=65).
N_DEPLOY = 82


def flat(j, p):
    h = hashlib.sha256(SEED_T2 + j.to_bytes(4, "big")).digest()
    v = int.from_bytes(h, "big") % p
    return v if v != 0 else 1


def derive_fresh(n, p):
    """Return (c_list, d_list), the canonical derive-fresh t=2 constants for N=n."""
    c = [flat(i, p) for i in range(n)]
    d = [flat(n + i, p) for i in range(n)]
    return c, d


if __name__ == "__main__":
    import sys
    field = sys.argv[1] if len(sys.argv) > 1 else "BN254"
    n = int(sys.argv[2]) if len(sys.argv) > 2 else N_DEPLOY
    p = FIELDS[field]
    c, d = derive_fresh(n, p)
    print(f"# field={field} N={n} (derive-fresh, d-offset={n})")
    for i in range(n):
        print(f"c[{i}]={c[i]}")
    for i in range(n):
        print(f"d[{i}]={d[i]}")
