# Mambo Round Constants — Deterministic Derivation Specification

## Overview

All Mambo round constants are derived deterministically from SHA-256. Anyone can regenerate them from the seed string.

## General Rule

For state width `t` and field `F_p`, generate `t * max_rounds` constants:

```
seed = "Mambo_round_constants"         (for t=2)
seed = "Mambo_t3_round_constants"      (for t=3)
seed = "Mambo_t4_round_constants"      (for t=4)

For j in [0, t * max_rounds):
    h = SHA-256(seed || BE32(j))       // BE32 = big-endian 32-bit counter
    val = int(h) mod p                 // reduce modulo field prime
    if val == 0: val = 1               // avoid zero (zero would cancel terms)
    constants[j] = val
```

## Indexing

For t=2 (canonical DERIVE-FRESH scheme — matches the Python reference): a
permutation of N rounds derives 2N fresh constants:
- `c[i] = h_i`        for i in [0, N)
- `d[i] = h_{N + i}`  for i in [0, N)

No cycling. The d-series offset equals N, so the constant SET is N-DEPENDENT:
the constants for N=82 are NOT an extension of the N=65 set (the d block shifts).
A hardcoded RC table is therefore specific to one N; the deployed L1 cell is
N=82. The earlier scheme cycled a fixed 65-entry table (d-offset pinned to 65)
mod 65 — it coincides with derive-fresh only at exactly N=65.

For t >= 3:
- `constants[r*t + i]` = constant for element i at round r
- 0 <= i < t, 0 <= r < max_rounds

## Field-Specific Outputs

Each field generates its own set of constants using the same seed string and formula, differing only in the modulus `p`:

| Field        | p (decimal)                                                                                         | t=2 first c_0        |
|--------------|----------------------------------------------------------------------------------------------------|---------------------|
| BN254        | 21888242871839275222246405745257275088548364400416034343698204186575808495617                      | 11827785480768218948832965540304435174091293194226561066705381355847415829987 |
| Goldilocks   | 18446744069414584321                                                                               | 11932328547287637518 |
| BabyBear     | 2013265921                                                                                         | 1232491868          |
| Mersenne-61  | 2305843009213693951                                                                                | 2037741323232763514 |
| Stark field  | 3618502788666131213697322783095070105623107215331596699973092056135872020481                       | (computed from seed) |

## Verification

To reproduce any constant:

```python
import hashlib
def gen_constant(t, r, i, p, seed):
    j = r * t + i if t > 2 else None   # for t=2, use flat layout
    # For t=2 historical layout: flat index runs 0..129 for 65 c values then 65 d values
    # For t>=3:
    h = hashlib.sha256(seed.encode() + j.to_bytes(4, 'big')).digest()
    v = int.from_bytes(h, 'big') % p
    return v if v != 0 else 1
```

## Test Vectors

First constant (j=0) for t=2 seed on each field:

- BN254: `c_0 = 11827785480768218948832965540304435174091293194226561066705381355847415829987`
- BabyBear: `c_0 = 1232491868`
- Goldilocks: `c_0 = 11932328547287637518`

First constant (j=0) for t=3 seed:
- BN254: `15887682186238891969935225783036151264124640837591497272492565195223657078625`

First constant (j=0) for t=4 seed:
- BN254: (verified via Python reference)

## Why This Design

1. **Deterministic:** Any third party can regenerate from the seed.
2. **Nothing up my sleeve:** The seed is a literal human-readable string. No hidden parameters.
3. **Pseudorandom:** SHA-256 output is indistinguishable from uniform (in practice).
4. **Zero-avoidance:** Avoiding zero prevents the round constant from becoming a no-op in any round.
5. **Field-agnostic:** Same derivation works for any prime field by changing the modulus.
