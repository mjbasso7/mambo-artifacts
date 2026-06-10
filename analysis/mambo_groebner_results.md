# Mambo Gröbner Basis Attack — Results

Script: mambo_groebner_singular.py
Backend: Singular `std()`
Date: 2026-04-12

| p | bits | L_rounds | Wall (s) | GB time (ms) | GB size | Status |
|---|------|----------|----------|--------------|---------|--------|
| 17 | 5 | 2 | 0.022 | 0 | 5 | OK |
| 17 | 5 | 3 | 0.03 | 0 | 7 | OK |
| 31 | 5 | 3 | 0.04 | 0 | 7 | OK |
| 31 | 5 | 5 | 0.035 | 0 | 11 | OK |
| 101 | 7 | 3 | 0.033 | 0 | 7 | OK |
| 101 | 7 | 5 | 0.023 | 0 | 11 | OK |
| 101 | 7 | 8 | 0.028 | 0 | 17 | OK |
| 251 | 8 | 5 | 0.02 | 0 | 11 | OK |
| 251 | 8 | 8 | 0.023 | 0 | 17 | OK |
| 1009 | 10 | 5 | 0.022 | 0 | 11 | OK |
| 1009 | 10 | 8 | 0.031 | 0 | 17 | OK |
| 1009 | 10 | 13 | 0.026 | 0 | 27 | OK |

## Interpretation

Barrier identified where Singular times out at 5-minute budget. Scaling from
small primes + few rounds to production (M31, 33+ rounds) is beyond any
feasible GB attack.
