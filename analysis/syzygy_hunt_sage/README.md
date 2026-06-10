# Syzygy-hunt Sage scripts (reproducibility layer for §5.3)

Five SageMath scripts that reproduce the Hilbert-series / d_reg /
solution-count / graded-Betti / characteristic-independence
measurements cited in §5.3 Prop 5.3 and the closed-form
corollary added during the 2026-04-21 audit pass.

## Contents

| Script | What it measures | Reproduces |
|---|---|---|
| `mambo_d_reg_paper.sage` | `hilb(G, 2)` on the paper's determined ideal at n ∈ {2..8} | Paper Table `tab:groebner` — `d_reg = 2n` for each n |
| `mambo_hs_large_n.sage` | Same, extended to n ∈ {6..10} | Closed-form observation: HS numerator = `(1+z)^(2n-1)` at every n |
| `mambo_syzygy_paper.sage` | First syzygy module via Singular `syz()`, bucketed by weighted degree, compared to Koszul pair count | First syzygy = Koszul exactly; non-genericity is not at first level |
| `mambo_graded_hom.sage` | Minimal free resolution of the HOMOGENIZED ideal, full graded Betti table | Homogenized ideal is semi-regular (non-genericity erased by adding h variable) |
| `mambo_chareq.sage` | Same measurement at `F_p` for `p ∈ {101, 257, 1009, 7919}` | Characteristic-independence of HS (paper's claim at end of Prop 5.3) |

## Dependencies

- SageMath 10.x (tested on 10.8) with bundled Singular. No external
  Singular install needed — Sage drives Singular through
  `sage.interfaces.singular`.
- Python 3.13 (Sage's bundled) — `hashlib`, `time` only (stdlib).

## Run

```
sage mambo_d_reg_paper.sage
sage mambo_hs_large_n.sage
sage mambo_syzygy_paper.sage
sage mambo_graded_hom.sage
sage mambo_chareq.sage
```

Each script prints its measurement to stdout. Wall-clock on
DO-Premium-AMD 8 vCPU: each finishes in under a minute; the char-eq
test is the longest at ~30s.

## Connection to the author-shipped computation

The original computation for Prop 5.3 lives in
`../mambo_hilbert_series.py` (plain Python driving a command-line
Singular). This new set reproduces the same ideal formulation and
matches its output at every overlapping n, then extends with:

1. Closed-form Hilbert numerator observation `(1+z)^(2n-1)` (not
   stated in the original author script or paper text).
2. Solution-count corollary `dim_Q(R/I) = 2^(2n-1)` (via sum of
   binomial coefficients).
3. Graded-Betti analysis showing first syzygy is exactly Koszul (rules
   out low-order non-generic syzygy as the driver of the d_reg gap).
4. Homogenization diagnostic showing the non-genericity is purely
   affine.
5. Small-prime empirical confirmation of characteristic independence.

These are measurements, not proofs. The MQ-reduction described in
the 2026-04-21 syzygy-hunt writeup is a **heuristic observation
about the half-density Bezout gap**, not a formal cryptographic
reduction — a full reduction is open work and not claimed by these
scripts.

## Audit contract

Every numerical claim in the 2026-04-21 syzygy-hunt writeup is
backed by one of the five scripts above. If a number cannot be
reproduced from these scripts on the same round-constant seed,
please flag it as a correctness issue.
