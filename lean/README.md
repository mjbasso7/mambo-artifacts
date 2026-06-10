# Mambo — Lean 4 Formalization

Lean 4 formalization of the Mambo cryptographic construction. Four modules:

- `Mambo/RoundFunction.lean` — t=4 coupled-quadratic permutation round (matches
  the production t = 4 round function)
- `Mambo/UniversalQ.lean` — Hilbert-series stabilization theorem (t = 4
  universal-in-n) statement plus a fully-proven corollary
  `dim_K(R/I) = 2^(4·n − 3)`
- `Mambo/MacaulayBound.lean` — Macaulay (Bardet-Faugère-Salvy) Gröbner-basis
  cost estimate; production-parameter security bounds discharged via
  `native_decide`
- `Mambo/BooleanReduction.lean` — Step B.1 Boolean-reduction lemma; dimension
  contribution fully proven

## Reproduce

```
cd lean
lake build     # ~5 s, no mathlib required
```

The lakefile contains a commented `require mathlib` line. Uncommenting it
fetches mathlib v4.13.0 + transitive deps and enables the future
`Polynomial`/`Ideal` lift work.

## What's proved vs. open

**Fully proved (zero `sorry`):**
- `Mambo.RoundFunction` — round function definition + length-preservation
- `Mambo.UniversalQ.evalAtOne_predicted` — predicted HS numerator evaluates
  to `2^(t·n − 3)` at `z = 1` (dimension corollary at t = 4)
- `Mambo.MacaulayBound.security_t4_L1_geq_128bits` — `binom(146, 69) ≥ 2^128`
  via kernel `decide` (production t=4, exactly-proven d_reg). NOTE: (4, 18)
  belongs to the superseded model-dependent grid (see conservative grid below).
- **Conservative-grid Macaulay floors (2026-06-10)** — the nine recommended
  cells under the new conservative sizing rule, each kernel-checked via
  `decide` with an empty axiom set
  (`Mambo.MacaulayBound.security_tX_LY_geq_ZZZbits_conservative`):
  - L1/128: `(2, 65)` — `binom(263, 130)`; `(3, 44)` — `binom(267, 131)`;
    `(4, 34)` — `binom(274, 133)`
  - L3/192: `(2, 97)` — `binom(391, 194)`; `(3, 66)` — `binom(399, 197)`;
    `(4, 50)` — `binom(402, 197)`
  - L5/256: `(2, 129)` — `binom(519, 258)`; `(3, 87)` — `binom(525, 260)`;
    `(4, 66)` — `binom(530, 261)`

  Scope caveats (same as all Macaulay floors in `MacaulayBound.lean`): these
  are Macaulay-model arithmetic — the Gröbner/Macaulay-step lower bound
  `binom(numVars + d_reg, d_reg) ≥ 2^λ` only, not the FGLM conversion step
  (a modeling assumption, paper §5.4). The d_reg input is theorem-backed at
  t = 2 via the proven closed form `2n`; at t = 3, 4 the formulas `3n − 1`
  and `4n − 3` are the paper's exactly-measured values at production widths.
  The earlier grid's floors ((2,33)/(2,49)/(2,65), (3,23)/(3,33)/(3,44),
  (4,18)/(4,27)/(4,36)) remain in the file, marked as the superseded
  model-dependent grid.

**Conditional / research (not a paper claim):**
- `Mambo.MacaulayBound.security_t16_L1_geq_256bits_CONDITIONAL` —
  `binom(277, 116) ≥ 2^256` via kernel `decide`. The inequality is kernel-true,
  but t=16 is NOT a paper production width (paper widths are t ∈ {2,3,4}) and
  d_reg(16,9)=116 uses the UNVALIDATED t≥5 fallback. The 256-bit conclusion
  holds only if the true offset at t=16 is ≤ 36 (see d_reg WARNING in
  MacaulayBound.lean). Do not treat as a robust security guarantee.
- `Mambo.BooleanReduction.mambo_boolean_dim` — Boolean residuals contribute
  `2^(t·n − 9)` to total dimension
- 4 in-n empirical anchors at t = 4 (n = 3, 4, 5, 6) + 4 cross-width n = 3
  cells (t = 5, 6, 7, 8) verified by Lean kernel `decide`

**Open (require mathlib for `Polynomial`/`Ideal` types):**
- `Mambo.UniversalQ.universal_Q_HS_stabilization` — equality of predicted
  vs. actual HS of the Mambo ideal at t = 4
- `Mambo.BooleanReduction.semantic_boolean_reduction` — the semantic
  `x_i² = x_i` claim in `R/I`

## Scope correction (2026-05-15)

An earlier conjecture that the universal-Q theorem extends to all `t ≥ 4`
was **retracted** after the `t = 6, n = 4` measurement: HS sum = 2^20
(not predicted 2^21), peeled residue is degree-7 (not degree-5 Q). The
theorem is now scoped to **t = 4 universal-in-n** only. Cells at t = 5..8
with n = 3 still match the predicted formula numerically but are not
universality evidence (small-n degenerate regime).

This matters for production: paper Table 7's deployment width is `t = 4`,
so the practically relevant scope is preserved. Wider-`t` parameters are
empirical-by-width, not theorem.

## Status

~360 LOC across 5 files. Toolchain: Lean 4 v4.13.0. Self-contained
(builds without mathlib in ~5 s). Empirical anchors machine-checked at
Lean kernel level — the t = 4 dimension claim is mechanically verified at
concrete `(4, n)` cells, not just numerically agreed across machines.
