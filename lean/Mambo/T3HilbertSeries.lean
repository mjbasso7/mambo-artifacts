import Mambo.BooleanReduction
import Mambo.B2Enumeration

/-!
# Mambo t=3 Hilbert Series — empirical companion

Lean 4 corollary file for the t=3 CICO closed-form Hilbert series
result (empirical anchor on 3 cells, n=3,4,5 over F_257).

**Empirical claim (3 cells n=3,4,5 over F_257; corrected per 5-cell
sage verification 2026-05-18):**

  HS_{R/I}(z) = (1 + z)^{3n − 2}  at width t = 3

  ⇒  dim_{F_p}(R/I) = 2^{3n − 2}  = 2 · 8^{n−1}  = D_I (Bezout)

  ⇒  d_reg = 3n − 1  (HS degree + 1)

**Note on prior version**: an earlier version of this file used
`booleanCount = 3·(n−1)` giving `dim = 2^{3(n−1)} = 8^{n−1}` and
`d_reg = 3n−2`. That formula was off by 1 in the exponent — measured
dims at n=2,3,4 are 16, 128, 1024 (matching `2^{3n−2}`), not 8, 64,
512. Corrected here per 5-cell sage verification.

This file captures the **dimension-level** corollaries: at t = 3 the
Boolean-factor count is `3n − 2`, and the corresponding HS factor
`(1 + z)^{3n − 2}` evaluates to `2^{3n − 2}` at z = 1.

The **semantic** content — that the Mambo coupled-quadratic ideal at
t = 3 has exactly `3n − 2` independent Boolean residuals — remains
an empirical claim pending the mathlib-backed semantic reduction
(analogous to the open B.4 derivation at t = 4).

The variable-count anchor `Fintype.card (VarIndex 3 n) = 3·(n + 1)`
is provided by `Mambo.B2Enumeration.card_VarIndex`.
-/

namespace Mambo.T3HilbertSeries

open Mambo.BooleanReduction Mambo.B2Enumeration Mambo.UniversalQ

/-- Boolean-residual count at t = 3, depth n: `3n − 2`. -/
def t3_booleanCount (n : Nat) : Nat := 3 * n - 2

/-- **t = 3 HS-factor dim** (corollary of `booleanFactor_dim`).

    At width t = 3 and depth n ≥ 1, the Boolean-factor `(1+z)^{3n−2}`
    evaluates to `2^{3n−2}` at z = 1, matching measured dims
    `(16, 128, 1024, 8192, …)` at `n = 2, 3, 4, 5, …`. -/
theorem t3_dim_from_boolean_factor (n : Nat) :
    Poly.evalAtOne (booleanFactor (t3_booleanCount n)) = 2 ^ (3 * n - 2) :=
  booleanFactor_dim _

/-- cell n = 2: HS = (1+z)^4, dim = 16 = 2^4. -/
theorem t3_anchor_n2 : Poly.evalAtOne (booleanFactor (t3_booleanCount 2)) = 16 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- cell n = 3: HS = (1+z)^7, dim = 128 = 2^7. -/
theorem t3_anchor_n3 : Poly.evalAtOne (booleanFactor (t3_booleanCount 3)) = 128 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- cell n = 4: HS = (1+z)^10, dim = 1024 = 2^10. -/
theorem t3_anchor_n4 : Poly.evalAtOne (booleanFactor (t3_booleanCount 4)) = 1024 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- cell n = 5: HS = (1+z)^13, dim = 8192 = 2^13. -/
theorem t3_anchor_n5 : Poly.evalAtOne (booleanFactor (t3_booleanCount 5)) = 8192 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- cell n = 6: HS = (1+z)^16, dim = 65536 = 2^16. -/
theorem t3_anchor_n6 : Poly.evalAtOne (booleanFactor (t3_booleanCount 6)) = 65536 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- cell n = 7: HS = (1+z)^19, dim = 524288 = 2^19. -/
theorem t3_anchor_n7 : Poly.evalAtOne (booleanFactor (t3_booleanCount 7)) = 524288 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- cell n = 8: HS = (1+z)^22, dim = 4194304 = 2^22. -/
theorem t3_anchor_n8 : Poly.evalAtOne (booleanFactor (t3_booleanCount 8)) = 4194304 := by
  unfold t3_booleanCount
  rw [booleanFactor_dim]

/-- d_reg at t = 3 (empirical, 5 cells, post-correction 2026-05-18): `3n − 1`. -/
def t3_d_reg (n : Nat) : Nat := 3 * n - 1

/-- Production t = 3 d_reg values (paper Table 7). -/
theorem t3_d_reg_prod_L1 : t3_d_reg 23 = 68 := by decide
theorem t3_d_reg_prod_L3 : t3_d_reg 33 = 98 := by decide
theorem t3_d_reg_prod_L5 : t3_d_reg 44 = 131 := by decide

/-- The t = 3 polynomial-ring variable count: `3 · (n + 1)`. -/
theorem t3_var_count (n : Nat) :
    Fintype.card (VarIndex 3 n) = 3 * (n + 1) := by
  rw [card_VarIndex 3 n]
  unfold numStateVars
  ring

/-- Sanity: t = 3, n = 3 → 12 typed variables in the polynomial ring. -/
example : Fintype.card (VarIndex 3 3) = 12 := by
  rw [t3_var_count 3]

/-- Sanity: t = 3, n = 5 → 18 typed variables. -/
example : Fintype.card (VarIndex 3 5) = 18 := by
  rw [t3_var_count 5]

/-- **d_reg formula at production widths** (sage-anchored at t = 2, 3, 4):

      d_reg(t, n) = t·n − (t − 1)(t − 2) / 2

    Specialises to:
      - t = 2: 2n − 0     = 2n         (paper Thm hilb_closed)
      - t = 3: 3n − 1                  (sage-verified n = 2, 3, 4 — this work)
      - t = 4: 4n − 3                  (sage-verified n = 3..8 — `T4HilbertSeries`)

    **SCOPE LIMIT (2026-05-19 retraction)**: an earlier framing of this
    formula as "universal across all t" was retracted after sage probes
    at t = 5 (n = 2, 3) and t = 6 (n = 2) measured d_reg = 5n − 3,
    6n − 4 — incompatible with the `(t − 1)(t − 2) / 2` extrapolation.
    The formula is **only valid at production widths t ∈ {2, 3, 4}**,
    consistent with the t = 4 / t ≥ 5 regime boundary noted in project
    memory `project_mambo_regime_boundary_t4_vs_t5`. The 3 instance
    theorems below remain correct at their respective t.

    The `(t − 1)(t − 2)/2` correction term captures the additional
    HS-degree contribution from the residual factor beyond the all-Boolean
    part at production widths only. -/
def production_d_reg (t n : Nat) : Nat := t * n - (t - 1) * (t - 2) / 2

/-- t = 2 instance recovers paper formula `2n`. -/
theorem production_d_reg_t2 (n : Nat) : production_d_reg 2 n = 2 * n := by
  unfold production_d_reg
  simp

/-- t = 3 instance recovers `3n − 1`. -/
theorem production_d_reg_t3 (n : Nat) (hn : 1 ≤ n) :
    production_d_reg 3 n = 3 * n - 1 := by
  unfold production_d_reg
  simp

/-- t = 4 instance recovers `4n − 3`. -/
theorem production_d_reg_t4 (n : Nat) (hn : 1 ≤ n) :
    production_d_reg 4 n = 4 * n - 3 := by
  unfold production_d_reg
  simp

end Mambo.T3HilbertSeries
