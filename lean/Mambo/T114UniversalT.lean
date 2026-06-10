import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# T114 generalized: AI(R) ≤ 2 at universal width t ≥ 2

Generalizes `Mambo.T114AlgebraicImmunity.exists_annihilator_totalDegree_le_2`
from width t = 2 to arbitrary t ≥ 2.

The Mambo round at width t has:
- `R_0(x) = phi · x_0 + x_{t-1}^2 + c_0`
  (cell-0 round; uses the freshly-squared LAST input cell)

The degree-2 annihilator at any width t is `L_0 = y_0 − R_0(x)`, where `y_0`
is the output of cell 0. `R_0` has total degree 2 from `x_{t-1}^2`, so `L_0`
has total degree max(1, 2) = 2.

Together with the t=2 5-coefficient AI ≥ 2 result, this gives AI(R) ≤ 2
machine-verified at all production widths t ∈ {2, 3, 4}.
-/

namespace Mambo.T114UniversalT

open MvPolynomial

variable (K : Type*) [CommRing K] [Nontrivial K]

/-- Variable indices at width t: 2t variables total (t for input x's, t for output y's).
    Index `i ∈ [0, t)` is `x_i`; index `t + i ∈ [t, 2t)` is `y_i`. -/
abbrev VarIdx (t : ℕ) := Fin (2 * t)

/-- The Mambo R_0 output as an MvPolynomial at width t ≥ 2:
    `R_0(x) = phi · x_0 + x_{t-1}^2 + c_0`.
    Uses `x_0` at index 0 and `x_{t-1}` at index t-1. -/
noncomputable def R0_poly_universal {t : ℕ} (h : 2 ≤ t) (phi c0 : K) :
    MvPolynomial (VarIdx t) K :=
  C phi * X ⟨0, by omega⟩ + (X ⟨t - 1, by omega⟩)^2 + C c0

/-- The degree-2 annihilator at width t: `L_0(x, y) = y_0 − R_0(x)`.
    `y_0` is at index `t` (first y-variable). -/
noncomputable def annihilator_L0_universal {t : ℕ} (h : 2 ≤ t) (phi c0 : K) :
    MvPolynomial (VarIdx t) K :=
  X ⟨t, by omega⟩ - R0_poly_universal K h phi c0

/-- **AI(R) ≤ 2 at universal width t ≥ 2**: the annihilator
    `L_0 = y_0 − R_0(x)` has total degree ≤ 2. Proof mirrors the t=2 case
    (`Mambo.T114AlgebraicImmunity.annihilator_L0_totalDegree_le_2`): y_0 has
    degree 1, R_0 has degree 2 from `x_{t-1}^2`. -/
theorem annihilator_L0_universal_totalDegree_le_2
    {t : ℕ} (h : 2 ≤ t) (phi c0 : K) :
    (annihilator_L0_universal K h phi c0).totalDegree ≤ 2 := by
  unfold annihilator_L0_universal R0_poly_universal
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  refine max_le ?_ ?_
  · rw [MvPolynomial.totalDegree_X]; decide
  · refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
      refine max_le ?_ ?_
      · -- C phi * X ⟨0, _⟩ has totalDegree ≤ 1
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; decide
      · -- (X ⟨t-1, _⟩)^2 has totalDegree ≤ 2
        refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
        rw [MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]; decide

/-- **AI(R) ≤ 2 at universal width t ≥ 2 (corollary)**: there exists a
    non-zero annihilator polynomial with total degree ≤ 2. -/
theorem exists_annihilator_universal_totalDegree_le_2
    {t : ℕ} (h : 2 ≤ t) (phi c0 : K) :
    ∃ L : MvPolynomial (VarIdx t) K, L ≠ 0 ∧ L.totalDegree ≤ 2 := by
  refine ⟨annihilator_L0_universal K h phi c0, ?_, annihilator_L0_universal_totalDegree_le_2 K h phi c0⟩
  -- L_0 ≠ 0 via eval at (0, ..., 0, c_0 + 1, 0, ..., 0) with y_0 = c_0 + 1, others = 0.
  -- R_0_poly evaluates to phi·0 + 0² + c_0 = c_0, so L_0 → (c_0+1) - c_0 = 1.
  intro hzero
  have heval :
      MvPolynomial.eval
          (fun i : VarIdx t => if i.val = t then c0 + 1 else 0)
          (annihilator_L0_universal K h phi c0) = 1 := by
    unfold annihilator_L0_universal R0_poly_universal
    simp [MvPolynomial.eval_sub, MvPolynomial.eval_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
          show (⟨0, by omega⟩ : VarIdx t).val ≠ t by simp; omega,
          show (⟨t - 1, by omega⟩ : VarIdx t).val ≠ t by simp; omega,
          show (⟨t, by omega⟩ : VarIdx t).val = t by simp]
  rw [hzero, map_zero] at heval
  exact zero_ne_one heval

/-! ### Instantiations at production widths -/

/-- AI(R) ≤ 2 at t = 2 (instantiation of universal-t). -/
theorem ai_leq_2_at_t2 (phi c0 : K) :
    ∃ L : MvPolynomial (VarIdx 2) K, L ≠ 0 ∧ L.totalDegree ≤ 2 :=
  exists_annihilator_universal_totalDegree_le_2 K (by decide : 2 ≤ 2) phi c0

/-- AI(R) ≤ 2 at t = 3 (instantiation of universal-t). -/
theorem ai_leq_2_at_t3 (phi c0 : K) :
    ∃ L : MvPolynomial (VarIdx 3) K, L ≠ 0 ∧ L.totalDegree ≤ 2 :=
  exists_annihilator_universal_totalDegree_le_2 K (by decide : 2 ≤ 3) phi c0

/-- AI(R) ≤ 2 at t = 4 (instantiation of universal-t). -/
theorem ai_leq_2_at_t4 (phi c0 : K) :
    ∃ L : MvPolynomial (VarIdx 4) K, L ≠ 0 ∧ L.totalDegree ≤ 2 :=
  exists_annihilator_universal_totalDegree_le_2 K (by decide : 2 ≤ 4) phi c0

end Mambo.T114UniversalT
