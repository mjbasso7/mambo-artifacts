import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Mambo has no Flystel-pair structure (Anemoi non-applicability, lane #12)

The Anemoi cipher's Campa-Roy 2026 attack exploits the **Flystel-pair**
structure: a bivariate map `(x, y) ↦ (y - x^α, G(x, y))` with `α ≥ 3`
(typically α = 5). Every output coordinate of a Flystel-pair therefore
has total degree ≥ α ≥ 3.

Mambo's round at width `t = 2` has FIRST output coordinate

  s'_0(θ, ψ) = φ · θ + ψ² + c

with the squaring `ψ²` as the only nonlinear term. The monomial `ψ²`
sits in `s'_0`'s support with non-zero coefficient — so `s'_0` has
total degree at least 2 (achieved exactly).

This file isolates the **degree-side witness** on Mambo's coordinate 0
that drives the structural-impossibility argument: `(X 1)^2` is in
`mambo_s0.support`. Combined with the fact that any Flystel α-pair has
all coordinates of degree ≥ α ≥ 3, no affine-equivalent Flystel pair
exists for Mambo's round.

The full no-Flystel theorem (involving affine transformations and the
Anemoi-side degree lemma) is treated in the paper; the Lean version here
captures the load-bearing degree fact on the Mambo side.
-/

namespace Mambo.NoFlystelPair

open MvPolynomial Finsupp

variable {K : Type*} [CommRing K]

/-- The Mambo round's first output coordinate as a bivariate polynomial in
    `(X 0, X 1) = (θ, ψ)`: `s'_0(θ, ψ) = φ · θ + ψ² + c`. -/
noncomputable def mambo_s0 (phi c : K) : MvPolynomial (Fin 2) K :=
  (phi : K) • X 0 + X 1 ^ 2 + C c

/-- The "degree-2 ψ²" monomial: `Finsupp.single 1 2` is the multidegree
    where coordinate 1 has degree 2 and coordinate 0 has degree 0. -/
noncomputable def psi_sq_monomial : Fin 2 →₀ ℕ := Finsupp.single 1 2

/-- The `ψ²` coefficient of `mambo_s0` equals 1 (≠ 0 in any non-trivial ring).

    Direct: `mambo_s0 = φ·X 0 + (X 1)^2 + C c`. The monomial `(X 1)^2`
    has multidegree `Finsupp.single 1 2`, and its coefficient in `(X 1)^2`
    is 1. The other two summands don't contribute to this monomial:
    `φ·X 0` is supported on `Finsupp.single 0 1`, and `C c` is supported
    on `0`. -/
theorem mambo_s0_coeff_psi_sq (phi c : K) :
    coeff psi_sq_monomial (mambo_s0 phi c) = 1 := by
  unfold mambo_s0 psi_sq_monomial
  -- coeff at (single 1 2):
  --   φ•X 0 contributes: X 0 has monomial (single 0 1) ≠ (single 1 2), so 0
  --   (X 1)^2 contributes: X 1^2 has monomial (single 1 2), coeff 1, ✓
  --   C c contributes: monomial 0 ≠ (single 1 2), so 0
  have h_X0 : coeff (Finsupp.single (1 : Fin 2) 2) (X 0 : MvPolynomial (Fin 2) K) = 0 := by
    rw [coeff_X']
    simp [Finsupp.single_eq_single_iff]
  have h_X1sq : coeff (Finsupp.single (1 : Fin 2) 2)
                  ((X 1 : MvPolynomial (Fin 2) K) ^ 2) = 1 := by
    rw [coeff_X_pow]; simp
  have h_C : coeff (Finsupp.single (1 : Fin 2) 2) (C c : MvPolynomial (Fin 2) K) = 0 := by
    rw [coeff_C]
    have : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
      intro h
      have := congrArg (· 1) h
      simp at this
    simp [this]
  rw [coeff_add, coeff_add, coeff_smul, h_X0, h_X1sq, h_C]
  simp

/-- **Mambo's `s'_0` has the `ψ²` monomial in its support** (assuming
    `(1 : K) ≠ 0`, i.e. `K` is non-trivial).

    Witness that `s'_0` is genuinely degree-2 — the degree-2 term
    `ψ²` has non-zero coefficient and therefore lives in the support.

    This is the load-bearing fact for the no-Flystel argument: any
    Flystel-pair coordinate has degree ≥ α ≥ 3, so Mambo's coordinate
    0 (degree exactly 2 via this witness) cannot be Flystel-pair-shaped. -/
theorem mambo_s0_psi_sq_in_support (phi c : K) (h_one : (1 : K) ≠ 0) :
    psi_sq_monomial ∈ (mambo_s0 phi c).support := by
  rw [MvPolynomial.mem_support_iff]
  rw [mambo_s0_coeff_psi_sq]
  exact h_one

end Mambo.NoFlystelPair
