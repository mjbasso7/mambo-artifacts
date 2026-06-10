import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Mambo — Boolean Quotient Dimension (Lean proof)

Proves `Module.finrank K (K[X] / (X² − X)) = 2` for any field K.

The Boolean polynomial `X² − X = X · (X − 1)` is monic of degree 2.
Its quotient ring `AdjoinRoot (X² − X)` has the standard power basis
`{1, X̄}`, so its dimension as a K-module is 2.

This is the **dimension half** of Step B.1 Boolean reduction at one
variable: not only does the relation `X² ≡ X (mod I)` hold (proven in
`Mambo.MathlibBridge`), but the quotient is exactly 2-dimensional —
giving the `(1+z)` factor in the universal-Q Hilbert series for one
Boolean residual variable.
-/

namespace Mambo.MathlibBridge.Dim

open Polynomial AdjoinRoot

variable (K : Type*) [Field K]

/-- The Boolean defining polynomial `X² − X`, as a `Polynomial K`. -/
noncomputable def boolPoly : Polynomial K := X^2 - X

/-- The Boolean polynomial has natDegree 2. -/
theorem boolPoly_natDegree : (boolPoly K).natDegree = 2 := by
  unfold boolPoly
  compute_degree!

/-- The Boolean polynomial is monic. -/
theorem boolPoly_monic : (boolPoly K).Monic := by
  unfold boolPoly
  monicity!

/-- The Boolean polynomial is non-zero (degree 2 implies non-zero). -/
theorem boolPoly_ne_zero : boolPoly K ≠ 0 := fun h => by
  have h_deg : (boolPoly K).natDegree = 2 := boolPoly_natDegree K
  rw [h] at h_deg
  simp at h_deg

/-- **Dimension corollary (fully proven via mathlib):**
    The Boolean quotient `AdjoinRoot (X² − X)` is 2-dimensional over K.

    Proof: the polynomial is monic of natDegree 2, so by
    `AdjoinRoot.powerBasis'` we get a power basis whose dimension equals
    `natDegree = 2`. -/
theorem boolQuot_finrank :
    Module.finrank K (AdjoinRoot (boolPoly K)) = 2 := by
  have h_monic : (boolPoly K).Monic := boolPoly_monic K
  have h_deg : (boolPoly K).natDegree = 2 := boolPoly_natDegree K
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis' h_monic),
      AdjoinRoot.powerBasis'_dim, h_deg]

end Mambo.MathlibBridge.Dim
