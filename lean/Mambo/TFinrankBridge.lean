import Mambo.TGeneralDegreeTracking
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Bridge from natDegree to Module.finrank (Universal-t)

Connects the univariate degree formula from `TGeneralDegreeTracking`
(`T113_D_I_universal_stub`: `natDegree(x_0(n) - C τ) = 2^(t(n-1))`) to
the K-module rank of the quotient ring (= paper's `D_I` as
field-saturation degree).

Goal:
```
finrank K (AdjoinRoot (state K phi_K (t-1) c_seq n 0 - C tau)) = 2^(t*(n-1))
```

This uses `Polynomial.PowerBasis.finrank` once we establish:
1. The polynomial `state n 0 - C τ` is nonzero (degree ≥ 1)
2. It can be normalized to a monic polynomial (in a field K, divide by
   leading coefficient — preserves the ideal generated)
3. `AdjoinRoot` of the monic version has the right power basis

The t = 2 specialization is proven in `Mambo.T2GeneralN.t2_general_dim`;
this file extends the bridge to general t ≥ 2 using
`T113_D_I_universal_stub`.

NOTE: requires `K : Field` (stronger than CommRing in TGeneralDegreeTracking)
so that the eliminating polynomial can be normalized to monic.
-/

namespace Mambo.TFinrankBridge

open Polynomial Mambo.TGeneralDegreeTracking

variable (K : Type*) [Field K]

/-- Pending. Bridge theorem: the K-module rank of the CICO elimination
    quotient ring equals paper's D_I.

    For t ≥ 2, phi_K ≠ 0, c_seq, τ, n ≥ 1:
    ```
    finrank K (AdjoinRoot (state K phi_K (t-1) c_seq n 0 - C τ)) = 2^(t*(n-1))
    ```

    Proof outline (template from `Mambo.T2GeneralN.t2_general_dim`):
    1. Show `state n 0 - C τ` is nonzero (from D_I formula: natDegree
       = 2^(t(n-1)) ≥ 1 when n ≥ 1).
    2. Normalize to monic via `Polynomial.mul_leadingCoeff_inv` etc.
    3. Apply `PowerBasis.finrank ∘ AdjoinRoot.powerBasis'`.
    4. Use `T113_D_I_universal_stub` to identify natDegree = 2^(t(n-1)).

    Status: stub, target for next session. -/
theorem mambo_universal_D_I_finrank
    (phi_K : K) (h7 : phi_K ≠ 0)
    (t : ℕ) (ht2 : 2 ≤ t) (c_seq : ℕ → ℕ → K) (tau : K)
    (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank K
      (AdjoinRoot (state K phi_K (t - 1) c_seq n 0 - Polynomial.C tau))
      = 2 ^ (t * (n - 1)) := by
  -- Step 1: derive natDegree from universal-t theorem
  have hdeg : (state K phi_K (t - 1) c_seq n 0 - Polynomial.C tau).natDegree
      = 2 ^ (t * (n - 1)) :=
    T113_D_I_universal_stub K phi_K h7 t ht2 c_seq tau n hn
  -- Step 2: polynomial is nonzero (has positive degree)
  have hne : (state K phi_K (t - 1) c_seq n 0 - Polynomial.C tau) ≠ 0 := by
    intro hzero
    have hdz : (state K phi_K (t - 1) c_seq n 0 - Polynomial.C tau).natDegree = 0 := by
      rw [hzero]; exact Polynomial.natDegree_zero
    rw [hdeg] at hdz
    have hpos : 0 < 2 ^ (t * (n - 1)) := pow_pos (by norm_num : (0:Nat) < 2) _
    omega
  -- Step 3: apply AdjoinRoot.powerBasis (works for non-monic over a field)
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne)]
  rw [AdjoinRoot.powerBasis_dim]
  exact hdeg

-- Axiom check
#print axioms mambo_universal_D_I_finrank

end Mambo.TFinrankBridge
