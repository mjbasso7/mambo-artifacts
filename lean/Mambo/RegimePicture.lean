import Mambo.UniversalQ

/-!
# Regime Picture for Mambo Hilbert Series (post-retraction structure)

After the 2026-05-15 retraction of "Q universal across t ≥ 4", the
Mambo Hilbert series picture splits into **three regimes** (the
classification, confirmed by 2 cells in the new regime):

| Regime          | HS formula                          | Status                  |
|-----------------|-------------------------------------|-------------------------|
| t = 2           | (1+z)^(2n − 1)                      | paper theorem (proven)  |
| t = 3           | (1+z)^k pure Boolean (k tbd)        | empirical               |
| t = 4, n ≥ 3    | (1+z)^(4n − 9) · Q_4(z)             | 6 cells empirical       |
| t ≥ 6, n = 4    | (1+z)^(tn − 14) · Q_{n=4}(z)        | 2 cells (t=6, t=8)      |
| t = 5, n ≥ 4    | UNKNOWN — pending cell           | open                    |

Two distinct residue polynomials so far:
- `Q_4 = z⁵ + 11z⁴ + 25z³ + 19z² + 7z + 1` (degree 5, irreducible over F_p)
- `Q_{n=4} = z⁷ + 77z⁶ + 326z⁵ + 347z⁴ + 196z³ + 64z² + 12z + 1`
  (degree 7, factors as (linear)³·(quadratic)² over F_p)

This file captures the regime picture as defined formulas, with each
regime's evaluation at z=1 (the dim corollary) machine-checked at
concrete (t, n) cells.
-/

namespace Mambo.RegimePicture

open Mambo.UniversalQ

/-- The n-indexed residue observed at t = 6, n = 4 and t = 8, n = 4
    (BIT-IDENTICAL across these two cells, supporting the n-indexed
    hypothesis at t ≥ 6). -/
def Q_n4 : Poly := [1, 12, 64, 196, 347, 326, 77, 1]

/-- Q_{n=4}(1) = 1024 = 2^10. -/
theorem evalAtOne_Q_n4 : Poly.evalAtOne Q_n4 = 1024 := by decide

theorem Q_n4_sum_is_2_pow_10 : Poly.evalAtOne Q_n4 = 2 ^ 10 := by decide

/-- **Predicted HS at the t ≥ 6, n = 4 regime:** `(1+z)^(tn − 14) · Q_{n=4}(z)`.
    Defined here so we can check the dim corollary at t = 6 and t = 8. -/
def predicted_HS_n4_regime (t : Nat) : Poly :=
  Poly.mul (onePlusZPow (t * 4 - 14)) Q_n4

/-- **t = 6, n = 4 anchor:** dim = 2^20 = 1,048,576. -/
example : Poly.evalAtOne (predicted_HS_n4_regime 6) = 1048576 := by decide

/-- **t = 8, n = 4 anchor:** dim = 2^28 = 268,435,456. -/
example : Poly.evalAtOne (predicted_HS_n4_regime 8) = 268435456 := by decide

/-- **General formula for t ≥ 6, n = 4 regime:** dim = 2^(t·4 − 4) = 2^(tn − 4). -/
theorem evalAtOne_n4_regime (t : Nat) (ht : 6 ≤ t) :
    Poly.evalAtOne (predicted_HS_n4_regime t) = 2 ^ (t * 4 - 4) := by
  show Poly.evalAtOne (Poly.mul (onePlusZPow (t * 4 - 14)) Q_n4) = 2 ^ (t * 4 - 4)
  rw [Poly.evalAtOne_mul, evalAtOne_onePlusZPow, Q_n4_sum_is_2_pow_10,
      ← Nat.pow_add]
  congr 1
  -- Need: (t*4 - 14) + 10 = t*4 - 4, given t ≥ 6
  -- Since t ≥ 6, t*4 ≥ 24, so t*4 - 14 ≥ 10 and t*4 - 4 ≥ 20
  have : 6 * 4 ≤ t * 4 := Nat.mul_le_mul_right _ ht
  omega

/-- The dim deficit at t ≥ 6 vs the old (failed) t=4-style prediction.

    Old (failed) formula at t=6 n=4: 2^(tn − 3) = 2^21.
    New formula:                     2^(tn − 4) = 2^20.

    Deficit: factor of 2. The Mambo algebra at t ≥ 6, n = 4 has **one fewer
    free direction** than the t=4 algebra would suggest. -/
theorem n4_regime_dim_deficit (t : Nat) (ht : 6 ≤ t) :
    Poly.evalAtOne (predicted_HS_n4_regime t) * 2 = 2 ^ (t * 4 - 3) := by
  rw [evalAtOne_n4_regime t ht]
  rw [show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.pow_add]
  congr 1
  have : 6 * 4 ≤ t * 4 := Nat.mul_le_mul_right _ ht
  omega

end Mambo.RegimePicture
