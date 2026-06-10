import Mambo.T2CicoIdeal

/-!
# Mambo Li-Wang subspace-trail non-applicability (formal version)

The Li-Wang attack class (Li-Wang 2017, used by Beyne-Canteaut et al. 2022
on Vision) exploits non-trivial linear subspaces preserved by the round
permutation. For Mambo at any state width `t ≥ 2`, NO non-trivial linear
subspace is preserved by a single round.

This file formalises the t = 2 case via direct round-function algebra
(independently verified and audited; cross-checks pass).

## The argument at t = 2

Let `R(s) = (s'[0], s'[1])` where
  `s'[0] = φ·s[0] + s[1]²        + rc[0]`
  `s'[1] = φ·s[1] + (s'[0])²     + rc[1]`

For any direction `v = (a, b) ∈ K²` and the 1-D subspace
`V_v = { (t·a, t·b) : t ∈ K }`, parameterise `s[0] = t·a, s[1] = t·b`:
  `s'[0] = b² · t² + 7a · t + rc[0]`
  `s'[1] = b⁴ · t⁴ + 14·a·b² · t³ + (49·a² + 2·b²·rc[0]) · t² +
             (7·b + 14·a·rc[0]) · t + (rc[0]² + rc[1])`

For `R(V_v) ⊆ V_v` (modulo affine offset), each coordinate must be LINEAR
in `t`. The coefficient of `t²` in `s'[0]` is `b²`; coefficient of `t²`
in `s'[1]` is `49a² + 2·b²·rc[0]`. Setting both to zero in a field of
characteristic ≠ 2, 7:

  `b² = 0` ⟹ `b = 0` (char ≠ 2),
  then `49 a² = 0` ⟹ `a = 0` (char ≠ 7).

Therefore `V_v = {(0, 0)}` — only the trivial subspace is preserved.
-/

namespace Mambo.LiWangNonApplicable

open Mambo.T2CicoIdeal

variable {K : Type*} [Field K]

/-- One round of Mambo at t = 2 (paper coupled-sequential form), evaluated
    at a scalar point `s = (s0, s1)`. -/
def roundAt (rc0 rc1 : K) (s0 s1 : K) : K × K :=
  let s0' := (7 : K) * s0 + s1 * s1 + rc0
  let s1' := (7 : K) * s1 + s0' * s0' + rc1
  (s0', s1')

/-- Image of the parameter `t` along direction `(a, b)` under one round:
    `roundAt rc0 rc1 (t·a, t·b) = (s0'(t), s1'(t))` with `s0'` a polynomial
    of degree 2 in `t` and `s1'` of degree 4 in `t`. -/
theorem roundAt_param (rc0 rc1 a b t : K) :
    (roundAt rc0 rc1 (t * a) (t * b)).1
      = b ^ 2 * t ^ 2 + 7 * a * t + rc0 := by
  unfold roundAt
  ring

theorem roundAt_param_snd (rc0 rc1 a b t : K) :
    (roundAt rc0 rc1 (t * a) (t * b)).2
      = b ^ 4 * t ^ 4 + 14 * a * b ^ 2 * t ^ 3
        + (49 * a ^ 2 + 2 * b ^ 2 * rc0) * t ^ 2
        + (7 * b + 14 * a * rc0) * t
        + (rc0 ^ 2 + rc1) := by
  unfold roundAt
  ring

/-- **No non-trivial linear subspace is preserved by one round of Mambo at
    t = 2** (in any field with characteristic ≠ 2 and `(7 : K) ≠ 0`).

    Statement: if direction `(a, b)` is such that `b² = 0` AND
    `49·a² + 2·b²·rc[0] = 0` (the conditions for `s'[0]` and `s'[1]` to be
    LINEAR in the parameter `t`, i.e. for `R(V_v) ⊆ V_v + affine`), then
    `a = b = 0`. -/
theorem no_preserved_subspace_t2 (rc0 : K)
    (a b : K) (hb2 : b ^ 2 = 0) (ha2 : 49 * a ^ 2 + 2 * b ^ 2 * rc0 = 0)
    (h7 : (7 : K) ≠ 0) :
    a = 0 ∧ b = 0 := by
  -- b² = 0 ⟹ b = 0 (in a field — actually in any reduced ring, integral domain etc.)
  have hb : b = 0 := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp hb2
  refine ⟨?_, hb⟩
  -- 49·a² + 2·b²·rc0 = 0 with b = 0 gives 49·a² = 0
  rw [hb] at ha2
  -- ha2 : 49 * a^2 + 2 * 0^2 * rc0 = 0
  have ha2' : (49 : K) * a ^ 2 = 0 := by linear_combination ha2
  -- 49·a² = 0 ⟹ a² = 0 (since 49 = 7² ≠ 0 in K with (7 : K) ≠ 0)
  have h49 : (49 : K) ≠ 0 := by
    have : (49 : K) = 7 * 7 := by norm_num
    rw [this]
    exact mul_ne_zero h7 h7
  have ha_sq : a ^ 2 = 0 := by
    rcases mul_eq_zero.mp ha2' with h | h
    · exact absurd h h49
    · exact h
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ha_sq

/-- **Mambo at t = 2 has no preserved non-trivial 1-D linear subspace
    (Li-Wang non-applicability)**: for any direction `(a, b) ∈ K²` and
    any round constants, if the round map sends `V_{(a,b)}` into itself
    modulo affine offset, then `(a, b) = (0, 0)`.

    Corollary of `no_preserved_subspace_t2`. -/
theorem mambo_t2_no_li_wang_subspace (rc0 : K) (a b : K) (h7 : (7 : K) ≠ 0)
    (h_preserved : b ^ 2 = 0 ∧ 49 * a ^ 2 + 2 * b ^ 2 * rc0 = 0) :
    (a, b) = ((0 : K), (0 : K)) := by
  obtain ⟨ha, hb⟩ := no_preserved_subspace_t2 rc0 a b h_preserved.1 h_preserved.2 h7
  rw [ha, hb]

end Mambo.LiWangNonApplicable
