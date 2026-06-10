import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree

/-!
# Mambo t = 3 Universal D_I Degree Tracking (paper convention)

Implementation of the T113 universal D_I proof outline at t = 3.

Setup (paper convention, `mambo_tosc_2026.tex` lines 1870-1883):
- rate = 1, capacity = t - 1 = 2
- Boundaries: `x_1(0) = 0`, `x_2(0) = 0`, `x_0(n) = τ`
- Free variable: `x_0(0)` (the rate-in CICO unknown)

Theorem (T113 at t=3):
For r ≥ 1 and i ∈ {0, 1, 2}, the per-cell polynomial `x_i(r)` viewed
as a polynomial in the single free variable `x_0(0)` has degree
`2^(3(r-1) + i)`.

D_I corollary: `deg(x_0(n) − τ) = 2^(3(n-1))`, matching the paper's
`D_I = 2^(t(n-1))` formula at t = 3.

Strategy:
1. Define three mutually-recursive univariate polynomial iterators
   `x0_p`, `x1_p`, `x2_p` over `Polynomial K` with `X = x_0(0)`.
2. Track `natDegree` of each iterator by joint induction on r.
3. Track `Monic` property as the iterators are constructed by
   squaring monic polynomials and adding lower-degree corrections.

This file targets the t = 3 case specifically; general-t parametric
extension is future work.
-/

namespace Mambo.T3DegreeTracking

open Polynomial

variable (K : Type*) [CommRing K]

/-- Mambo multiplier `φ = 7`. -/
def phi : Nat := 7

/-! ### Univariate iterators at paper convention

Convention:
- `X` denotes the free variable `x_0(0)`.
- `x1(0) = 0`, `x2(0) = 0` (paper cap-in boundaries).
- Iterator chain at round `r → r+1`:
    x_0(r+1) = φ·x_0(r) + (x_2(r))² + c_{0,r}
    x_1(r+1) = φ·x_1(r) + (x_0(r+1))² + c_{1,r}
    x_2(r+1) = φ·x_2(r) + (x_1(r+1))² + c_{2,r}
-/

mutual

/-- Iterator for `x_0(r)` (rate cell). Base case: `x_0(0) = X`. -/
noncomputable def x0_p (c0 c1 c2 : Nat → K) : Nat → Polynomial K
  | 0     => Polynomial.X
  | r + 1 =>
      (Polynomial.C (phi : K)) * x0_p c0 c1 c2 r
        + (x2_p c0 c1 c2 r) ^ 2
        + Polynomial.C (c0 r)

/-- Iterator for `x_1(r)` (cap cell 1). Base case: `x_1(0) = 0` (paper cap-in). -/
noncomputable def x1_p (c0 c1 c2 : Nat → K) : Nat → Polynomial K
  | 0     => 0
  | r + 1 =>
      (Polynomial.C (phi : K)) * x1_p c0 c1 c2 r
        + (x0_p c0 c1 c2 (r + 1)) ^ 2
        + Polynomial.C (c1 r)

/-- Iterator for `x_2(r)` (cap cell 2). Base case: `x_2(0) = 0` (paper cap-in). -/
noncomputable def x2_p (c0 c1 c2 : Nat → K) : Nat → Polynomial K
  | 0     => 0
  | r + 1 =>
      (Polynomial.C (phi : K)) * x2_p c0 c1 c2 r
        + (x1_p c0 c1 c2 (r + 1)) ^ 2
        + Polynomial.C (c2 r)

end

/-! ### Base-case lemmas (r = 0) -/

theorem x0_p_zero (c0 c1 c2 : Nat → K) :
    x0_p K c0 c1 c2 0 = Polynomial.X := by
  simp only [x0_p]

theorem x1_p_zero (c0 c1 c2 : Nat → K) :
    x1_p K c0 c1 c2 0 = 0 := by
  simp only [x1_p]

theorem x2_p_zero (c0 c1 c2 : Nat → K) :
    x2_p K c0 c1 c2 0 = 0 := by
  simp only [x2_p]

/-! ### Successor unfoldings -/

theorem x0_p_succ (c0 c1 c2 : Nat → K) (r : Nat) :
    x0_p K c0 c1 c2 (r + 1)
      = Polynomial.C (phi : K) * x0_p K c0 c1 c2 r + (x2_p K c0 c1 c2 r) ^ 2
        + Polynomial.C (c0 r) := by
  simp only [x0_p]

theorem x1_p_succ (c0 c1 c2 : Nat → K) (r : Nat) :
    x1_p K c0 c1 c2 (r + 1)
      = Polynomial.C (phi : K) * x1_p K c0 c1 c2 r + (x0_p K c0 c1 c2 (r + 1)) ^ 2
        + Polynomial.C (c1 r) := by
  simp only [x1_p]

theorem x2_p_succ (c0 c1 c2 : Nat → K) (r : Nat) :
    x2_p K c0 c1 c2 (r + 1)
      = Polynomial.C (phi : K) * x2_p K c0 c1 c2 r + (x1_p K c0 c1 c2 (r + 1)) ^ 2
        + Polynomial.C (c2 r) := by
  simp only [x2_p]

/-! ### Concrete cells at r = 1

Per T113 formula `deg(x_i(r)) = 2^(3(r-1) + i)` at r = 1:
- `x_0(1)` has degree `2^0 = 1` (linear in X)
- `x_1(1)` has degree `2^1 = 2`
- `x_2(1)` has degree `2^2 = 4`

Explicit expansions:
- `x_0(1) = φ·X + 0² + c_{0,0} = φ·X + c_{0,0}`            (degree 1)
- `x_1(1) = φ·0 + (φ·X + c_{0,0})² + c_{1,0}`              (degree 2)
- `x_2(1) = φ·0 + (x_1(1))² + c_{2,0}`                     (degree 4)
-/

theorem x0_p_one_expand (c0 c1 c2 : Nat → K) :
    x0_p K c0 c1 c2 1
      = Polynomial.C (phi : K) * Polynomial.X + Polynomial.C (c0 0) := by
  rw [x0_p_succ, x2_p_zero, x0_p_zero]
  ring

theorem x1_p_one_expand (c0 c1 c2 : Nat → K) :
    x1_p K c0 c1 c2 1
      = (Polynomial.C (phi : K) * Polynomial.X + Polynomial.C (c0 0)) ^ 2
        + Polynomial.C (c1 0) := by
  rw [x1_p_succ, x1_p_zero, x0_p_one_expand]
  ring

theorem x2_p_one_expand (c0 c1 c2 : Nat → K) :
    x2_p K c0 c1 c2 1
      = ((Polynomial.C (phi : K) * Polynomial.X + Polynomial.C (c0 0)) ^ 2
            + Polynomial.C (c1 0)) ^ 2
        + Polynomial.C (c2 0) := by
  rw [x2_p_succ, x2_p_zero, x1_p_one_expand]
  ring

/-! ### Degree lemmas at r = 1

We work over a CommRing K where `(phi : K) = 7 ≠ 0` (needed so that
`C φ * X` has natDegree 1 rather than degenerating). The hypothesis
captures the production case (BabyBear, KoalaBear, both have prime
characteristic > 7).
-/

variable [Nontrivial K]

/-- Leading coefficient lemma: for `7 ≠ 0` in `K`, `C 7 * X + C c` has
    natDegree 1. -/
theorem natDegree_phi_X_add_C (c : K) (h7 : (phi : K) ≠ 0) :
    (Polynomial.C (phi : K) * Polynomial.X + Polynomial.C c).natDegree = 1 := by
  rw [show Polynomial.C (phi : K) * Polynomial.X
        = Polynomial.C (phi : K) * Polynomial.X ^ 1 from by ring]
  rw [Polynomial.natDegree_add_C]
  rw [Polynomial.natDegree_C_mul_X_pow _ _ h7]

/-- `x_0(1)` has natDegree 1 = `2^(3·0 + 0)` (T113 formula at r=1, i=0). -/
theorem x0_p_one_natDegree (c0 c1 c2 : Nat → K) (h7 : (phi : K) ≠ 0) :
    (x0_p K c0 c1 c2 1).natDegree = 1 := by
  rw [x0_p_one_expand]
  exact natDegree_phi_X_add_C K (c0 0) h7

/-- `x_1(1)` has natDegree 2 = `2^(3·0 + 1)` (T113 formula at r=1, i=1).

    Requires `NoZeroDivisors K` so that squaring doubles the degree.
-/
theorem x1_p_one_natDegree [NoZeroDivisors K] (c0 c1 c2 : Nat → K)
    (h7 : (phi : K) ≠ 0) :
    (x1_p K c0 c1 c2 1).natDegree = 2 := by
  rw [x1_p_one_expand]
  -- Goal: ((C 7 * X + C (c0 0))^2 + C (c1 0)).natDegree = 2
  -- Inner: (C 7 * X + C (c0 0))^2 has natDegree 2
  have hinner :
      (Polynomial.C (phi : K) * Polynomial.X + Polynomial.C (c0 0)).natDegree = 1 :=
    natDegree_phi_X_add_C K (c0 0) h7
  rw [Polynomial.natDegree_add_C, Polynomial.natDegree_pow, hinner]

/-- `x_2(1)` has natDegree 4 = `2^(3·0 + 2)` (T113 formula at r=1, i=2). -/
theorem x2_p_one_natDegree [NoZeroDivisors K] (c0 c1 c2 : Nat → K)
    (h7 : (phi : K) ≠ 0) :
    (x2_p K c0 c1 c2 1).natDegree = 4 := by
  rw [x2_p_one_expand]
  -- Inner squared has natDegree 2, outer squared has natDegree 4
  have hinner :
      ((Polynomial.C (phi : K) * Polynomial.X + Polynomial.C (c0 0)) ^ 2
          + Polynomial.C (c1 0)).natDegree = 2 := by
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_pow,
        natDegree_phi_X_add_C K (c0 0) h7]
  rw [Polynomial.natDegree_add_C, Polynomial.natDegree_pow, hinner]

/-! ### Round-step degree helper

The inductive step at each round has the form
`x_i(r+1) = C φ · x_i(r) + q^2 + C c`

where `q` is some polynomial whose natDegree is known. The lemma below
abstracts this: when `q^2` strictly dominates `C φ · p`, the result has
natDegree equal to `2 · q.natDegree`.

We need `NoZeroDivisors K` and `q ≠ 0` for `(q^2).natDegree = 2·q.natDegree`.
The strict-domination hypothesis ensures the sum doesn't collapse.
-/

variable [NoZeroDivisors K]

theorem round_step_natDegree (p q : Polynomial K) (c : K) (a : K)
    (hq : q ≠ 0) (hdom : p.natDegree < 2 * q.natDegree) :
    (Polynomial.C a * p + q ^ 2 + Polynomial.C c).natDegree
      = 2 * q.natDegree := by
  rw [Polynomial.natDegree_add_C]
  -- Goal: (C a * p + q^2).natDegree = 2 * q.natDegree
  have hCp : (Polynomial.C a * p).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_C_mul_le a p
  have hCp_lt : (Polynomial.C a * p).natDegree < 2 * q.natDegree :=
    lt_of_le_of_lt hCp hdom
  have hq2 : (q ^ 2).natDegree = 2 * q.natDegree :=
    Polynomial.natDegree_pow q 2
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (by rw [hq2]; exact hCp_lt), hq2]

/-! ### Main theorem: joint degree formula

The joint statement `T113_degree_t3` packages the per-cell degree
results in one inductive theorem, since the recurrence for `x_i(r+1)`
references both `x_i(r)` (previous round) AND `x_{i-1}(r+1)` (current
round freshly computed), requiring all three statements to advance
together.
-/

/-- For r ≥ 1: per-cell natDegree formula at t = 3, paper convention.

    Matches the T113 closed form `deg_{x_0(0)}(x_i(r)) = 2^(t(r-1) + i)`
    at t = 3. -/
theorem T113_degree_t3 (c0 c1 c2 : Nat → K) (h7 : (phi : K) ≠ 0) :
    ∀ r : Nat, 1 ≤ r →
      (x0_p K c0 c1 c2 r).natDegree = 2 ^ (3 * (r - 1)) ∧
      (x1_p K c0 c1 c2 r).natDegree = 2 ^ (3 * (r - 1) + 1) ∧
      (x2_p K c0 c1 c2 r).natDegree = 2 ^ (3 * (r - 1) + 2) := by
  intro r hr
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hrz : r = 0
    · -- Base case: r + 1 = 1
      subst hrz
      refine ⟨?_, ?_, ?_⟩
      · simp only [Nat.add_sub_cancel, Nat.mul_zero, pow_zero]
        exact x0_p_one_natDegree K c0 c1 c2 h7
      · simp only [Nat.add_sub_cancel, Nat.mul_zero, zero_add, pow_one]
        exact x1_p_one_natDegree K c0 c1 c2 h7
      · simp only [Nat.add_sub_cancel, Nat.mul_zero, zero_add]
        -- Goal: x2_p ... 1.natDegree = 2^2 = 4
        rw [show (2 : Nat) ^ 2 = 4 from by norm_num]
        exact x2_p_one_natDegree K c0 c1 c2 h7
    · -- Inductive step: r ≥ 1, advancing to r + 1
      have hr_pos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrz
      obtain ⟨ih0, ih1, ih2⟩ := ih hr_pos
      -- Useful: r - 1 + 1 = r when r ≥ 1
      have hr_sub : r - 1 + 1 = r := Nat.sub_add_cancel hr_pos
      have hrsucc_sub : r + 1 - 1 = r := by omega
      -- Step 1: x_0(r+1) has natDegree 2^(3·r)
      have hx0_succ_ne : x2_p K c0 c1 c2 r ≠ 0 := by
        intro hzero
        have : (x2_p K c0 c1 c2 r).natDegree = 0 := by
          rw [hzero]; exact Polynomial.natDegree_zero
        rw [ih2] at this
        have : (2 : Nat) ^ (3 * (r - 1) + 2) > 0 := pow_pos (by norm_num : (0:Nat) < 2) _
        omega
      have hx0_dom :
          (x0_p K c0 c1 c2 r).natDegree < 2 * (x2_p K c0 c1 c2 r).natDegree := by
        rw [ih0, ih2]
        -- 2^(3(r-1)) < 2 · 2^(3(r-1)+2) = 2^(3(r-1)+3)
        have : (2 : Nat) * 2 ^ (3 * (r - 1) + 2) = 2 ^ (3 * (r - 1) + 3) := by ring
        rw [this]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hx0_step : (x0_p K c0 c1 c2 (r + 1)).natDegree
          = 2 * (x2_p K c0 c1 c2 r).natDegree := by
        rw [x0_p_succ]
        exact round_step_natDegree K (x0_p K c0 c1 c2 r) (x2_p K c0 c1 c2 r)
              (c0 r) (phi : K) hx0_succ_ne hx0_dom
      have hx0_val : (x0_p K c0 c1 c2 (r + 1)).natDegree = 2 ^ (3 * r) := by
        rw [hx0_step, ih2]
        have : (2 : Nat) * 2 ^ (3 * (r - 1) + 2) = 2 ^ (3 * r) := by
          rw [show (2 : Nat) * 2 ^ (3 * (r - 1) + 2)
                = 2 ^ (3 * (r - 1) + 2 + 1) from by ring]
          congr 1; omega
        exact this
      -- Step 2: x_1(r+1) has natDegree 2^(3·r + 1)
      have hx1_succ_ne : x0_p K c0 c1 c2 (r + 1) ≠ 0 := by
        intro hzero
        have : (x0_p K c0 c1 c2 (r + 1)).natDegree = 0 := by
          rw [hzero]; exact Polynomial.natDegree_zero
        rw [hx0_val] at this
        have : (2 : Nat) ^ (3 * r) > 0 := pow_pos (by norm_num : (0:Nat) < 2) _
        omega
      have hx1_dom :
          (x1_p K c0 c1 c2 r).natDegree < 2 * (x0_p K c0 c1 c2 (r + 1)).natDegree := by
        rw [ih1, hx0_val]
        -- 2^(3(r-1)+1) < 2 · 2^(3r) = 2^(3r+1)
        have : (2 : Nat) * 2 ^ (3 * r) = 2 ^ (3 * r + 1) := by ring
        rw [this]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hx1_step : (x1_p K c0 c1 c2 (r + 1)).natDegree
          = 2 * (x0_p K c0 c1 c2 (r + 1)).natDegree := by
        rw [x1_p_succ]
        exact round_step_natDegree K (x1_p K c0 c1 c2 r) (x0_p K c0 c1 c2 (r + 1))
              (c1 r) (phi : K) hx1_succ_ne hx1_dom
      have hx1_val : (x1_p K c0 c1 c2 (r + 1)).natDegree = 2 ^ (3 * r + 1) := by
        rw [hx1_step, hx0_val]
        ring
      -- Step 3: x_2(r+1) has natDegree 2^(3·r + 2)
      have hx2_succ_ne : x1_p K c0 c1 c2 (r + 1) ≠ 0 := by
        intro hzero
        have : (x1_p K c0 c1 c2 (r + 1)).natDegree = 0 := by
          rw [hzero]; exact Polynomial.natDegree_zero
        rw [hx1_val] at this
        have : (2 : Nat) ^ (3 * r + 1) > 0 := pow_pos (by norm_num : (0:Nat) < 2) _
        omega
      have hx2_dom :
          (x2_p K c0 c1 c2 r).natDegree < 2 * (x1_p K c0 c1 c2 (r + 1)).natDegree := by
        rw [ih2, hx1_val]
        have : (2 : Nat) * 2 ^ (3 * r + 1) = 2 ^ (3 * r + 2) := by ring
        rw [this]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hx2_step : (x2_p K c0 c1 c2 (r + 1)).natDegree
          = 2 * (x1_p K c0 c1 c2 (r + 1)).natDegree := by
        rw [x2_p_succ]
        exact round_step_natDegree K (x2_p K c0 c1 c2 r) (x1_p K c0 c1 c2 (r + 1))
              (c2 r) (phi : K) hx2_succ_ne hx2_dom
      have hx2_val : (x2_p K c0 c1 c2 (r + 1)).natDegree = 2 ^ (3 * r + 2) := by
        rw [hx2_step, hx1_val]
        ring
      -- Combine into goal form for r + 1
      refine ⟨?_, ?_, ?_⟩
      · rw [hx0_val, hrsucc_sub]
      · rw [hx1_val, hrsucc_sub]
      · rw [hx2_val, hrsucc_sub]

/-! ### D_I corollary

At round n (the depth-n boundary), the eliminating polynomial is
`x_0(n) − τ`, of degree `2^(3(n-1))`. This is exactly the paper's
`D_I = 2^(t(n-1))` at t = 3.
-/

/-- D_I = `2^(3(n-1))` at t = 3, paper convention. -/
theorem T113_D_I_t3 (c0 c1 c2 : Nat → K) (tau : K) (h7 : (phi : K) ≠ 0)
    (n : Nat) (hn : 1 ≤ n) :
    (x0_p K c0 c1 c2 n - Polynomial.C tau).natDegree = 2 ^ (3 * (n - 1)) := by
  have hx0 : (x0_p K c0 c1 c2 n).natDegree = 2 ^ (3 * (n - 1)) :=
    (T113_degree_t3 K c0 c1 c2 h7 n hn).1
  -- Subtracting a constant doesn't change natDegree when degree > 0
  have hpos : 0 < 2 ^ (3 * (n - 1)) := pow_pos (by norm_num : (0:Nat) < 2) _
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.natDegree_add_C]
  exact hx0

-- Axiom check: T113_degree_t3 closes with only the standard 3 axioms
-- (propext, Classical.choice, Quot.sound). Same kernel-trust footprint
-- as boolQuot_finrank (paper d_reg=2n) and t2_general_dim.
#print axioms T113_degree_t3

#print axioms T113_D_I_t3

end Mambo.T3DegreeTracking
