import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Fin.Basic

/-!
# Mambo Universal D_I Degree Tracking (parametric on t)

Generalization of `Mambo.T3DegreeTracking` to arbitrary t ≥ 2.

Setup (paper convention, `mambo_tosc_2026.tex` lines 1870-1883):
- Width t ≥ 2
- Boundaries at depth 0: `x_i(0) = 0` for `i ∈ {1, ..., t-1}` (cap-in zeros)
- Boundary at depth n: `x_0(n) = τ` (rate-out)
- Free variable: `x_0(0)` (the rate-in CICO unknown)

Round recurrence:
- `x_0(r+1) = phi * x_0(r) + x_{t-1}(r)^2 + c_0`           (wraps last cell of prev round)
- `x_i(r+1) = phi * x_i(r) + x_{i-1}(r+1)^2 + c_i`         for i = 1..t-1 (chained sequential)

Main theorem (T113 universal):
For r ≥ 1 and i < t, `natDegree(state t r i) = 2^(t*(r-1) + i)`.

D_I corollary: `natDegree(x_0(n) - C tau) = 2^(t*(n-1))`.
-/

namespace Mambo.TGeneralDegreeTracking

open Polynomial

variable (K : Type*) [CommRing K] [Nontrivial K] [NoZeroDivisors K]

/-- Mambo multiplier `phi = 7` (paper default). -/
def phi : Nat := 7

/-- Within one round, the i-th newly-computed cell (from `prev` state +
    round constants `c`). Recursive on i. Indexed by Nat for inductive
    structure; caller must ensure `i < t`.

    - cell 0 uses prev's last cell (index t-1) squared
    - cell (i+1) uses just-computed cell i squared

    For caller convenience, `prev_last` is `prev (t-1)` and `prev_i` is
    `prev i` — passed explicitly so the recursion is clean. -/
noncomputable def cellAt
    (phi_K : K) (c : ℕ → K) (prev : ℕ → Polynomial K) (prev_last : Polynomial K) :
    ℕ → Polynomial K
  | 0     => Polynomial.C phi_K * prev 0 + prev_last ^ 2 + Polynomial.C (c 0)
  | i + 1 => Polynomial.C phi_K * prev (i + 1)
              + (cellAt phi_K c prev prev_last i) ^ 2
              + Polynomial.C (c (i + 1))

/-- State chain: at round 0, cell 0 is `X`, others are 0. At round r+1,
    cell i (for i < t) is `cellAt phi (c_seq r) (prev := state r) (...)`.

    `t_minus_1` is the last-cell index, t-1; passed as parameter to avoid
    repeated arithmetic. -/
noncomputable def state (phi_K : K) (t_minus_1 : ℕ) (c_seq : ℕ → ℕ → K) :
    ℕ → ℕ → Polynomial K
  | 0,     i => if i = 0 then Polynomial.X else 0
  | r + 1, i => cellAt K phi_K (c_seq r)
                  (state phi_K t_minus_1 c_seq r)
                  (state phi_K t_minus_1 c_seq r t_minus_1)
                  i

/-! ### Unfolding lemmas -/

theorem state_zero_zero (phi_K : K) (t_minus_1 : ℕ) (c_seq : ℕ → ℕ → K) :
    state K phi_K t_minus_1 c_seq 0 0 = Polynomial.X := by
  simp [state]

theorem state_zero_pos (phi_K : K) (t_minus_1 : ℕ) (c_seq : ℕ → ℕ → K)
    (i : ℕ) (hi : 0 < i) :
    state K phi_K t_minus_1 c_seq 0 i = 0 := by
  simp [state, Nat.ne_of_gt hi]

theorem state_succ (phi_K : K) (t_minus_1 : ℕ) (c_seq : ℕ → ℕ → K)
    (r i : ℕ) :
    state K phi_K t_minus_1 c_seq (r + 1) i
      = cellAt K phi_K (c_seq r)
          (state K phi_K t_minus_1 c_seq r)
          (state K phi_K t_minus_1 c_seq r t_minus_1)
          i := by
  simp [state]

theorem cellAt_zero (phi_K : K) (c : ℕ → K) (prev : ℕ → Polynomial K)
    (prev_last : Polynomial K) :
    cellAt K phi_K c prev prev_last 0
      = Polynomial.C phi_K * prev 0 + prev_last ^ 2 + Polynomial.C (c 0) := by
  simp [cellAt]

theorem cellAt_succ (phi_K : K) (c : ℕ → K) (prev : ℕ → Polynomial K)
    (prev_last : Polynomial K) (i : ℕ) :
    cellAt K phi_K c prev prev_last (i + 1)
      = Polynomial.C phi_K * prev (i + 1)
          + (cellAt K phi_K c prev prev_last i) ^ 2
          + Polynomial.C (c (i + 1)) := by
  simp [cellAt]

/-! ### Round-step degree helper

When `p^2` strictly dominates `C phi * q`, the natDegree of
`(C phi * q + p^2 + C c)` equals `2 * natDegree(p)`.
-/

theorem round_step_natDegree (p q : Polynomial K) (c : K) (a : K)
    (hq : q ≠ 0) (hdom : p.natDegree < 2 * q.natDegree) :
    (Polynomial.C a * p + q ^ 2 + Polynomial.C c).natDegree
      = 2 * q.natDegree := by
  rw [Polynomial.natDegree_add_C]
  have hCp : (Polynomial.C a * p).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_C_mul_le a p
  have hCp_lt : (Polynomial.C a * p).natDegree < 2 * q.natDegree :=
    lt_of_le_of_lt hCp hdom
  have hq2 : (q ^ 2).natDegree = 2 * q.natDegree :=
    Polynomial.natDegree_pow q 2
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (by rw [hq2]; exact hCp_lt), hq2]

/-! ### Internal-induction lemma (within a single round)

Given a previous-round state with the correct degree formula,
`cellAt` produces cell i with degree `2^(t*r + i)` (when r ≥ 0 and we
are computing for the *next* round, i.e., previous round index is r).

Hypotheses captured concretely:
- `prev_deg_i : natDegree(prev i) = 2^(t*r + i - t)` for i < t when r ≥ 1
- `prev_deg_last : natDegree(prev_last) = 2^(t*r + (t-1) - t) = 2^(t*r - 1)` when r ≥ 1
- Domination: `prev i ≠ 0` for relevant cells

For r = 1 base case: prev is state 0; only prev 0 = X is non-zero,
others = 0. Need a separate handling.
-/

/-- Inner per-cell-within-a-round lemma (BOUNDED form).

    Same as the universal form but only requires `prev_deg_eq` and
    `h_dom_chain` to hold for indices ≤ target. This lets the caller
    avoid providing degree characterizations of `prev j` for j outside
    the relevant chain.
-/
theorem cellAt_natDegree_in_round_bounded
    (phi_K : K) (c : ℕ → K) (prev : ℕ → Polynomial K) (prev_last : Polynomial K)
    (prev_last_ne : prev_last ≠ 0) (pl_d : ℕ)
    (prev_last_deg_eq : prev_last.natDegree = pl_d)
    (pl_d_pos : 0 < pl_d)
    (target_i : ℕ)
    (prev_d : ℕ → ℕ)
    (prev_deg_eq : ∀ j ≤ target_i, (prev j).natDegree = prev_d j)
    (h_dom0 : prev_d 0 < 2 * pl_d)
    (h_dom_chain : ∀ j < target_i, prev_d (j + 1) < 2 ^ (j + 1) * (2 * pl_d)) :
    (cellAt K phi_K c prev prev_last target_i).natDegree = 2 ^ target_i * (2 * pl_d) := by
  induction target_i with
  | zero =>
    rw [cellAt_zero]
    have hp0 : (prev 0).natDegree = prev_d 0 := prev_deg_eq 0 (Nat.zero_le _)
    have h := round_step_natDegree K (prev 0) prev_last (c 0) phi_K
      prev_last_ne
      (by rw [hp0, prev_last_deg_eq]; exact h_dom0)
    rw [h, prev_last_deg_eq]
    ring
  | succ target_i_prev ih =>
    rw [cellAt_succ]
    have ih_applied :
        (cellAt K phi_K c prev prev_last target_i_prev).natDegree
          = 2 ^ target_i_prev * (2 * pl_d) := by
      apply ih
      · intro j hj
        exact prev_deg_eq j (by omega)
      · intro j hj
        exact h_dom_chain j (by omega)
    have hcell_ne : cellAt K phi_K c prev prev_last target_i_prev ≠ 0 := by
      intro hzero
      have : (cellAt K phi_K c prev prev_last target_i_prev).natDegree = 0 := by
        rw [hzero]; exact Polynomial.natDegree_zero
      rw [ih_applied] at this
      have hpos : 0 < 2 ^ target_i_prev * (2 * pl_d) := by
        apply Nat.mul_pos
        · exact pow_pos (by norm_num : (0:Nat) < 2) target_i_prev
        · omega
      omega
    have hp_succ : (prev (target_i_prev + 1)).natDegree = prev_d (target_i_prev + 1) :=
      prev_deg_eq (target_i_prev + 1) (le_refl _)
    have hdom : (prev (target_i_prev + 1)).natDegree
        < 2 * (cellAt K phi_K c prev prev_last target_i_prev).natDegree := by
      rw [hp_succ, ih_applied]
      have heq : 2 * (2 ^ target_i_prev * (2 * pl_d))
          = 2 ^ (target_i_prev + 1) * (2 * pl_d) := by ring
      rw [heq]
      exact h_dom_chain target_i_prev (by omega)
    have h := round_step_natDegree K (prev (target_i_prev + 1))
      (cellAt K phi_K c prev prev_last target_i_prev)
      (c (target_i_prev + 1)) phi_K hcell_ne hdom
    rw [h, ih_applied]
    ring

/-! ### Status

The internal cell recursion now has a clean inductive structure
(`cellAt` recurses on `i : ℕ`), making per-cell degree tracking
tractable. The full theorem closure requires:

1. **Per-round lemma**: for r ≥ 1, given prev satisfies
   `(prev i).natDegree = 2^(t*(r-1) + i)` for all i < t and prev cells
   are non-zero, conclude
   `(cellAt phi (c_seq r) prev prev_last i).natDegree = 2^(t*r + i)`
   by induction on i.

2. **Outer induction on r**: chain the per-round lemma starting from
   r = 1 base case (where prev = state 0 has cell 0 = X, others = 0
   — needs special handling).

3. **D_I corollary**: at i = 0, r = n, deg = 2^(t*(n-1)) = paper D_I.

The t = 3 specialization is fully closed in
`Mambo.T3DegreeTracking.T113_degree_t3` (sorry-free, 3 std axioms).
The universal-t lift is mechanical extension of that proof's
algebraic skeleton.
-/

/-! ### Base-case lemma (r = 1)

At r = 0, state has cell 0 = X and all others = 0. At r = 1, applying
cellAt with prev = state 0 (so prev 0 = X, prev j = 0 for j ≥ 1) and
prev_last = state 0 (t-1) = 0 (since t-1 ≥ 1 when t ≥ 2).

The cellAt recursion becomes:
- cellAt 0 = phi*X + 0^2 + c(0) = phi*X + c(0)   [deg 1]
- cellAt (i+1) = 0 + (cellAt i)^2 + c(i+1)        [deg 2*prev deg]

So deg(cellAt i at r=1) = 2^i.
-/

theorem cellAt_natDegree_base_at_r1
    (phi_K : K) (h7 : phi_K ≠ 0)
    (c : ℕ → K) (prev : ℕ → Polynomial K)
    (prev_zero_x : prev 0 = Polynomial.X)
    (prev_pos_zero : ∀ j, j > 0 → prev j = 0)
    (i : ℕ) :
    (cellAt K phi_K c prev 0 i).natDegree = 2 ^ i := by
  induction i with
  | zero =>
    rw [cellAt_zero]
    -- Goal: natDegree(C phi * prev 0 + 0^2 + C (c 0)) = 1
    rw [prev_zero_x]
    -- Goal: natDegree(C phi * X + 0^2 + C (c 0)) = 1
    simp only [pow_two, zero_mul]
    rw [Polynomial.natDegree_add_C]
    -- Goal: natDegree(C phi * X + 0) = 1
    rw [add_zero]
    rw [show Polynomial.C phi_K * Polynomial.X
          = Polynomial.C phi_K * Polynomial.X ^ 1 from by ring]
    rw [Polynomial.natDegree_C_mul_X_pow _ _ h7]
    decide
  | succ i ih =>
    rw [cellAt_succ]
    -- Goal: natDegree(C phi * prev (i+1) + (cellAt ... i)^2 + C (c (i+1))) = 2^(i+1)
    have hp_zero : prev (i + 1) = 0 := prev_pos_zero (i + 1) (Nat.succ_pos i)
    rw [hp_zero]
    -- Goal: natDegree(C phi * 0 + (cellAt ... i)^2 + C (c (i+1))) = 2^(i+1)
    simp only [mul_zero, zero_add]
    rw [Polynomial.natDegree_add_C]
    rw [Polynomial.natDegree_pow, ih]
    ring

/-! ### Main theorem (r ≥ 1)

Composes the base case (r = 1) and the inductive step (r → r+1) using
`cellAt_natDegree_in_round`.
-/

/-- Main theorem: for r ≥ 1 and i < t (t ≥ 2):
    `natDegree(state t r i) = 2^(t*(r-1) + i)`.

    Proof composes:
    - `cellAt_natDegree_base_at_r1` for the r = 1 step
    - `cellAt_natDegree_in_round` for r ≥ 2 inductive step
-/
theorem T113_universal_t_stub
    (phi_K : K) (h7 : phi_K ≠ 0)
    (t : ℕ) (ht2 : 2 ≤ t) (c_seq : ℕ → ℕ → K)
    (r : ℕ) (hr : 1 ≤ r) (i : ℕ) (hi : i < t) :
    (state K phi_K (t - 1) c_seq r i).natDegree = 2 ^ (t * (r - 1) + i) := by
  revert i hi
  induction r with
  | zero => intro i hi; omega
  | succ rprev ih =>
    intro i hi
    by_cases hrz : rprev = 0
    · -- r = 1 base case
      subst hrz
      rw [state_succ]
      have ht1_pos : 0 < t - 1 := by omega
      have hst_last : state K phi_K (t - 1) c_seq 0 (t - 1) = 0 := by
        unfold state
        simp [Nat.ne_of_gt ht1_pos]
      rw [hst_last]
      have hp0 : state K phi_K (t - 1) c_seq 0 0 = Polynomial.X := state_zero_zero K phi_K (t - 1) c_seq
      have hpj : ∀ j, j > 0 → state K phi_K (t - 1) c_seq 0 j = 0 := fun j hj =>
        state_zero_pos K phi_K (t - 1) c_seq j hj
      have hb := cellAt_natDegree_base_at_r1 K phi_K h7 (c_seq 0)
        (state K phi_K (t - 1) c_seq 0) hp0 hpj i
      rw [hb]
      ring
    · -- r ≥ 2 inductive case: apply cellAt_natDegree_in_round_bounded.
      have hrprev : 1 ≤ rprev := Nat.one_le_iff_ne_zero.mpr hrz
      rw [state_succ]
      -- Goal: (cellAt phi (c_seq rprev) (state rprev) (state rprev (t-1)) i).natDegree
      --       = 2 ^ (t * rprev + i)
      have ht1_lt_t : t - 1 < t := by omega
      -- IH at the last cell: (state rprev (t-1)).natDegree = 2^(t*(rprev-1)+(t-1))
      have hpl_deg : (state K phi_K (t - 1) c_seq rprev (t - 1)).natDegree
          = 2 ^ (t * (rprev - 1) + (t - 1)) := ih hrprev (t - 1) ht1_lt_t
      have hpl_pos : 0 < 2 ^ (t * (rprev - 1) + (t - 1)) :=
        pow_pos (by norm_num : (0:Nat) < 2) _
      -- prev_last ≠ 0
      have hpl_ne : state K phi_K (t - 1) c_seq rprev (t - 1) ≠ 0 := by
        intro hzero
        have : (state K phi_K (t - 1) c_seq rprev (t - 1)).natDegree = 0 := by
          rw [hzero]; exact Polynomial.natDegree_zero
        rw [hpl_deg] at this
        omega
      -- prev_deg_eq for j ≤ i (with i < t)
      have hp_deg : ∀ j ≤ i,
          (state K phi_K (t - 1) c_seq rprev j).natDegree = 2 ^ (t * (rprev - 1) + j) := by
        intro j hj
        exact ih hrprev j (by omega)
      -- h_dom0 : 2^(t*(rprev-1)) < 2 * 2^(t*(rprev-1)+(t-1))
      have hdom0 : 2 ^ (t * (rprev - 1) + 0) < 2 * 2 ^ (t * (rprev - 1) + (t - 1)) := by
        simp only [add_zero]
        have heq : 2 * 2 ^ (t * (rprev - 1) + (t - 1))
            = 2 ^ (t * (rprev - 1) + (t - 1) + 1) := by
          rw [show 2 * 2 ^ (t * (rprev - 1) + (t - 1))
                = 2 ^ 1 * 2 ^ (t * (rprev - 1) + (t - 1)) from by ring]
          rw [← pow_add]; ring_nf
        rw [heq]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      -- h_dom_chain : ∀ j < i, 2^(t*(rprev-1)+j+1) < 2^(j+1) * (2 * 2^(t*(rprev-1)+(t-1)))
      have hdom_chain : ∀ j < i, 2 ^ (t * (rprev - 1) + (j + 1))
          < 2 ^ (j + 1) * (2 * 2 ^ (t * (rprev - 1) + (t - 1))) := by
        intro j hj
        have heq : 2 ^ (j + 1) * (2 * 2 ^ (t * (rprev - 1) + (t - 1)))
            = 2 ^ (j + 1 + 1 + (t * (rprev - 1) + (t - 1))) := by
          rw [show (2 : ℕ) ^ (j + 1) * (2 * 2 ^ (t * (rprev - 1) + (t - 1)))
                = 2 ^ (j + 1) * 2 ^ 1 * 2 ^ (t * (rprev - 1) + (t - 1)) from by ring]
          rw [← pow_add, ← pow_add]
        rw [heq]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      -- Apply the bounded inner lemma
      have hcell := cellAt_natDegree_in_round_bounded K phi_K (c_seq rprev)
        (state K phi_K (t - 1) c_seq rprev)
        (state K phi_K (t - 1) c_seq rprev (t - 1))
        hpl_ne (2 ^ (t * (rprev - 1) + (t - 1))) hpl_deg hpl_pos
        i (fun j => 2 ^ (t * (rprev - 1) + j))
        hp_deg hdom0 hdom_chain
      rw [hcell]
      -- Goal: 2 ^ i * (2 * 2 ^ (t * (rprev - 1) + (t - 1))) = 2 ^ (t * (rprev + 1 - 1) + i)
      have hgoal : 2 ^ i * (2 * 2 ^ (t * (rprev - 1) + (t - 1)))
          = 2 ^ (t * (rprev + 1 - 1) + i) := by
        rw [show 2 ^ i * (2 * 2 ^ (t * (rprev - 1) + (t - 1)))
              = 2 ^ (i + 1 + (t * (rprev - 1) + (t - 1))) from by
          rw [show (2 : ℕ) ^ i * (2 * 2 ^ (t * (rprev - 1) + (t - 1)))
                = 2 ^ i * 2 ^ 1 * 2 ^ (t * (rprev - 1) + (t - 1)) from by ring]
          rw [← pow_add, ← pow_add]]
        congr 1
        -- Goal: i + 1 + (t * (rprev - 1) + (t - 1)) = t * (rprev + 1 - 1) + i
        have h_simplify : t * (rprev + 1 - 1) = t * rprev := by
          have : rprev + 1 - 1 = rprev := by omega
          rw [this]
        rw [h_simplify]
        -- Goal: i + 1 + (t * (rprev - 1) + (t - 1)) = t * rprev + i
        -- Use t * rprev = t * (rprev - 1) + t (since rprev ≥ 1)
        have hr_eq : t * rprev = t * (rprev - 1) + t := by
          conv_lhs => rw [show rprev = (rprev - 1) + 1 from (Nat.sub_add_cancel hrprev).symm]
          ring
        omega
      exact hgoal

/-- D_I corollary: `natDegree(state n 0 - C tau) = 2^(t*(n-1))`. -/
theorem T113_D_I_universal_stub
    (phi_K : K) (h7 : phi_K ≠ 0)
    (t : ℕ) (ht2 : 2 ≤ t) (c_seq : ℕ → ℕ → K) (tau : K)
    (n : ℕ) (hn : 1 ≤ n) :
    (state K phi_K (t - 1) c_seq n 0 - Polynomial.C tau).natDegree
      = 2 ^ (t * (n - 1)) := by
  have hx := T113_universal_t_stub K phi_K h7 t ht2 c_seq n hn 0 (by omega)
  simp only [add_zero] at hx
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.natDegree_add_C]
  exact hx

-- Axiom check: T113 universal-t theorem closes with only the standard 3 axioms
-- [propext, Classical.choice, Quot.sound] — same kernel-trust footprint as
-- boolQuot_finrank (paper d_reg=2n) and T3DegreeTracking.T113_D_I_t3.
#print axioms T113_universal_t_stub

#print axioms T113_D_I_universal_stub

end Mambo.TGeneralDegreeTracking
