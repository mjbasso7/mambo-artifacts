import Mambo.T3CicoIdeal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.ComputeDegree

/-!
# Mambo t = 3 Generic-n Eliminating Polynomial (scaffold)

Mirror of `Mambo.T2GeneralN` at width 3. The free variable for the
CICO elimination chain is `s_{2, 0}` (the last-cell initial value);
all other cells of all rounds are expressed as polynomials in this
single free variable via the coupled-quadratic recurrences.

Per the empirical 3-cell data:
`dim_K(R_{3,n}/I_{3,n}) = 2^{3(n-1)} = 8^{n-1}`. The eliminating
univariate `U_n^{t=3}` has natDegree `8^{n-1}` accordingly.

This file:
1. Defines the three mutually recursive iterators `s0_iter`, `s1_iter`,
   `s2_iter` over `Polynomial K` (with `X = s_{2,0}` as the free
   generator).
2. Defines `U_n_t3 := s0_iter n - C tau`.
3. (FUTURE) Mirror of `t2_general_dim` proof: AdjoinRoot bridge to
   conclude `dim_K(R_{3,n}/I_{3,n}) = 8^{n-1}` formally.

Step 3 is a paper-additive result (empirical, no paper Thm
hilb_closed at t=3 yet). Following the t=2 template at
`Mambo.T2GeneralN`, the full proof is mechanical extension.
-/

namespace Mambo.T3GeneralN

open Mambo.T3CicoIdeal MvPolynomial

variable (K : Type*) [Field K]

/-! ### Three mutually recursive iterators at t = 3

Convention: variables `s_{c, r}` for `c ∈ Fin 3`, `r ∈ Fin (n+1)`.
The free variable for the elimination is `s_{2, 0}` (= `Polynomial.X`
in the symbolic substitution ring).

Round recurrences (paper t = 3 coupled-sequential):
  s_{0, r+1} = φ · s_{0, r} + (s_{2, r})²       + c_{0,r}
  s_{1, r+1} = φ · s_{1, r} + (s_{0, r+1})²     + c_{1,r}
  s_{2, r+1} = φ · s_{2, r} + (s_{1, r+1})²     + c_{2,r}

Boundary: `s_{0, 0} = 0`. The free variable `s_{2, 0}` is encoded by
`s2_iter 0 = Polynomial.X`.

**Note on natural free-variable count vs cyclicity** (revised per universal
cyclicity finding, 5-cell empirical at t=2,3,4 × n=3,4,5):

At t = 3 the naive variable count suggests TWO "free" cells (`s_{1, 0}`
and `s_{2, 0}`) rather than one — chain coupling alone leaves
`s_{1, 0}` underdetermined by round constraints + boundary. This led
to an earlier scoping note "needs bivariate-AdjoinRoot infrastructure"
in this file.

That earlier note was WRONG. The empirical universal-cyclicity finding
shows the Mambo CICO quotient at t = 3 is a CYCLIC K[X]-module under
mult-by-primitive-variable: minpoly = charpoly of degree D_I = 2·8^(n-1).
Hence the quotient is K-algebra-isomorphic to K[X]/(U_n) for some
univariate `U_n` of that degree — same shape as t = 2, just with a
similarity transform from the natural FGLM basis to the companion-matrix
basis.

So a UNIVARIATE-AdjoinRoot bridge (the same template used in
`Mambo.T2GeneralN.t2_general_dim` at t = 2) applies at t = 3 too,
once the cyclic-module property is formally captured.

The iterators below remain a useful symbolic-recurrence scaffold; the
remaining work is the cyclicity formalisation (Path A: per-n
native_decide on Lean Matrix; Path B: structural induction extending
the joint identity from `Mambo.T2GeneralN.t2_general_mk_X_iter_joint`).
-/

mutual
/-- Symbolic iterator for `s_{0, r}` (cell 0). `s0_iter 0 = 0` (boundary). -/
noncomputable def s0_iter (c0_seq c1_seq c2_seq : Nat → K) : Nat → Polynomial K
  | 0     => 0
  | r + 1 =>
      (Polynomial.C 7) * s0_iter c0_seq c1_seq c2_seq r
        + (s2_iter c0_seq c1_seq c2_seq r) ^ 2
        + Polynomial.C (c0_seq r)

/-- Symbolic iterator for `s_{1, r}` (cell 1). `s1_iter 0 = X` (free, placeholder). -/
noncomputable def s1_iter (c0_seq c1_seq c2_seq : Nat → K) : Nat → Polynomial K
  | 0     => Polynomial.X
  | r + 1 =>
      (Polynomial.C 7) * s1_iter c0_seq c1_seq c2_seq r
        + (s0_iter c0_seq c1_seq c2_seq (r + 1)) ^ 2
        + Polynomial.C (c1_seq r)

/-- Symbolic iterator for `s_{2, r}` (cell 2). `s2_iter 0 = X` (the primitive
    free variable for the t = 3 elimination chain).

    `s_{2, 0}` is the primitive cell: under universal cyclicity (empirical
    at t=3, n=3), the K[X]-module structure on the Mambo CICO quotient
    via `x ↦ s_{2, 0}-multiplication` is cyclic, so `s_{2, 0}` alone
    generates the entire quotient as a K-algebra. `s_{1, 0}` is then
    expressible as a polynomial in `s_{2, 0}` via the chain coupling. -/
noncomputable def s2_iter (c0_seq c1_seq c2_seq : Nat → K) : Nat → Polynomial K
  | 0     => Polynomial.X
  | r + 1 =>
      (Polynomial.C 7) * s2_iter c0_seq c1_seq c2_seq r
        + (s1_iter c0_seq c1_seq c2_seq (r + 1)) ^ 2
        + Polynomial.C (c2_seq r)
end

/-- The (scaffold) eliminating polynomial at depth n: `U_n^{t=3}(X) := s0_iter n - τ`.

    Caveat: this is the same form as `Mambo.T2GeneralN.U_n` but at t = 3 the
    full picture requires bivariate elimination (two free vars). This
    univariate version captures only part of the structure. -/
noncomputable def U_n_t3 (c0_seq c1_seq c2_seq : Nat → K) (tau : K) (n : Nat) :
    Polynomial K :=
  s0_iter K c0_seq c1_seq c2_seq n - Polynomial.C tau

/-! ### Base-case reduction lemmas -/

theorem s0_iter_zero (c0 c1 c2 : Nat → K) :
    s0_iter K c0 c1 c2 0 = 0 := by
  simp only [s0_iter]

theorem s1_iter_zero (c0 c1 c2 : Nat → K) :
    s1_iter K c0 c1 c2 0 = Polynomial.X := by
  simp only [s1_iter]

theorem s2_iter_zero (c0 c1 c2 : Nat → K) :
    s2_iter K c0 c1 c2 0 = Polynomial.X := by
  simp only [s2_iter]

theorem s0_iter_succ (c0 c1 c2 : Nat → K) (r : Nat) :
    s0_iter K c0 c1 c2 (r + 1)
      = Polynomial.C 7 * s0_iter K c0 c1 c2 r + (s2_iter K c0 c1 c2 r) ^ 2
        + Polynomial.C (c0 r) := by
  simp only [s0_iter]

theorem s1_iter_succ (c0 c1 c2 : Nat → K) (r : Nat) :
    s1_iter K c0 c1 c2 (r + 1)
      = Polynomial.C 7 * s1_iter K c0 c1 c2 r + (s0_iter K c0 c1 c2 (r + 1)) ^ 2
        + Polynomial.C (c1 r) := by
  simp only [s1_iter]

theorem s2_iter_succ (c0 c1 c2 : Nat → K) (r : Nat) :
    s2_iter K c0 c1 c2 (r + 1)
      = Polynomial.C 7 * s2_iter K c0 c1 c2 r + (s1_iter K c0 c1 c2 (r + 1)) ^ 2
        + Polynomial.C (c2 r) := by
  simp only [s2_iter]

/-! ### Sanity at n = 1

At n = 1, U_1^{t=3} = X² + c_{0,0} − τ (since s0_iter 1 = (s2_iter 0)² + c_{0,0}
= X² + c_{0,0}, then U_1 = X² + c_{0,0} - τ). Degree 2.

This is the SAME form as the t = 2 n = 1 case because the s_{0,r+1} recurrence
only sees s_{2,r}² (last cell), which at r=0 is just X² regardless of t. -/

example (c0 c1 c2 : Nat → K) (tau : K) :
    U_n_t3 K c0 c1 c2 tau 1 = Polynomial.X ^ 2 + Polynomial.C (c0 0) - Polynomial.C tau := by
  unfold U_n_t3
  rw [s0_iter_succ, s2_iter_zero, s0_iter_zero]
  ring

/-! ### Degree-growth theorems at n = 1 (concrete cells)

Pattern at t = 3 (mirror of `Mambo.T2GeneralN`):
- `natDegree(s0_iter n)` = `2·8^(n-1)` = `2^(3n-2)`  (n ≥ 1)
- `natDegree(s1_iter n)` = `4·8^(n-1)` = `2^(3n-1)`  (n ≥ 1)
- `natDegree(s2_iter n)` = `8^n`       = `2^(3n)`    (n ≥ 1; also n = 0)

`s0_iter`, `s1_iter`, `s2_iter` are all monic for n ≥ 1.
-/

/-- `s0_iter 1` reduces to `X² + C (c0 0)`. -/
theorem s0_iter_one_expand (c0 c1 c2 : Nat → K) :
    s0_iter K c0 c1 c2 1
      = Polynomial.X ^ 2 + Polynomial.C (c0 0) := by
  rw [s0_iter_succ, s2_iter_zero, s0_iter_zero]
  ring

/-- `s0_iter 1` is monic. -/
theorem s0_iter_one_monic (c0 c1 c2 : Nat → K) :
    (s0_iter K c0 c1 c2 1).Monic := by
  rw [s0_iter_one_expand]
  exact Polynomial.monic_X_pow_add_C (c0 0) (by decide)

/-- `s0_iter 1` has natDegree 2. -/
theorem s0_iter_one_natDegree (c0 c1 c2 : Nat → K) :
    (s0_iter K c0 c1 c2 1).natDegree = 2 := by
  rw [s0_iter_one_expand]
  rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]

/-- `s1_iter 1` explicit normal form. -/
theorem s1_iter_one_expand (c0 c1 c2 : Nat → K) :
    s1_iter K c0 c1 c2 1
      = Polynomial.C 7 * Polynomial.X
        + (Polynomial.X ^ 2 + Polynomial.C (c0 0)) ^ 2
        + Polynomial.C (c1 0) := by
  rw [s1_iter_succ, s1_iter_zero, s0_iter_one_expand]

/-- `s1_iter 1` is monic. -/
theorem s1_iter_one_monic (c0 c1 c2 : Nat → K) :
    (s1_iter K c0 c1 c2 1).Monic := by
  rw [s1_iter_one_expand]
  monicity!

/-- `s1_iter 1` has natDegree 4. -/
theorem s1_iter_one_natDegree (c0 c1 c2 : Nat → K) :
    (s1_iter K c0 c1 c2 1).natDegree = 4 := by
  rw [s1_iter_one_expand]
  compute_degree!

/-- `s2_iter 1` explicit normal form. -/
theorem s2_iter_one_expand (c0 c1 c2 : Nat → K) :
    s2_iter K c0 c1 c2 1
      = Polynomial.C 7 * Polynomial.X
        + (Polynomial.C 7 * Polynomial.X
            + (Polynomial.X ^ 2 + Polynomial.C (c0 0)) ^ 2
            + Polynomial.C (c1 0)) ^ 2
        + Polynomial.C (c2 0) := by
  rw [s2_iter_succ, s2_iter_zero, s1_iter_one_expand]

/-- `s2_iter 1` is monic. -/
theorem s2_iter_one_monic (c0 c1 c2 : Nat → K) :
    (s2_iter K c0 c1 c2 1).Monic := by
  rw [s2_iter_one_expand]
  monicity!

/-- `s2_iter 1` has natDegree 8. -/
theorem s2_iter_one_natDegree (c0 c1 c2 : Nat → K) :
    (s2_iter K c0 c1 c2 1).natDegree = 8 := by
  rw [s2_iter_one_expand]
  compute_degree!

/-! ### Inductive: 8^k positivity and strictly-greater inequalities (helpers) -/

private theorem eight_pow_pos (k : Nat) : 0 < (8 : Nat)^k := by positivity

private theorem eight_pow_strict (k : Nat) (hk : 1 ≤ k) : 8^(k-1) < 8^k := by
  have : k - 1 < k := Nat.sub_lt hk (by decide)
  exact Nat.pow_lt_pow_right (by decide : 1 < 8) this

private theorem two_eight_pow_lt (k : Nat) (hk : 1 ≤ k) : 2 * 8^(k-1) < 2 * 8^k := by
  have := eight_pow_strict k hk
  omega

private theorem four_eight_pow_lt (k : Nat) (hk : 1 ≤ k) : 4 * 8^(k-1) < 4 * 8^k := by
  have := eight_pow_strict k hk
  omega

/-! ### Inductive step: s0 at general k ≥ 1

`s0_iter (k+1) = 7·s0_iter k + (s2_iter k)² + C (c0 k)`. The `(s2_iter k)²`
term has natDegree `2 · 8^k`, dominating the linear `7·s0_iter k` (whose
natDegree ≤ `2 · 8^(k-1)`) and the constant `C (c0 k)`. -/
theorem s0_iter_succ_monic_natDegree (c0 c1 c2 : Nat → K) (k : Nat) (hk : 1 ≤ k)
    (h_s2_monic : (s2_iter K c0 c1 c2 k).Monic)
    (h_s2_deg : (s2_iter K c0 c1 c2 k).natDegree = 8^k)
    (h_s0_deg : (s0_iter K c0 c1 c2 k).natDegree ≤ 2 * 8^(k-1)) :
    (s0_iter K c0 c1 c2 (k+1)).Monic
      ∧ (s0_iter K c0 c1 c2 (k+1)).natDegree = 2 * 8^k := by
  rw [s0_iter_succ]
  rw [show (Polynomial.C 7 * s0_iter K c0 c1 c2 k + (s2_iter K c0 c1 c2 k) ^ 2
              + Polynomial.C (c0 k) : Polynomial K)
        = (s2_iter K c0 c1 c2 k) ^ 2
          + (Polynomial.C 7 * s0_iter K c0 c1 c2 k + Polynomial.C (c0 k)) by ring]
  set p : Polynomial K := (s2_iter K c0 c1 c2 k) ^ 2 with hp
  set q : Polynomial K := Polynomial.C 7 * s0_iter K c0 c1 c2 k + Polynomial.C (c0 k) with hq
  have hp_monic : p.Monic := h_s2_monic.pow 2
  have hp_deg : p.natDegree = 2 * 8^k := by
    rw [hp, Polynomial.natDegree_pow, h_s2_deg]
  have hq_deg : q.natDegree ≤ 2 * 8^(k-1) := by
    rw [hq]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      exact h_s0_deg
    · exact (Polynomial.natDegree_C _).trans_le (Nat.zero_le _)
  have h_lt : q.natDegree < p.natDegree := by
    rw [hp_deg]
    exact lt_of_le_of_lt hq_deg (two_eight_pow_lt k hk)
  refine ⟨hp_monic.add_of_left ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hp_monic.ne_zero]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h_lt)
  · rw [add_comm p q, Polynomial.natDegree_add_eq_right_of_natDegree_lt h_lt, hp_deg]

/-! ### Inductive step: s1 at general k ≥ 1

`s1_iter (k+1) = 7·s1_iter k + (s0_iter (k+1))² + C (c1 k)`. `(s0_iter (k+1))²`
has natDegree `4 · 8^k`, dominating. -/
theorem s1_iter_succ_monic_natDegree (c0 c1 c2 : Nat → K) (k : Nat) (hk : 1 ≤ k)
    (h_s0_succ_monic : (s0_iter K c0 c1 c2 (k+1)).Monic)
    (h_s0_succ_deg : (s0_iter K c0 c1 c2 (k+1)).natDegree = 2 * 8^k)
    (h_s1_deg : (s1_iter K c0 c1 c2 k).natDegree ≤ 4 * 8^(k-1)) :
    (s1_iter K c0 c1 c2 (k+1)).Monic
      ∧ (s1_iter K c0 c1 c2 (k+1)).natDegree = 4 * 8^k := by
  rw [s1_iter_succ]
  rw [show (Polynomial.C 7 * s1_iter K c0 c1 c2 k + (s0_iter K c0 c1 c2 (k+1)) ^ 2
              + Polynomial.C (c1 k) : Polynomial K)
        = (s0_iter K c0 c1 c2 (k+1)) ^ 2
          + (Polynomial.C 7 * s1_iter K c0 c1 c2 k + Polynomial.C (c1 k)) by ring]
  set p : Polynomial K := (s0_iter K c0 c1 c2 (k+1)) ^ 2 with hp
  set q : Polynomial K := Polynomial.C 7 * s1_iter K c0 c1 c2 k + Polynomial.C (c1 k) with hq
  have hp_monic : p.Monic := h_s0_succ_monic.pow 2
  have hp_deg : p.natDegree = 4 * 8^k := by
    rw [hp, Polynomial.natDegree_pow, h_s0_succ_deg]
    ring
  have hq_deg : q.natDegree ≤ 4 * 8^(k-1) := by
    rw [hq]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      exact h_s1_deg
    · exact (Polynomial.natDegree_C _).trans_le (Nat.zero_le _)
  have h_lt : q.natDegree < p.natDegree := by
    rw [hp_deg]
    exact lt_of_le_of_lt hq_deg (four_eight_pow_lt k hk)
  refine ⟨hp_monic.add_of_left ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hp_monic.ne_zero]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h_lt)
  · rw [add_comm p q, Polynomial.natDegree_add_eq_right_of_natDegree_lt h_lt, hp_deg]

/-! ### Inductive step: s2 at general k ≥ 1

`s2_iter (k+1) = 7·s2_iter k + (s1_iter (k+1))² + C (c2 k)`. `(s1_iter (k+1))²`
has natDegree `8 · 8^k = 8^(k+1)`. -/
theorem s2_iter_succ_monic_natDegree (c0 c1 c2 : Nat → K) (k : Nat) (hk : 1 ≤ k)
    (h_s1_succ_monic : (s1_iter K c0 c1 c2 (k+1)).Monic)
    (h_s1_succ_deg : (s1_iter K c0 c1 c2 (k+1)).natDegree = 4 * 8^k)
    (h_s2_deg : (s2_iter K c0 c1 c2 k).natDegree ≤ 8^k) :
    (s2_iter K c0 c1 c2 (k+1)).Monic
      ∧ (s2_iter K c0 c1 c2 (k+1)).natDegree = 8^(k+1) := by
  rw [s2_iter_succ]
  rw [show (Polynomial.C 7 * s2_iter K c0 c1 c2 k + (s1_iter K c0 c1 c2 (k+1)) ^ 2
              + Polynomial.C (c2 k) : Polynomial K)
        = (s1_iter K c0 c1 c2 (k+1)) ^ 2
          + (Polynomial.C 7 * s2_iter K c0 c1 c2 k + Polynomial.C (c2 k)) by ring]
  set p : Polynomial K := (s1_iter K c0 c1 c2 (k+1)) ^ 2 with hp
  set q : Polynomial K := Polynomial.C 7 * s2_iter K c0 c1 c2 k + Polynomial.C (c2 k) with hq
  have hp_monic : p.Monic := h_s1_succ_monic.pow 2
  have hp_deg : p.natDegree = 8^(k+1) := by
    rw [hp, Polynomial.natDegree_pow, h_s1_succ_deg]
    rw [pow_succ]; ring
  have hq_deg : q.natDegree ≤ 8^k := by
    rw [hq]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      exact h_s2_deg
    · exact (Polynomial.natDegree_C _).trans_le (Nat.zero_le _)
  have h_lt : q.natDegree < p.natDegree := by
    rw [hp_deg]
    refine lt_of_le_of_lt hq_deg ?_
    rw [pow_succ]
    have := eight_pow_pos k
    omega
  refine ⟨hp_monic.add_of_left ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hp_monic.ne_zero]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h_lt)
  · rw [add_comm p q, Polynomial.natDegree_add_eq_right_of_natDegree_lt h_lt, hp_deg]

/-! ### Joint general-n monic + natDegree theorem at t = 3

Mirrors `Mambo.T2GeneralN.s0_s1_iter_monic_natDegree` with the addition of
s2_iter (the third chained cell). The combined statement is proved by
single induction over n with all three monic+natDegree facts in the
inductive hypothesis. -/

theorem s0_s1_s2_iter_monic_natDegree
    (c0 c1 c2 : Nat → K) (n : Nat) (hn : 1 ≤ n) :
    (s0_iter K c0 c1 c2 n).Monic ∧ (s0_iter K c0 c1 c2 n).natDegree = 2 * 8^(n-1) ∧
    (s1_iter K c0 c1 c2 n).Monic ∧ (s1_iter K c0 c1 c2 n).natDegree = 4 * 8^(n-1) ∧
    (s2_iter K c0 c1 c2 n).Monic ∧ (s2_iter K c0 c1 c2 n).natDegree = 8^n := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      refine ⟨s0_iter_one_monic K c0 c1 c2, ?_,
              s1_iter_one_monic K c0 c1 c2, ?_,
              s2_iter_one_monic K c0 c1 c2, ?_⟩
      · rw [s0_iter_one_natDegree]; rfl
      · rw [s1_iter_one_natDegree]; rfl
      · rw [s2_iter_one_natDegree]; rfl
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      obtain ⟨_h_s0_monic, h_s0_deg, _h_s1_monic, h_s1_deg, h_s2_monic, h_s2_deg⟩ := ih hk_pos
      -- s0 inductive step (uses s2_iter k)
      have ⟨h_s0_succ_monic, h_s0_succ_deg⟩ :=
        s0_iter_succ_monic_natDegree K c0 c1 c2 k hk_pos h_s2_monic h_s2_deg h_s0_deg.le
      -- s1 inductive step (uses s0_iter (k+1) and s1_iter k)
      have ⟨h_s1_succ_monic, h_s1_succ_deg⟩ :=
        s1_iter_succ_monic_natDegree K c0 c1 c2 k hk_pos h_s0_succ_monic h_s0_succ_deg h_s1_deg.le
      -- s2 inductive step (uses s1_iter (k+1) and s2_iter k)
      have ⟨h_s2_succ_monic, h_s2_succ_deg⟩ :=
        s2_iter_succ_monic_natDegree K c0 c1 c2 k hk_pos h_s1_succ_monic h_s1_succ_deg h_s2_deg.le
      refine ⟨h_s0_succ_monic, ?_, h_s1_succ_monic, ?_, h_s2_succ_monic, ?_⟩
      · rw [show (k + 1 - 1) = k from rfl]; exact h_s0_succ_deg
      · rw [show (k + 1 - 1) = k from rfl]; exact h_s1_succ_deg
      · exact h_s2_succ_deg

/-! ### U_n_t3 monic + natDegree for general n ≥ 1

`U_n_t3 := s0_iter n - C tau`. Since `natDegree(s0_iter n) = 2·8^(n-1) ≥ 2`
for n ≥ 1, and `C tau` has natDegree 0 < 2, subtracting `C tau` preserves
the leading term. -/

theorem U_n_t3_monic (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    (U_n_t3 K c0 c1 c2 tau n).Monic := by
  unfold U_n_t3
  obtain ⟨h_s0_monic, h_s0_deg, _, _, _, _⟩ := s0_s1_s2_iter_monic_natDegree K c0 c1 c2 n hn
  rw [sub_eq_add_neg]
  have h_neg_deg : (-Polynomial.C tau).natDegree = 0 := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_C]
  have h_lt : (-Polynomial.C tau : Polynomial K).natDegree
                < (s0_iter K c0 c1 c2 n).natDegree := by
    rw [h_neg_deg, h_s0_deg]
    have : 0 < 8^(n-1) := eight_pow_pos (n-1)
    omega
  refine h_s0_monic.add_of_left ?_
  rw [Polynomial.degree_eq_natDegree h_s0_monic.ne_zero]
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h_lt)

/-- `U_n_t3` has natDegree `2 · 8^(n-1)` = `2^(3n-2)` for n ≥ 1. This is
    the polynomial-elimination degree at t = 3, equal to the K-vector-space
    dimension of `R / mamboT3Ideal_n` under the universal-cyclicity assumption
    (which is to be formalised via FGLM/cyclic-module bridge in subsequent
    work). -/
theorem U_n_t3_natDegree (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    (U_n_t3 K c0 c1 c2 tau n).natDegree = 2 * 8^(n-1) := by
  unfold U_n_t3
  obtain ⟨h_s0_monic, h_s0_deg, _, _, _, _⟩ := s0_s1_s2_iter_monic_natDegree K c0 c1 c2 n hn
  rw [sub_eq_add_neg]
  have h_neg_deg : (-Polynomial.C tau).natDegree = 0 := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_C]
  have h_lt : (-Polynomial.C tau : Polynomial K).natDegree
                < (s0_iter K c0 c1 c2 n).natDegree := by
    rw [h_neg_deg, h_s0_deg]
    have : 0 < 8^(n-1) := eight_pow_pos (n-1)
    omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h_lt]
  exact h_s0_deg

/-- `AdjoinRoot(U_n_t3)` has K-finrank `2 · 8^(n-1)` = `2^(3n-2)` for n ≥ 1.
    By `AdjoinRoot.powerBasis'` on the monic `U_n_t3` of natDegree `2·8^(n-1)`. -/
theorem U_n_t3_AdjoinRoot_finrank (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    Module.finrank K (AdjoinRoot (U_n_t3 K c0 c1 c2 tau n)) = 2 * 8^(n-1) := by
  have h_monic := U_n_t3_monic K c0 c1 c2 tau n hn
  have h_deg := U_n_t3_natDegree K c0 c1 c2 tau n hn
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis' h_monic),
      AdjoinRoot.powerBasis'_dim, h_deg]

/-! ### Closed-form dim relation: 2 · 8^(n-1) = 2^(3n-2) at n ≥ 1

The closed form for the AdjoinRoot finrank matches the t=3 d_reg = 3n-1
result via dim = 2^(d_reg - 1) = 2^(3n-2). -/

theorem two_eight_pow_eq_two_pow (n : Nat) (hn : 1 ≤ n) :
    2 * 8^(n-1) = 2 ^ (3 * n - 2) := by
  -- 2·8^(n-1) = 2·(2^3)^(n-1) = 2 · 2^(3(n-1)) = 2^(1 + 3(n-1)) = 2^(3n-2)
  have h_eight : (8 : Nat) = 2^3 := by decide
  rw [h_eight, ← Nat.pow_mul]
  rw [show (2 : Nat) * 2 ^ (3 * (n - 1)) = 2 ^ 1 * 2 ^ (3 * (n - 1)) from by ring]
  rw [← Nat.pow_add]
  congr 1
  omega

/-- **Closed-form K-finrank of AdjoinRoot(U_n_t3) for general n**:
    `2^(3n-2)`. Matches the empirical result + paper d_reg = 3n-1 at t=3. -/
theorem U_n_t3_AdjoinRoot_finrank_closed (c0 c1 c2 : Nat → K) (tau : K)
    (n : Nat) (hn : 1 ≤ n) :
    Module.finrank K (AdjoinRoot (U_n_t3 K c0 c1 c2 tau n)) = 2 ^ (3 * n - 2) := by
  rw [U_n_t3_AdjoinRoot_finrank K c0 c1 c2 tau n hn]
  exact two_eight_pow_eq_two_pow n hn

/-! ### General-n eval map: MvPoly(VarIndex 3 n) → AdjoinRoot(U_n_t3) -/

open Mambo.T3CicoIdeal Mambo.B2Enumeration

/-- Variable image map at t = 3, general n: send each Mambo variable
    `s_{c, r}` to its iterator polynomial image at the AdjoinRoot generator.
    Three branches on `c ∈ Fin 3`. -/
noncomputable def t3_general_var_image (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    VarIndex 3 n → AdjoinRoot (U_n_t3 K c0 c1 c2 tau n) :=
  fun v =>
    if v.1.val = 0 then
      Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
        (s0_iter K c0 c1 c2 v.2.val)
    else if v.1.val = 1 then
      Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
        (s1_iter K c0 c1 c2 v.2.val)
    else
      Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
        (s2_iter K c0 c1 c2 v.2.val)

/-- The general-n eval map at t = 3: MvPoly(VarIndex 3 n) → AdjoinRoot(U_n_t3). -/
noncomputable def t3_general_eval (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    MvPolynomial (VarIndex 3 n) K →ₐ[K] AdjoinRoot (U_n_t3 K c0 c1 c2 tau n) :=
  MvPolynomial.aeval (t3_general_var_image K c0 c1 c2 tau n)

/-! ### Polynomial identities for round-constraint kills

For each cell c ∈ {0, 1, 2}, the iterator `s_c_iter (r+1)` satisfies a
polynomial identity that, when applied to the AdjoinRoot generator,
makes the corresponding round constraint evaluate to zero. -/

theorem t3_s0_iter_succ_identity (c0 c1 c2 : Nat → K) (r : Nat) :
    (s0_iter K c0 c1 c2 (r + 1) - Polynomial.C 7 * s0_iter K c0 c1 c2 r
      - (s2_iter K c0 c1 c2 r) ^ 2 - Polynomial.C (c0 r) : Polynomial K) = 0 := by
  rw [s0_iter_succ]
  ring

theorem t3_s1_iter_succ_identity (c0 c1 c2 : Nat → K) (r : Nat) :
    (s1_iter K c0 c1 c2 (r + 1) - Polynomial.C 7 * s1_iter K c0 c1 c2 r
      - (s0_iter K c0 c1 c2 (r + 1)) ^ 2 - Polynomial.C (c1 r) : Polynomial K) = 0 := by
  rw [s1_iter_succ]
  ring

theorem t3_s2_iter_succ_identity (c0 c1 c2 : Nat → K) (r : Nat) :
    (s2_iter K c0 c1 c2 (r + 1) - Polynomial.C 7 * s2_iter K c0 c1 c2 r
      - (s1_iter K c0 c1 c2 (r + 1)) ^ 2 - Polynomial.C (c2 r) : Polynomial K) = 0 := by
  rw [s2_iter_succ]
  ring

/-! ### Boundary kills -/

/-- The boundary constraint `s_{0, 0} = 0` is killed by the eval map. -/
theorem t3_general_eval_boundaryStart (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    t3_general_eval K c0 c1 c2 tau n (Mambo.T3CicoIdeal.boundaryStart K n) = 0 := by
  unfold t3_general_eval Mambo.T3CicoIdeal.boundaryStart Mambo.T3CicoIdeal.sVar
  rw [MvPolynomial.aeval_X]
  unfold t3_general_var_image
  -- The variable is X (0, ⟨0, _⟩); first component val=0 → s0 branch.
  show (if ((0 : Fin 3).val = 0) then
          (Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n)))
            (s0_iter K c0 c1 c2 (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)).val)
        else _) = 0
  rw [if_pos (by decide : (0 : Fin 3).val = 0)]
  show (Polynomial.aeval (AdjoinRoot.root _)) (s0_iter K c0 c1 c2 0) = 0
  rw [s0_iter_zero, map_zero]

/-- The boundary constraint `s_{0, n} = τ` is killed by the eval map. -/
theorem t3_general_eval_boundaryEnd (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    t3_general_eval K c0 c1 c2 tau n (Mambo.T3CicoIdeal.boundaryEnd K n tau) = 0 := by
  unfold t3_general_eval Mambo.T3CicoIdeal.boundaryEnd Mambo.T3CicoIdeal.sVar
  rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t3_general_var_image
  -- The X (0, ⟨n, _⟩) variable lands in s0 branch (first component val = 0).
  rw [if_pos (by decide : (0 : Fin 3).val = 0)]
  -- Goal: aeval root (s0_iter ⟨n,_⟩.val) - algebraMap K _ tau = 0
  --   i.e. aeval root (s0_iter n) - algebraMap K _ tau = 0
  -- This equals aeval root (U_n_t3) = mk U_n_t3 U_n_t3 = 0
  show Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
          (s0_iter K c0 c1 c2 n)
        - algebraMap K _ tau = 0
  rw [show (Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n)))
              (s0_iter K c0 c1 c2 n)
            - algebraMap K _ tau
          = Polynomial.aeval (AdjoinRoot.root _) (U_n_t3 K c0 c1 c2 tau n) by
        unfold U_n_t3
        rw [map_sub, Polynomial.aeval_C]]
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-! ### Helpers: Fin 3 valuation lemmas -/

private theorem fin3_zero_val : ((0 : Fin 3).val = 0) := by decide
private theorem fin3_one_val : ((1 : Fin 3).val = 1) := by decide
private theorem fin3_two_val : ((2 : Fin 3).val = 2) := by decide
private theorem fin3_one_ne_zero : ((1 : Fin 3).val = 0) = False := by
  simp [fin3_one_val]
private theorem fin3_two_ne_zero : ((2 : Fin 3).val = 0) = False := by
  simp [fin3_two_val]
private theorem fin3_two_ne_one : ((2 : Fin 3).val = 1) = False := by
  simp [fin3_two_val]

/-- Cell 0 round constraint killed by the eval map. -/
theorem t3_general_eval_roundConstraint0 (c0 c1 c2 : Nat → K) (tau : K) (n : Nat)
    (r : Fin n) :
    t3_general_eval K c0 c1 c2 tau n
      (Mambo.T3CicoIdeal.roundConstraint0 K n r (c0 r.val)) = 0 := by
  unfold t3_general_eval Mambo.T3CicoIdeal.roundConstraint0 Mambo.T3CicoIdeal.sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t3_general_var_image
  -- Variables: (0, r.succ), (0, r.castSucc), (2, r.castSucc). All first-component val ∈ {0,2}.
  simp only [fin3_zero_val, fin3_two_ne_zero, fin3_two_ne_one,
             if_true, if_false]
  -- Goal: aeval root (s0_iter (r+1)) - phi • aeval root (s0_iter r)
  --        - aeval root (s2_iter r) * aeval root (s2_iter r)
  --        - algebraMap K _ (c0 r.val) = 0
  have h_id := t3_s0_iter_succ_identity K c0 c1 c2 r.val
  have h_aeval : Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
                  (s0_iter K c0 c1 c2 (r.val + 1)
                    - Polynomial.C 7 * s0_iter K c0 c1 c2 r.val
                    - (s2_iter K c0 c1 c2 r.val) ^ 2
                    - Polynomial.C (c0 r.val)) = 0 := by
    rw [h_id]; exact map_zero _
  rw [map_sub, map_sub, map_sub, map_mul, Polynomial.aeval_C,
      map_pow, Polynomial.aeval_C] at h_aeval
  -- h_aeval now has: ... - algebraMap K _ 7 * ... - ()² - algebraMap K _ (c0 r.val) = 0
  -- Goal: ... - phi • ... - _ * _ - algebraMap _ _ (c0 r.val) = 0
  -- Need to bridge phi vs C 7 via Algebra.smul_def, and a² vs a*a via pow_two.
  show Polynomial.aeval (AdjoinRoot.root _)
          (s0_iter K c0 c1 c2 (Fin.val r.succ))
        - (Mambo.T3CicoIdeal.phi : K) • _
        - _ * _
        - algebraMap K _ (c0 r.val) = 0
  rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl, Algebra.smul_def,
      ← pow_two]
  -- Fin.val r.succ = r.val + 1 ; Fin.val r.castSucc = r.val
  show Polynomial.aeval (AdjoinRoot.root _)
          (s0_iter K c0 c1 c2 (r.val + 1))
        - algebraMap K _ 7
            * Polynomial.aeval (AdjoinRoot.root _)
                (s0_iter K c0 c1 c2 r.val)
        - (Polynomial.aeval (AdjoinRoot.root _)
                (s2_iter K c0 c1 c2 r.val)) ^ 2
        - algebraMap K _ (c0 r.val) = 0
  linear_combination h_aeval

/-- Cell 1 round constraint killed by the eval map. -/
theorem t3_general_eval_roundConstraint1 (c0 c1 c2 : Nat → K) (tau : K) (n : Nat)
    (r : Fin n) :
    t3_general_eval K c0 c1 c2 tau n
      (Mambo.T3CicoIdeal.roundConstraint1 K n r (c1 r.val)) = 0 := by
  unfold t3_general_eval Mambo.T3CicoIdeal.roundConstraint1 Mambo.T3CicoIdeal.sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t3_general_var_image
  -- Variables: (1, r.succ), (1, r.castSucc), (0, r.succ).
  simp only [fin3_zero_val, fin3_one_ne_zero, fin3_one_val,
             if_true, if_false]
  have h_id := t3_s1_iter_succ_identity K c0 c1 c2 r.val
  have h_aeval : Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
                  (s1_iter K c0 c1 c2 (r.val + 1)
                    - Polynomial.C 7 * s1_iter K c0 c1 c2 r.val
                    - (s0_iter K c0 c1 c2 (r.val + 1)) ^ 2
                    - Polynomial.C (c1 r.val)) = 0 := by
    rw [h_id]; exact map_zero _
  rw [map_sub, map_sub, map_sub, map_mul, Polynomial.aeval_C,
      map_pow, Polynomial.aeval_C] at h_aeval
  show Polynomial.aeval (AdjoinRoot.root _)
          (s1_iter K c0 c1 c2 (Fin.val r.succ))
        - (Mambo.T3CicoIdeal.phi : K) • _
        - _ * _
        - algebraMap K _ (c1 r.val) = 0
  rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl, Algebra.smul_def,
      ← pow_two]
  show Polynomial.aeval (AdjoinRoot.root _)
          (s1_iter K c0 c1 c2 (r.val + 1))
        - algebraMap K _ 7
            * Polynomial.aeval (AdjoinRoot.root _)
                (s1_iter K c0 c1 c2 r.val)
        - (Polynomial.aeval (AdjoinRoot.root _)
                (s0_iter K c0 c1 c2 (r.val + 1))) ^ 2
        - algebraMap K _ (c1 r.val) = 0
  linear_combination h_aeval

/-- Cell 2 round constraint killed by the eval map. -/
theorem t3_general_eval_roundConstraint2 (c0 c1 c2 : Nat → K) (tau : K) (n : Nat)
    (r : Fin n) :
    t3_general_eval K c0 c1 c2 tau n
      (Mambo.T3CicoIdeal.roundConstraint2 K n r (c2 r.val)) = 0 := by
  unfold t3_general_eval Mambo.T3CicoIdeal.roundConstraint2 Mambo.T3CicoIdeal.sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t3_general_var_image
  -- Variables: (2, r.succ), (2, r.castSucc), (1, r.succ).
  simp only [fin3_two_ne_zero, fin3_two_ne_one, fin3_one_ne_zero, fin3_one_val,
             if_true, if_false]
  have h_id := t3_s2_iter_succ_identity K c0 c1 c2 r.val
  have h_aeval : Polynomial.aeval (AdjoinRoot.root (U_n_t3 K c0 c1 c2 tau n))
                  (s2_iter K c0 c1 c2 (r.val + 1)
                    - Polynomial.C 7 * s2_iter K c0 c1 c2 r.val
                    - (s1_iter K c0 c1 c2 (r.val + 1)) ^ 2
                    - Polynomial.C (c2 r.val)) = 0 := by
    rw [h_id]; exact map_zero _
  rw [map_sub, map_sub, map_sub, map_mul, Polynomial.aeval_C,
      map_pow, Polynomial.aeval_C] at h_aeval
  show Polynomial.aeval (AdjoinRoot.root _)
          (s2_iter K c0 c1 c2 (Fin.val r.succ))
        - (Mambo.T3CicoIdeal.phi : K) • _
        - _ * _
        - algebraMap K _ (c2 r.val) = 0
  rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl, Algebra.smul_def,
      ← pow_two]
  show Polynomial.aeval (AdjoinRoot.root _)
          (s2_iter K c0 c1 c2 (r.val + 1))
        - algebraMap K _ 7
            * Polynomial.aeval (AdjoinRoot.root _)
                (s2_iter K c0 c1 c2 r.val)
        - (Polynomial.aeval (AdjoinRoot.root _)
                (s1_iter K c0 c1 c2 (r.val + 1))) ^ 2
        - algebraMap K _ (c2 r.val) = 0
  linear_combination h_aeval

/-- **The full mamboT3Ideal at general n is killed by the eval map.** -/
theorem t3_general_eval_kills_ideal (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    Mambo.T3CicoIdeal.mamboT3Ideal K n (fun r => c0 r.val)
        (fun r => c1 r.val) (fun r => c2 r.val) tau
      ≤ RingHom.ker (t3_general_eval K c0 c1 c2 tau n).toRingHom := by
  unfold Mambo.T3CicoIdeal.mamboT3Ideal
  rw [Ideal.span_le]
  rintro p (((⟨r, rfl⟩ | ⟨r, rfl⟩) | ⟨r, rfl⟩) | (rfl | rfl))
  · exact t3_general_eval_roundConstraint0 K c0 c1 c2 tau n r
  · exact t3_general_eval_roundConstraint1 K c0 c1 c2 tau n r
  · exact t3_general_eval_roundConstraint2 K c0 c1 c2 tau n r
  · exact t3_general_eval_boundaryStart K c0 c1 c2 tau n
  · exact t3_general_eval_boundaryEnd K c0 c1 c2 tau n

/-! ### Factored quotient map (push 3) -/

/-- IsTwoSided instance for mamboT3Ideal at general n (needed for liftₐ). -/
instance (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (Mambo.T3CicoIdeal.mamboT3Ideal K n (fun r => c0 r.val)
        (fun r => c1 r.val) (fun r => c2 r.val) tau).IsTwoSided :=
  inferInstance

/-- **Factored general-n eval map** as an AlgHom on the quotient.

    Direct corollary of `t3_general_eval_kills_ideal`: the eval map
    factors through the quotient `MvPoly / mamboT3Ideal`. -/
noncomputable def t3_general_eval_bar (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (MvPolynomial (VarIndex 3 n) K ⧸
        Mambo.T3CicoIdeal.mamboT3Ideal K n
          (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau) →ₐ[K]
    AdjoinRoot (U_n_t3 K c0 c1 c2 tau n) :=
  Ideal.Quotient.liftₐ _ (t3_general_eval K c0 c1 c2 tau n)
    (fun a ha => t3_general_eval_kills_ideal K c0 c1 c2 tau n ha)

/-- The eval_bar map sends the class of `s_{0, 0}` to 0 (boundary). -/
theorem t3_general_eval_bar_boundaryStart_var
    (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    t3_general_eval_bar K c0 c1 c2 tau n
      (Ideal.Quotient.mk _
        (MvPolynomial.X ((0 : Fin 3),
          (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))))) = 0 := by
  -- The class of `X (0, ⟨0, _⟩)` is exactly `boundaryStart`, which the eval map kills.
  unfold t3_general_eval_bar
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  -- The reduced goal: t3_general_eval ... (X (0, ⟨0,_⟩)) = 0
  -- = boundaryStart applied to t3_general_eval
  have : MvPolynomial.X ((0 : Fin 3), (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)))
         = Mambo.T3CicoIdeal.boundaryStart K n := by
    unfold Mambo.T3CicoIdeal.boundaryStart Mambo.T3CicoIdeal.sVar
    rfl
  rw [this]
  exact t3_general_eval_boundaryStart K c0 c1 c2 tau n

end Mambo.T3GeneralN
