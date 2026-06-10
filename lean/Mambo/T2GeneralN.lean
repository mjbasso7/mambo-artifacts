import Mambo.T2CicoIdeal

/-!
# Mambo t = 2 Generic-n Eliminating Polynomial

For the t = 2 Mambo CICO ideal at depth n, the elimination procedure
(substituting boundaries + all round constraints) reduces to a single
univariate polynomial U_n(X) in `X := s_{1,0}`, of degree
`d_θ(n) = 2·4^{n-1} = 2^{2n-1}`. The quotient ring is K-algebra-isomorphic
to `AdjoinRoot (U_n)`, with K-finrank `2^{2n-1}` — matching paper
Thm `thm:hilb_closed` for all n ≥ 1.

This file defines the symbolic iterators `s0_iter`, `s1_iter` that
compute these expressions recursively, and defines the eliminating
polynomial `U_n`. The dim theorem (paper Thm hilb_closed full generality)
is then assembled from these polynomial-level definitions plus the
AlgEquiv template established at n = 1 in `T2CicoIdeal.lean`.
-/

namespace Mambo.T2GeneralN

open Mambo.T2CicoIdeal MvPolynomial

variable (K : Type*) [Field K]

mutual
/-- Symbolic iterator for `s_{0,r}` as a polynomial in `X = s_{1,0}`.
    `s0_iter 0 = 0` (boundary start). `s0_iter (r+1) = 7·s0_iter r +
    (s1_iter r)² + c_r`. -/
noncomputable def s0_iter (c_seq d_seq : Nat → K) : Nat → Polynomial K
  | 0     => 0
  | r + 1 =>
      (Polynomial.C 7) * s0_iter c_seq d_seq r
        + (s1_iter c_seq d_seq r) ^ 2
        + Polynomial.C (c_seq r)

/-- Symbolic iterator for `s_{1,r}`. `s1_iter 0 = X` (the unique free var).
    `s1_iter (r+1) = 7·s1_iter r + (s0_iter (r+1))² + d_r`. -/
noncomputable def s1_iter (c_seq d_seq : Nat → K) : Nat → Polynomial K
  | 0     => Polynomial.X
  | r + 1 =>
      (Polynomial.C 7) * s1_iter c_seq d_seq r
        + (s0_iter c_seq d_seq (r + 1)) ^ 2
        + Polynomial.C (d_seq r)
end

/-- The eliminating polynomial at depth n: `U_n(X) := s_{0,n}(X) − τ`.
    For n = 0 this is `−τ` (degree 0, degenerate). For n ≥ 1 it has
    degree `2·4^{n-1}`. -/
noncomputable def U_n (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    Polynomial K :=
  s0_iter K c_seq d_seq n - Polynomial.C tau

/-! ### Base-case reduction lemmas -/

theorem s0_iter_zero (c d : Nat → K) :
    s0_iter K c d 0 = 0 := by
  simp only [s0_iter]

theorem s1_iter_zero (c d : Nat → K) :
    s1_iter K c d 0 = Polynomial.X := by
  simp only [s1_iter]

theorem s0_iter_succ (c d : Nat → K) (r : Nat) :
    s0_iter K c d (r + 1)
      = Polynomial.C 7 * s0_iter K c d r + (s1_iter K c d r) ^ 2
        + Polynomial.C (c r) := by
  simp only [s0_iter]

theorem s1_iter_succ (c d : Nat → K) (r : Nat) :
    s1_iter K c d (r + 1)
      = Polynomial.C 7 * s1_iter K c d r + (s0_iter K c d (r + 1)) ^ 2
        + Polynomial.C (d r) := by
  simp only [s1_iter]

/-- Sanity: at n = 1, U_1 = X² + c_0 − τ. -/
example (c d : Nat → K) (tau : K) :
    U_n K c d tau 1 = Polynomial.X ^ 2 + Polynomial.C (c 0) - Polynomial.C tau := by
  unfold U_n
  rw [s0_iter_succ, s1_iter_zero, s0_iter_zero]
  ring

/-- **Degree of U_n at n = 1: 2.** -/
theorem U_n_natDegree_one (c d : Nat → K) (tau : K) :
    (U_n K c d tau 1).natDegree = 2 := by
  unfold U_n
  rw [s0_iter_succ, s1_iter_zero, s0_iter_zero]
  -- Goal: natDegree (C 7 * 0 + X^2 + C (c 0) - C tau) = 2
  rw [show (Polynomial.C 7 * (0 : Polynomial K) + Polynomial.X ^ 2 + Polynomial.C (c 0)
              - Polynomial.C tau)
        = Polynomial.X ^ 2 - Polynomial.C (tau - c 0) by
        rw [Polynomial.C_sub]; ring]
  exact t2_n1_defining_poly_natDegree K (c 0) tau

/-- **U_n at n = 1 is monic.** -/
theorem U_n_monic_one (c d : Nat → K) (tau : K) :
    (U_n K c d tau 1).Monic := by
  unfold U_n
  rw [s0_iter_succ, s1_iter_zero, s0_iter_zero]
  rw [show (Polynomial.C 7 * (0 : Polynomial K) + Polynomial.X ^ 2 + Polynomial.C (c 0)
              - Polynomial.C tau)
        = Polynomial.X ^ 2 - Polynomial.C (tau - c 0) by
        rw [Polynomial.C_sub]; ring]
  exact t2_n1_defining_poly_monic K (c 0) tau

/-! ### Joint monic + natDegree induction for general n ≥ 1

The s0/s1 iterators jointly satisfy: at each step both are monic, and
their degrees follow the d_θ/d_ψ recurrence (paper Thm `thm:degree`):

  natDegree (s0_iter n) = 2·4^{n-1}   for n ≥ 1
  natDegree (s1_iter n) = 4^n         for n ≥ 0

By induction on n. Foundation: squared monic polynomials are monic and
double in degree. Adding lower-degree summands preserves the leading
term. -/

/-- Base case n = 1, s0 part: monic with natDegree 2. -/
theorem s0_iter_one_monic (c d : Nat → K) : (s0_iter K c d 1).Monic := by
  rw [s0_iter_succ, s1_iter_zero, s0_iter_zero]
  show (Polynomial.C 7 * (0 : Polynomial K) + Polynomial.X ^ 2 + Polynomial.C (c 0)).Monic
  rw [show (Polynomial.C 7 * (0 : Polynomial K) + Polynomial.X ^ 2 + Polynomial.C (c 0))
        = Polynomial.X ^ 2 + Polynomial.C (c 0) by ring]
  exact Polynomial.monic_X_pow_add_C (c 0) (by decide)

theorem s0_iter_one_natDegree (c d : Nat → K) : (s0_iter K c d 1).natDegree = 2 := by
  rw [s0_iter_succ, s1_iter_zero, s0_iter_zero]
  show (Polynomial.C 7 * (0 : Polynomial K) + Polynomial.X ^ 2 + Polynomial.C (c 0)).natDegree = 2
  rw [show (Polynomial.C 7 * (0 : Polynomial K) + Polynomial.X ^ 2 + Polynomial.C (c 0))
        = Polynomial.X ^ 2 + Polynomial.C (c 0) by ring]
  rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]

-- s1_iter at n=1 has degree 4 (from (X² + c_0)² leading X^4). Joint monic+natDegree
-- induction for s1 + general n deferred to next push.

/-- s1_iter 1 reduces explicitly to `7X + (X² + C c_0)² + C d_0`. -/
theorem s1_iter_one_expand (c d : Nat → K) :
    s1_iter K c d 1 = Polynomial.C 7 * Polynomial.X
                    + (Polynomial.X ^ 2 + Polynomial.C (c 0)) ^ 2
                    + Polynomial.C (d 0) := by
  rw [s1_iter_succ, s1_iter_zero]
  rw [show s0_iter K c d 1 = Polynomial.X ^ 2 + Polynomial.C (c 0) by
        rw [s0_iter_succ, s1_iter_zero, s0_iter_zero]; ring]

/-- s1_iter 1 is monic via the `monicity!` automated tactic. -/
theorem s1_iter_one_monic (c d : Nat → K) : (s1_iter K c d 1).Monic := by
  rw [s1_iter_one_expand]
  monicity!

/-- s1_iter 1 has natDegree 4 via the `compute_degree!` automated tactic. -/
theorem s1_iter_one_natDegree (c d : Nat → K) : (s1_iter K c d 1).natDegree = 4 := by
  rw [s1_iter_one_expand]
  compute_degree!

/-! ### Inductive: 4^k > 4^(k-1) inequalities -/

private theorem four_pow_strict (k : Nat) (hk : 1 ≤ k) : 4^(k-1) < 4^k := by
  have : k - 1 < k := Nat.sub_lt hk (by decide)
  exact Nat.pow_lt_pow_right (by decide : 1 < 4) this

private theorem two_four_pow_lt (k : Nat) (hk : 1 ≤ k) : 2 * 4^(k-1) < 2 * 4^k := by
  have := four_pow_strict k hk
  omega

private theorem four_pow_pos (k : Nat) : 0 < (4 : Nat)^k := by positivity

/-- **Inductive step for s0 at general k ≥ 1.**
    Given s1_iter k is monic with natDegree 4^k and a degree bound on
    s0_iter k, then s0_iter (k+1) is monic with natDegree 2·4^k. -/
theorem s0_iter_succ_monic_natDegree (c d : Nat → K) (k : Nat) (hk : 1 ≤ k)
    (h_s1_monic : (s1_iter K c d k).Monic)
    (h_s1_deg : (s1_iter K c d k).natDegree = 4^k)
    (h_s0_deg : (s0_iter K c d k).natDegree ≤ 2 * 4^(k-1)) :
    (s0_iter K c d (k+1)).Monic ∧ (s0_iter K c d (k+1)).natDegree = 2 * 4^k := by
  rw [s0_iter_succ]
  rw [show (Polynomial.C 7 * s0_iter K c d k + (s1_iter K c d k) ^ 2 + Polynomial.C (c k)
              : Polynomial K)
        = (s1_iter K c d k) ^ 2 + (Polynomial.C 7 * s0_iter K c d k + Polynomial.C (c k)) by
        ring]
  set p : Polynomial K := (s1_iter K c d k) ^ 2 with hp
  set q : Polynomial K := Polynomial.C 7 * s0_iter K c d k + Polynomial.C (c k) with hq
  have hp_monic : p.Monic := h_s1_monic.pow 2
  have hp_deg : p.natDegree = 2 * 4^k := by
    rw [hp, Polynomial.natDegree_pow, h_s1_deg]
  have hq_deg : q.natDegree ≤ 2 * 4^(k-1) := by
    rw [hq]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      exact h_s0_deg
    · exact (Polynomial.natDegree_C _).trans_le (Nat.zero_le _)
  have h_lt : q.natDegree < p.natDegree := by
    rw [hp_deg]
    exact lt_of_le_of_lt hq_deg (two_four_pow_lt k hk)
  refine ⟨hp_monic.add_of_left ?_, ?_⟩
  · -- degree q < degree p
    rw [Polynomial.degree_eq_natDegree hp_monic.ne_zero]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h_lt)
  · rw [add_comm p q, Polynomial.natDegree_add_eq_right_of_natDegree_lt h_lt, hp_deg]

/-- **Inductive step for s1 at general k ≥ 1.**
    Given s0_iter (k+1) monic with natDegree 2·4^k (from s0 inductive step)
    and a degree bound on s1_iter k, then s1_iter (k+1) is monic with
    natDegree 4^(k+1). -/
theorem s1_iter_succ_monic_natDegree (c d : Nat → K) (k : Nat) (hk : 1 ≤ k)
    (h_s0_succ_monic : (s0_iter K c d (k+1)).Monic)
    (h_s0_succ_deg : (s0_iter K c d (k+1)).natDegree = 2 * 4^k)
    (h_s1_deg : (s1_iter K c d k).natDegree ≤ 4^k) :
    (s1_iter K c d (k+1)).Monic ∧ (s1_iter K c d (k+1)).natDegree = 4^(k+1) := by
  rw [s1_iter_succ]
  rw [show (Polynomial.C 7 * s1_iter K c d k + (s0_iter K c d (k+1)) ^ 2 + Polynomial.C (d k)
              : Polynomial K)
        = (s0_iter K c d (k+1)) ^ 2 + (Polynomial.C 7 * s1_iter K c d k + Polynomial.C (d k)) by
        ring]
  set p : Polynomial K := (s0_iter K c d (k+1)) ^ 2 with hp
  set q : Polynomial K := Polynomial.C 7 * s1_iter K c d k + Polynomial.C (d k) with hq
  have hp_monic : p.Monic := h_s0_succ_monic.pow 2
  have hp_deg : p.natDegree = 4^(k+1) := by
    rw [hp, Polynomial.natDegree_pow, h_s0_succ_deg]
    rw [pow_succ]; ring
  have hq_deg : q.natDegree ≤ 4^k := by
    rw [hq]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    refine max_le ?_ ?_
    · refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C, Nat.zero_add]
      exact h_s1_deg
    · exact (Polynomial.natDegree_C _).trans_le (Nat.zero_le _)
  have h_lt : q.natDegree < p.natDegree := by
    rw [hp_deg]
    refine lt_of_le_of_lt hq_deg ?_
    rw [pow_succ]
    have := four_pow_pos k
    omega
  refine ⟨hp_monic.add_of_left ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hp_monic.ne_zero]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h_lt)
  · rw [add_comm p q, Polynomial.natDegree_add_eq_right_of_natDegree_lt h_lt, hp_deg]

/-- **Joint general-n monic + natDegree theorem** (paper Lem `lem:recurrence`
    + Thm `thm:degree` for the Mambo iterators). For every n ≥ 1:
    `s0_iter n` is monic with natDegree `2·4^{n-1}`, and `s1_iter n` is
    monic with natDegree `4^n`. -/
theorem s0_s1_iter_monic_natDegree (c d : Nat → K) (n : Nat) (hn : 1 ≤ n) :
    (s0_iter K c d n).Monic ∧ (s0_iter K c d n).natDegree = 2 * 4^(n-1) ∧
    (s1_iter K c d n).Monic ∧ (s1_iter K c d n).natDegree = 4^n := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      refine ⟨s0_iter_one_monic K c d, ?_, s1_iter_one_monic K c d, ?_⟩
      · rw [s0_iter_one_natDegree]; rfl
      · rw [s1_iter_one_natDegree]; rfl
    · have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      obtain ⟨_h_s0_monic, h_s0_deg, h_s1_monic, h_s1_deg⟩ := ih hk_pos
      -- s0 inductive step
      have ⟨h_s0_succ_monic, h_s0_succ_deg⟩ :=
        s0_iter_succ_monic_natDegree K c d k hk_pos h_s1_monic h_s1_deg h_s0_deg.le
      -- s1 inductive step
      have ⟨h_s1_succ_monic, h_s1_succ_deg⟩ :=
        s1_iter_succ_monic_natDegree K c d k hk_pos h_s0_succ_monic h_s0_succ_deg h_s1_deg.le
      refine ⟨h_s0_succ_monic, ?_, h_s1_succ_monic, h_s1_succ_deg⟩
      rw [show (k + 1 - 1) = k from rfl]
      exact h_s0_succ_deg

/-! ### U_n monic + natDegree for general n ≥ 1 (paper Thm hilb_closed degree part) -/

/-- **U_n is monic for n ≥ 1.** Subtracting `C tau` doesn't disturb the
    leading term of `s0_iter n` (degree 2·4^(n−1) ≥ 2). -/
theorem U_n_monic (c d : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    (U_n K c d tau n).Monic := by
  unfold U_n
  rw [sub_eq_add_neg]
  -- s0_iter n + (-C tau)
  have ⟨h_s0_monic, h_s0_deg, _, _⟩ := s0_s1_iter_monic_natDegree K c d n hn
  apply h_s0_monic.add_of_left
  -- degree (-C tau) < degree (s0_iter n)
  have h_neg_deg : (-Polynomial.C tau).natDegree = 0 := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_C]
  have h_s0_pos : 0 < 2 * 4^(n-1) := by
    have := four_pow_pos (n-1)
    omega
  rw [Polynomial.degree_eq_natDegree h_s0_monic.ne_zero]
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  rw [h_neg_deg, h_s0_deg]
  exact_mod_cast h_s0_pos

/-- **U_n natDegree for n ≥ 1**: `2·4^{n-1} = 2^{2n-1}`. Equals
    `Mambo.DegreeGrowth.dTheta n` (the paper's d_θ closed form). -/
theorem U_n_natDegree (c d : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    (U_n K c d tau n).natDegree = 2 * 4^(n-1) := by
  unfold U_n
  rw [sub_eq_add_neg]
  have ⟨h_s0_monic, h_s0_deg, _, _⟩ := s0_s1_iter_monic_natDegree K c d n hn
  have h_neg_deg : (-Polynomial.C tau).natDegree = 0 := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_C]
  have h_lt : (-Polynomial.C tau : Polynomial K).natDegree
                < (s0_iter K c d n).natDegree := by
    rw [h_neg_deg, h_s0_deg]
    have := four_pow_pos (n-1)
    omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h_lt]
  exact h_s0_deg

/-- **AdjoinRoot(U_n) has K-finrank `2·4^{n-1}` for all n ≥ 1.**
    By `AdjoinRoot.powerBasis'` on the monic U_n of natDegree 2·4^(n-1). -/
theorem U_n_AdjoinRoot_finrank (c d : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    Module.finrank K (AdjoinRoot (U_n K c d tau n)) = 2 * 4^(n-1) := by
  have h_monic := U_n_monic K c d tau n hn
  have h_deg := U_n_natDegree K c d tau n hn
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis' h_monic),
      AdjoinRoot.powerBasis'_dim, h_deg]

/-! ### General-n eval map: MvPoly(VarIndex 2 n) → AdjoinRoot(U_n) -/

open Mambo.T2CicoIdeal Mambo.B2Enumeration

/-- Variable image map at general n: send each Mambo variable to its
    post-elimination image (`s_c_iter r` applied at the AdjoinRoot generator). -/
noncomputable def t2_general_var_image (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    VarIndex 2 n → AdjoinRoot (U_n K c_seq d_seq tau n) :=
  fun v =>
    if v.1 = 0 then
      Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n))
        (s0_iter K c_seq d_seq v.2.val)
    else
      Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n))
        (s1_iter K c_seq d_seq v.2.val)

/-- The general-n eval map MvPoly(VarIndex 2 n) → AdjoinRoot(U_n). -/
noncomputable def t2_general_eval (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    MvPolynomial (VarIndex 2 n) K →ₐ[K] AdjoinRoot (U_n K c_seq d_seq tau n) :=
  MvPolynomial.aeval (t2_general_var_image K c_seq d_seq tau n)

/-- **boundaryStart is killed by the general-n eval map.** -/
theorem t2_general_eval_boundaryStart (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    t2_general_eval K c_seq d_seq tau n
      (Mambo.T2CicoIdeal.boundaryStart K n) = 0 := by
  unfold t2_general_eval Mambo.T2CicoIdeal.boundaryStart Mambo.T2CicoIdeal.sVar
  rw [MvPolynomial.aeval_X]
  unfold t2_general_var_image
  -- The X (0, 0) variable: first component is 0 so the s0 branch fires
  simp only [s0_iter_zero, map_zero, if_true]

/-- **boundaryEnd is killed by the general-n eval map.** Follows from
    `aeval root (s0_iter n) - algebraMap K _ tau = aeval root (U_n) = 0`. -/
theorem t2_general_eval_boundaryEnd (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    t2_general_eval K c_seq d_seq tau n
      (Mambo.T2CicoIdeal.boundaryEnd K n tau) = 0 := by
  unfold t2_general_eval Mambo.T2CicoIdeal.boundaryEnd Mambo.T2CicoIdeal.sVar
  rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t2_general_var_image
  -- The X (0, n) variable lands in s0 branch (first component = 0).
  simp only [if_true]
  -- Goal: aeval root (s0_iter n) - algebraMap K _ tau = 0
  -- This equals aeval root (s0_iter n - C tau) = aeval root (U_n) = mk U_n U_n = 0
  rw [show (Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n)))
              (s0_iter K c_seq d_seq n)
            - algebraMap K _ tau
          = Polynomial.aeval (AdjoinRoot.root _) (U_n K c_seq d_seq tau n) by
        unfold U_n
        rw [map_sub, Polynomial.aeval_C]]
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

-- t2_general_eval_roundTheta + t2_general_eval_roundPsi: PROVEN below
-- (lines ~397+ and ~433+). Both follow structurally from
-- s0_iter_succ / s1_iter_succ as aeval-root-of-zero, with the Fin.val /
-- Fin.castSucc / Fin.succ + smul vs C-mul + phi normalization chain
-- discharged explicitly.

/-- Helper: Fin.castSucc.val = val. -/
private theorem fin_castSucc_val (r : Fin n) : r.castSucc.val = r.val := rfl

/-- Helper: Fin.succ.val = val + 1. -/
private theorem fin_succ_val (r : Fin n) : r.succ.val = r.val + 1 := rfl

/-- **Polynomial identity behind round-theta kill:** the difference
    `s0_iter (r+1) − C 7 · s0_iter r − (s1_iter r)² − C c_r = 0`
    in K[X], for any r. Direct from `s0_iter_succ`. -/
theorem s0_iter_succ_identity (c d : Nat → K) (r : Nat) :
    (s0_iter K c d (r + 1) - Polynomial.C 7 * s0_iter K c d r
      - (s1_iter K c d r) ^ 2 - Polynomial.C (c r) : Polynomial K) = 0 := by
  rw [s0_iter_succ]
  ring

/-- **Polynomial identity behind round-psi kill:** analogous for s1. -/
theorem s1_iter_succ_identity (c d : Nat → K) (r : Nat) :
    (s1_iter K c d (r + 1) - Polynomial.C 7 * s1_iter K c d r
      - (s0_iter K c d (r + 1)) ^ 2 - Polynomial.C (d r) : Polynomial K) = 0 := by
  rw [s1_iter_succ]
  ring

/-- **roundConstraintTheta at any r is killed by the general-n eval map.** -/
theorem t2_general_eval_roundTheta (c_seq d_seq : Nat → K) (tau : K) (n : Nat)
    (r : Fin n) :
    t2_general_eval K c_seq d_seq tau n
      (Mambo.T2CicoIdeal.roundConstraintTheta K n r (c_seq r.val)) = 0 := by
  unfold t2_general_eval Mambo.T2CicoIdeal.roundConstraintTheta Mambo.T2CicoIdeal.sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t2_general_var_image
  -- The 3 vars in roundTheta: (0, r+1), (0, r) [s0 branch], and (0-1, r) = (1, r) [s1 branch]
  simp only [if_true, fin_succ_val, fin_castSucc_val,
             show ((1 : Fin 2) = 0) ↔ False from ⟨by decide, False.elim⟩,
             if_false]
  -- Goal: aeval root (s0_iter (r.val + 1)) - phi • aeval root (s0_iter r.val)
  --        - aeval root (s1_iter r.val) * aeval root (s1_iter r.val)
  --        - algebraMap K _ (c_seq r.val) = 0
  have h_id := s0_iter_succ_identity K c_seq d_seq r.val
  -- Apply aeval root to both sides of h_id: aeval root LHS = aeval root 0 = 0
  have h_aeval : Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n))
                  (s0_iter K c_seq d_seq (r.val + 1)
                    - Polynomial.C 7 * s0_iter K c_seq d_seq r.val
                    - (s1_iter K c_seq d_seq r.val) ^ 2
                    - Polynomial.C (c_seq r.val)) = 0 := by
    rw [h_id]; exact map_zero _
  rw [map_sub, map_sub, map_sub, map_mul, Polynomial.aeval_C,
      map_pow, Polynomial.aeval_C] at h_aeval
  -- h_aeval: aeval root (s0_iter (r.val+1)) - algebraMap K _ 7 * aeval root (s0_iter r.val)
  --         - (aeval root (s1_iter r.val))^2 - algebraMap K _ (c_seq r.val) = 0
  -- Goal differs only in smul vs mul and pow vs ×
  show Polynomial.aeval (AdjoinRoot.root _) (s0_iter K c_seq d_seq (r.val + 1))
        - (Mambo.T2CicoIdeal.phi : K) • _
        - _ * _
        - algebraMap K _ (c_seq r.val) = 0
  rw [show (Mambo.T2CicoIdeal.phi : K) = 7 from rfl, Algebra.smul_def,
      ← pow_two]
  linear_combination h_aeval

/-- **roundConstraintPsi at any r is killed by the general-n eval map.** -/
theorem t2_general_eval_roundPsi (c_seq d_seq : Nat → K) (tau : K) (n : Nat)
    (r : Fin n) :
    t2_general_eval K c_seq d_seq tau n
      (Mambo.T2CicoIdeal.roundConstraintPsi K n r (d_seq r.val)) = 0 := by
  unfold t2_general_eval Mambo.T2CicoIdeal.roundConstraintPsi Mambo.T2CicoIdeal.sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  unfold t2_general_var_image
  -- 3 vars: (1, r+1), (1, r) [s1 branch], (0, r+1) [s0 branch]
  simp only [if_true, fin_succ_val, fin_castSucc_val,
             show ((1 : Fin 2) = 0) ↔ False from ⟨by decide, False.elim⟩,
             if_false]
  have h_id := s1_iter_succ_identity K c_seq d_seq r.val
  have h_aeval : Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n))
                  (s1_iter K c_seq d_seq (r.val + 1)
                    - Polynomial.C 7 * s1_iter K c_seq d_seq r.val
                    - (s0_iter K c_seq d_seq (r.val + 1)) ^ 2
                    - Polynomial.C (d_seq r.val)) = 0 := by
    rw [h_id]; exact map_zero _
  rw [map_sub, map_sub, map_sub, map_mul, Polynomial.aeval_C,
      map_pow, Polynomial.aeval_C] at h_aeval
  show Polynomial.aeval (AdjoinRoot.root _) (s1_iter K c_seq d_seq (r.val + 1))
        - (Mambo.T2CicoIdeal.phi : K) • _
        - _ * _
        - algebraMap K _ (d_seq r.val) = 0
  rw [show (Mambo.T2CicoIdeal.phi : K) = 7 from rfl, Algebra.smul_def,
      ← pow_two]
  linear_combination h_aeval

/-- **The full mamboT2Ideal at general n is killed by the eval map.** -/
theorem t2_general_eval_kills_ideal (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    Mambo.T2CicoIdeal.mamboT2Ideal K n (fun r => c_seq r.val)
        (fun r => d_seq r.val) tau
      ≤ RingHom.ker (t2_general_eval K c_seq d_seq tau n).toRingHom := by
  unfold Mambo.T2CicoIdeal.mamboT2Ideal
  rw [Ideal.span_le]
  rintro p (((⟨r, rfl⟩ | ⟨r, rfl⟩) | (rfl | rfl)))
  · exact t2_general_eval_roundTheta K c_seq d_seq tau n r
  · exact t2_general_eval_roundPsi K c_seq d_seq tau n r
  · exact t2_general_eval_boundaryStart K c_seq d_seq tau n
  · exact t2_general_eval_boundaryEnd K c_seq d_seq tau n

/-- IsTwoSided instance for mamboT2Ideal at general n. -/
instance (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    (Mambo.T2CicoIdeal.mamboT2Ideal K n (fun r => c_seq r.val)
        (fun r => d_seq r.val) tau).IsTwoSided := inferInstance

/-- **Factored general-n eval map** as an AlgHom on the quotient. -/
noncomputable def t2_general_eval_bar (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    (MvPolynomial (VarIndex 2 n) K ⧸
        Mambo.T2CicoIdeal.mamboT2Ideal K n
          (fun r => c_seq r.val) (fun r => d_seq r.val) tau) →ₐ[K]
    AdjoinRoot (U_n K c_seq d_seq tau n) :=
  Ideal.Quotient.liftₐ _ (t2_general_eval K c_seq d_seq tau n)
    (fun a ha => t2_general_eval_kills_ideal K c_seq d_seq tau n ha)

/-! ### s_(1,0) satisfies U_n in the quotient

For the AdjoinRoot.liftHom-based inverse, we need to show that the class
of `s_(1,0)` in the quotient satisfies the defining polynomial U_n. Per
the elimination structure, `s_(1,0)²` traverses up through the chain of
round constraints + boundaries, eventually equating to `(τ - constant)`
mod the ideal.

For general n, this is captured by the joint inductive identity:
  ∀ r ≤ n: in the quotient,
    mk(X(0, r)) = aeval mk(X(1,0)) (s0_iter r) AND
    mk(X(1, r)) = aeval mk(X(1,0)) (s1_iter r)

Then at r = n: mk(X(0, n)) = aeval mk(X(1,0)) (s0_iter n). And
mk(X(0, n)) = mk(C tau) (from boundaryEnd ∈ ideal). So
aeval mk(X(1,0)) (s0_iter n) = mk(C tau) = algebraMap K _ tau in the
quotient. Hence aeval mk(X(1,0)) (U_n) = aeval mk(X(1,0)) (s0_iter n - C tau)
= mk(C tau) - mk(C tau) = 0 in the quotient.

The joint induction itself is multi-step structural proof; deferred to
the next push. Once landed, AdjoinRoot.liftHom + AlgEquiv assembly closes
the paper Thm hilb_closed at general n. -/

/-- **Base case of joint inductive identity at r = 0.** At r = 0, both
    sides reduce trivially:
    - s0 side: mk(X(0,0)) = 0 (from boundaryStart) = aeval _ (s0_iter 0) = aeval _ 0 = 0
    - s1 side: mk(X(1,0)) = aeval mk(X(1,0)) X = mk(X(1,0)) by aeval_X. -/
theorem t2_general_mk_X_iter_eq_zero (c_seq d_seq : Nat → K) (tau : K) (n : Nat)
    (h_n_pos : 0 < n + 1) :
    let mk := Ideal.Quotient.mk
                (Mambo.T2CicoIdeal.mamboT2Ideal K n
                  (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau)
    mk (MvPolynomial.X (0, ⟨0, h_n_pos⟩))
      = Polynomial.aeval (mk (MvPolynomial.X (1, ⟨0, h_n_pos⟩)))
          (s0_iter K c_seq d_seq 0) ∧
    mk (MvPolynomial.X (1, ⟨0, h_n_pos⟩))
      = Polynomial.aeval (mk (MvPolynomial.X (1, ⟨0, h_n_pos⟩)))
          (s1_iter K c_seq d_seq 0) := by
  refine ⟨?_, ?_⟩
  · rw [s0_iter_zero, map_zero]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    unfold Mambo.T2CicoIdeal.mamboT2Ideal
    exact Ideal.subset_span (Or.inr (Or.inl rfl))
  · rw [s1_iter_zero, Polynomial.aeval_X]

set_option maxHeartbeats 800000 in
/-- s0 inductive step parametrized by `k : Fin n` (so k+1 ≤ n automatic).
    Given the joint IH at position k.castSucc, derive the s0 identity at
    position k.succ. -/
theorem t2_general_mk_X0_step (c_seq d_seq : Nat → K) (tau : K) (n : Nat) (k : Fin n)
    (h_ih_s0 :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (MvPolynomial.X (0, k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
            (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
          (s0_iter K c_seq d_seq k.val))
    (h_ih_s1 :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (MvPolynomial.X (1, k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
            (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
          (s1_iter K c_seq d_seq k.val)) :
    (Ideal.Quotient.mk
        (Mambo.T2CicoIdeal.mamboT2Ideal K n
          (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
      (MvPolynomial.X (0, k.succ))
    = Polynomial.aeval
        ((Ideal.Quotient.mk
            (Mambo.T2CicoIdeal.mamboT2Ideal K n
              (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
          (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
        (s0_iter K c_seq d_seq (k.val + 1)) := by
  -- roundConstraintTheta at r=k: in the ideal, so mk = 0
  have h_round_kill := t2_general_eval_roundTheta K c_seq d_seq tau n k
  -- Convert mk(roundConstraintTheta) = 0 from t2_general_eval form back to direct mk form
  -- Better: directly use Ideal.subset_span for membership
  have h_in_ideal :
      Mambo.T2CicoIdeal.roundConstraintTheta K n k (c_seq k.val)
        ∈ Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau := by
    unfold Mambo.T2CicoIdeal.mamboT2Ideal
    exact Ideal.subset_span (Or.inl (Or.inl ⟨k, rfl⟩))
  have h_mk_zero :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (Mambo.T2CicoIdeal.roundConstraintTheta K n k (c_seq k.val)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_ideal
  unfold Mambo.T2CicoIdeal.roundConstraintTheta Mambo.T2CicoIdeal.sVar at h_mk_zero
  have h_phi : (Mambo.T2CicoIdeal.phi : K) = 7 := rfl
  rw [h_phi] at h_mk_zero
  simp only [map_sub, map_smul, map_mul, Algebra.smul_def] at h_mk_zero
  -- Normalize: mk(algebraMap K MvPoly k) = algebraMap K Quotient k
  have h_norm_C7 : (Ideal.Quotient.mk
                    (Mambo.T2CicoIdeal.mamboT2Ideal K n
                      (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
                    ((algebraMap K (MvPolynomial (VarIndex 2 n) K)) 7)
                = algebraMap K _ 7 := rfl
  rw [h_norm_C7] at h_mk_zero
  -- After norm: h_mk_zero: mk(X(0,k+1)) - algebraMap _ 7 * mk(X(0,k))
  --                       - mk(X(1,k)) * mk(X(1,k)) - mk(C c_k) = 0
  have h_mk_C : (Ideal.Quotient.mk
                  (Mambo.T2CicoIdeal.mamboT2Ideal K n
                    (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
                  (MvPolynomial.C (c_seq k.val)
                    : MvPolynomial (VarIndex 2 n) K)
                = algebraMap K _ (c_seq k.val) := rfl
  rw [h_mk_C] at h_mk_zero
  rw [s0_iter_succ]
  rw [map_add, map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_C]
  rw [← h_ih_s0, ← h_ih_s1]
  linear_combination h_mk_zero

set_option maxHeartbeats 800000 in
/-- s1 inductive step parametrized by `k : Fin n`. Given the joint IH at
    k.castSucc AND the s0 step result at k.succ (just proven above),
    derive the s1 identity at k.succ. -/
theorem t2_general_mk_X1_step (c_seq d_seq : Nat → K) (tau : K) (n : Nat) (k : Fin n)
    (h_ih_s1 :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (MvPolynomial.X (1, k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
            (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
          (s1_iter K c_seq d_seq k.val))
    (h_s0_succ :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (MvPolynomial.X (0, k.succ))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
            (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
          (s0_iter K c_seq d_seq (k.val + 1))) :
    (Ideal.Quotient.mk
        (Mambo.T2CicoIdeal.mamboT2Ideal K n
          (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
      (MvPolynomial.X (1, k.succ))
    = Polynomial.aeval
        ((Ideal.Quotient.mk
            (Mambo.T2CicoIdeal.mamboT2Ideal K n
              (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
          (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
        (s1_iter K c_seq d_seq (k.val + 1)) := by
  have h_in_ideal :
      Mambo.T2CicoIdeal.roundConstraintPsi K n k (d_seq k.val)
        ∈ Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau := by
    unfold Mambo.T2CicoIdeal.mamboT2Ideal
    exact Ideal.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))
  have h_mk_zero :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (Mambo.T2CicoIdeal.roundConstraintPsi K n k (d_seq k.val)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_ideal
  unfold Mambo.T2CicoIdeal.roundConstraintPsi Mambo.T2CicoIdeal.sVar at h_mk_zero
  have h_phi : (Mambo.T2CicoIdeal.phi : K) = 7 := rfl
  rw [h_phi] at h_mk_zero
  simp only [map_sub, map_smul, map_mul, Algebra.smul_def] at h_mk_zero
  have h_norm_C7 : (Ideal.Quotient.mk
                    (Mambo.T2CicoIdeal.mamboT2Ideal K n
                      (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
                    ((algebraMap K (MvPolynomial (VarIndex 2 n) K)) 7)
                = algebraMap K _ 7 := rfl
  rw [h_norm_C7] at h_mk_zero
  have h_mk_C : (Ideal.Quotient.mk
                  (Mambo.T2CicoIdeal.mamboT2Ideal K n
                    (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
                  (MvPolynomial.C (d_seq k.val)
                    : MvPolynomial (VarIndex 2 n) K)
                = algebraMap K _ (d_seq k.val) := rfl
  rw [h_mk_C] at h_mk_zero
  rw [s1_iter_succ]
  rw [map_add, map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_C]
  rw [← h_ih_s1, ← h_s0_succ]
  linear_combination h_mk_zero

/-- **Joint inductive identity at general n** (paper Thm hilb_closed
    elimination-bridge). For every k ≤ n, in the quotient:
    `mk(X(0, k)) = aeval mk(X(1,0)) (s0_iter k)` AND
    `mk(X(1, k)) = aeval mk(X(1,0)) (s1_iter k)`.
    Proven by induction on k via s0_step + s1_step. -/
theorem t2_general_mk_X_iter_joint (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    ∀ k : Nat, ∀ (hk : k ≤ n),
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (MvPolynomial.X (0, ⟨k, Nat.lt_succ_of_le hk⟩))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
            (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
          (s0_iter K c_seq d_seq k) ∧
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (MvPolynomial.X (1, ⟨k, Nat.lt_succ_of_le hk⟩))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
            (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
          (s1_iter K c_seq d_seq k) := by
  intro k hk
  induction k with
  | zero => exact t2_general_mk_X_iter_eq_zero K c_seq d_seq tau n (Nat.succ_pos n)
  | succ j ih =>
    have hj : j ≤ n := Nat.le_of_succ_le hk
    obtain ⟨ih_s0, ih_s1⟩ := ih hj
    -- Wrap j as Fin n (since j + 1 ≤ n means j < n)
    have hj_lt : j < n := hk
    let k_fin : Fin n := ⟨j, hj_lt⟩
    -- Apply s0_step at k_fin (Fin coercions: k_fin.castSucc and ⟨j, _⟩ defeq)
    have h_s0_succ := t2_general_mk_X0_step K c_seq d_seq tau n k_fin ih_s0 ih_s1
    -- Apply s1_step at k_fin
    have h_s1_succ := t2_general_mk_X1_step K c_seq d_seq tau n k_fin ih_s1 h_s0_succ
    exact ⟨h_s0_succ, h_s1_succ⟩

/-- **The class of s_(1,0) satisfies U_n in the quotient ring** (general n).
    Follows from the joint inductive identity at k=n + boundaryEnd ∈ ideal. -/
theorem t2_general_U_n_root_eq_zero (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    Polynomial.aeval
        ((Ideal.Quotient.mk
            (Mambo.T2CicoIdeal.mamboT2Ideal K n
              (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
          (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
        (U_n K c_seq d_seq tau n) = 0 := by
  -- U_n = s0_iter n - C tau. aeval = aeval(s0_iter n) - algebraMap K _ tau.
  unfold U_n
  rw [map_sub, Polynomial.aeval_C]
  -- Goal: aeval mk(X(1,0)) (s0_iter n) - algebraMap K _ tau = 0
  -- Use joint identity at k=n: aeval(...) (s0_iter n) = mk(X(0, n))
  obtain ⟨h_s0_at_n, _⟩ := t2_general_mk_X_iter_joint K c_seq d_seq tau n n (le_refl n)
  rw [← h_s0_at_n]
  -- Goal: mk(X(0, ⟨n, _⟩)) - algebraMap K _ tau = 0
  -- boundaryEnd = X(0, n) - C tau is in ideal, so mk(X(0, n)) = mk(C tau) = algebraMap K _ tau
  have h_bd_kill :
      (Ideal.Quotient.mk
          (Mambo.T2CicoIdeal.mamboT2Ideal K n
            (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
        (Mambo.T2CicoIdeal.boundaryEnd K n tau) = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    unfold Mambo.T2CicoIdeal.mamboT2Ideal
    exact Ideal.subset_span (Or.inr (Or.inr rfl))
  unfold Mambo.T2CicoIdeal.boundaryEnd Mambo.T2CicoIdeal.sVar at h_bd_kill
  rw [map_sub] at h_bd_kill
  -- h_bd_kill: mk(X(0, ⟨n, Nat.lt_succ_self n⟩)) - mk(C tau) = 0
  have h_mk_C : (Ideal.Quotient.mk
                  (Mambo.T2CicoIdeal.mamboT2Ideal K n
                    (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau))
                  (MvPolynomial.C tau : MvPolynomial (VarIndex 2 n) K)
                = algebraMap K _ tau := rfl
  rw [h_mk_C] at h_bd_kill
  linear_combination h_bd_kill

/-- **Inverse alg-hom at general n**: AdjoinRoot(U_n) → MvPoly/mamboT2Ideal
    via AdjoinRoot.liftHom sending the AdjoinRoot generator to mk(X(1,0)). -/
noncomputable def t2_general_inverse (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    AdjoinRoot (U_n K c_seq d_seq tau n) →ₐ[K]
    (MvPolynomial (VarIndex 2 n) K ⧸
        Mambo.T2CicoIdeal.mamboT2Ideal K n
          (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau) :=
  AdjoinRoot.liftHom _
    ((Ideal.Quotient.mk _) (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)))
    (t2_general_U_n_root_eq_zero K c_seq d_seq tau n)

/-- **Forward direction** (eval_bar ∘ inverse = id on AdjoinRoot).
    Check on root via AdjoinRoot.algHom_ext + liftHom_root + var_image computation. -/
theorem t2_general_eval_bar_comp_inverse (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    (t2_general_eval_bar K c_seq d_seq tau n).comp
        (t2_general_inverse K c_seq d_seq tau n)
      = AlgHom.id K (AdjoinRoot (U_n K c_seq d_seq tau n)) := by
  apply AdjoinRoot.algHom_ext
  show t2_general_eval_bar K c_seq d_seq tau n
          (t2_general_inverse K c_seq d_seq tau n (AdjoinRoot.root _))
        = AdjoinRoot.root _
  unfold t2_general_inverse
  rw [AdjoinRoot.liftHom_root]
  -- Goal: eval_bar (mk (X (1, ⟨0, _⟩))) = root
  unfold t2_general_eval_bar
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  -- t2_general_eval (X (1, ⟨0, _⟩)) = var_image (1, ⟨0, _⟩) = s1_iter 0 at root = X at root = root
  unfold t2_general_eval
  show (MvPolynomial.aeval (t2_general_var_image K c_seq d_seq tau n))
          (MvPolynomial.X (1, ⟨0, Nat.succ_pos n⟩)) = AdjoinRoot.root _
  rw [MvPolynomial.aeval_X]
  unfold t2_general_var_image
  simp only [show ((1 : Fin 2) = 0) ↔ False from ⟨by decide, False.elim⟩, if_false,
             s1_iter_zero, Polynomial.aeval_X]

set_option maxHeartbeats 800000 in
/-- **Reverse direction** (inverse ∘ eval_bar = id on quotient).
    Use Ideal.Quotient.algHom_ext + MvPolynomial.algHom_ext to reduce to
    checking each X(c, r) variable. For each, use the joint identity. -/
theorem t2_general_inverse_comp_eval_bar (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    (t2_general_inverse K c_seq d_seq tau n).comp
        (t2_general_eval_bar K c_seq d_seq tau n)
      = AlgHom.id K
          (MvPolynomial (VarIndex 2 n) K ⧸
              Mambo.T2CicoIdeal.mamboT2Ideal K n
                (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  -- v : VarIndex 2 n = Fin 2 × Fin (n+1). Destructure.
  obtain ⟨c, r⟩ := v
  -- Reduce eval_bar (mk(X (c, r))) = eval (X (c, r)) = aeval root (s_c_iter r.val)
  show t2_general_inverse K c_seq d_seq tau n
          (t2_general_eval_bar K c_seq d_seq tau n
            ((Ideal.Quotient.mkₐ K _) (MvPolynomial.X (c, r))))
        = (Ideal.Quotient.mkₐ K _) (MvPolynomial.X (c, r))
  show t2_general_inverse K c_seq d_seq tau n
          (t2_general_eval_bar K c_seq d_seq tau n
            ((Ideal.Quotient.mk _) (MvPolynomial.X (c, r))))
        = (Ideal.Quotient.mk _) (MvPolynomial.X (c, r))
  unfold t2_general_eval_bar t2_general_eval
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  show t2_general_inverse K c_seq d_seq tau n
          ((MvPolynomial.aeval (t2_general_var_image K c_seq d_seq tau n))
            (MvPolynomial.X (c, r)))
        = _
  rw [MvPolynomial.aeval_X]
  unfold t2_general_var_image
  -- Case split on c : Fin 2 via fin_cases; the if reduces via defeq using `show`.
  fin_cases c
  · -- c = ⟨0, _⟩: if-branch resolves to the s0_iter image (defeq)
    show t2_general_inverse K c_seq d_seq tau n
            (Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n))
              (s0_iter K c_seq d_seq r.val))
          = (Ideal.Quotient.mk _) (MvPolynomial.X (⟨0, by decide⟩, r))
    -- Convert Polynomial.aeval root → AdjoinRoot.mk to apply liftHom_mk
    rw [AdjoinRoot.aeval_eq]
    unfold t2_general_inverse
    rw [AdjoinRoot.liftHom_mk]
    -- Goal: aeval (mk(X(1,0))) (s0_iter r.val) = mk(X(⟨0, _⟩, r))
    have hr_le : r.val ≤ n := Nat.lt_succ_iff.mp r.isLt
    have ⟨h_s0, _⟩ := t2_general_mk_X_iter_joint K c_seq d_seq tau n r.val hr_le
    -- h_s0: mk(X(0, ⟨r.val, _⟩)) = aeval mk(X(1,0)) (s0_iter r.val)
    -- Goal expects mk(X(⟨0,_⟩, r)) which is defeq.
    convert h_s0.symm using 2
  · -- c = ⟨1, _⟩: else-branch resolves to the s1_iter image (defeq)
    show t2_general_inverse K c_seq d_seq tau n
            (Polynomial.aeval (AdjoinRoot.root (U_n K c_seq d_seq tau n))
              (s1_iter K c_seq d_seq r.val))
          = (Ideal.Quotient.mk _) (MvPolynomial.X (⟨1, by decide⟩, r))
    rw [AdjoinRoot.aeval_eq]
    unfold t2_general_inverse
    rw [AdjoinRoot.liftHom_mk]
    have hr_le : r.val ≤ n := Nat.lt_succ_iff.mp r.isLt
    have ⟨_, h_s1⟩ := t2_general_mk_X_iter_joint K c_seq d_seq tau n r.val hr_le
    convert h_s1.symm using 2

/-- **The general-n algebra equivalence**:
    MvPoly(VarIndex 2 n) / mamboT2Ideal_n  ≃ₐ[K]  AdjoinRoot(U_n).

    Assembled from eval_bar (forward) and inverse, with the two unit/counit
    proofs `t2_general_eval_bar_comp_inverse` and `t2_general_inverse_comp_eval_bar`. -/
noncomputable def t2_general_algEquiv (c_seq d_seq : Nat → K) (tau : K) (n : Nat) :
    (MvPolynomial (VarIndex 2 n) K ⧸
        Mambo.T2CicoIdeal.mamboT2Ideal K n
          (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau)
      ≃ₐ[K] AdjoinRoot (U_n K c_seq d_seq tau n) :=
  AlgEquiv.ofAlgHom
    (t2_general_eval_bar K c_seq d_seq tau n)
    (t2_general_inverse K c_seq d_seq tau n)
    (t2_general_eval_bar_comp_inverse K c_seq d_seq tau n)
    (t2_general_inverse_comp_eval_bar K c_seq d_seq tau n)

/-- **Paper Thm `thm:hilb_closed` at general n (t=2 case)**:

    `dim_K(MvPoly(VarIndex 2 n) / mamboT2Ideal_n) = 2 · 4^(n-1) = 2^(2n-1)`

    Combines the general-n AlgEquiv with the AdjoinRoot finrank formula
    `dim_K(K[x]/U_n) = natDegree(U_n) = 2 · 4^(n-1)`. -/
theorem t2_general_dim (c_seq d_seq : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    Module.finrank K
        (MvPolynomial (VarIndex 2 n) K ⧸
            Mambo.T2CicoIdeal.mamboT2Ideal K n
              (fun r' => c_seq r'.val) (fun r' => d_seq r'.val) tau)
      = 2 * 4^(n-1) := by
  rw [(t2_general_algEquiv K c_seq d_seq tau n).toLinearEquiv.finrank_eq]
  exact U_n_AdjoinRoot_finrank K c_seq d_seq tau n hn

end Mambo.T2GeneralN
