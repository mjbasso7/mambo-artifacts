import Mambo.T3CicoIdeal
import Mambo.T3GeneralN
import Mambo.T3FirstCellCyclic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A2 universal-n: lift `t3_first_cell_cyclic_finrank` to all n ≥ 1.

## Goal

Prove:
  `Module.finrank K (MvPoly(VarIndex 3 n) / mamboT3IdealCyclic K n …) = 2^(3n − 2)`
for all n ≥ 1, matching the paper formula `d_reg = 3n − 1`.

## Strategy

Mirror `T2GeneralN.lean`:
1. Joint identity `t3_mk_X_iter_joint`: ∀ k ≤ n, three identities (one per
   cell c ∈ Fin 3) saying `mk(X(c, ⟨k, _⟩))` equals
   `aeval (mk X(2, 0)) (s_c_iter k)` in the cyclic quotient.
   Proven by strong induction on k.
2. Annihilator: `aeval (mk X(2, 0)) (U_n_t3 K c0 c1 c2 tau n) = 0` in the
   cyclic quotient — follows from joint identity at k=n + boundaryEnd.
3. Inverse AlgHom: `AdjoinRoot(U_n_t3 …) → cyclic quotient`,
   sending the AdjoinRoot generator to mk X(2, 0).
4. Forward/reverse compositions = id, build `AlgEquiv` via
   `AlgEquiv.ofAlgHom`.
5. Finrank lifts via `.toLinearEquiv.finrank_eq` +
   `U_n_t3_AdjoinRoot_finrank_closed`.

## Status

Scaffolding. Joint identity + steps to be proven in sequence.
-/

namespace Mambo.T3UniversalN

open MvPolynomial Mambo.B2Enumeration Mambo.T3FirstCellCyclic

variable (K : Type*) [Field K]

/-- **Base case of the joint inductive identity at r = 0.**

At r = 0:
- `s0_iter 0 = 0`, so `aeval _ (s0_iter 0) = 0`, and `mk(X(0,0)) = 0` via boundaryStart.
- `s1_iter 0 = X`, so `aeval mk(X(2,0)) (s1_iter 0) = mk(X(2,0))`, and `mk(X(1,0)) = mk(X(2,0))`
  via cyclicityGenerator.
- `s2_iter 0 = X`, so `aeval mk(X(2,0)) (s2_iter 0) = mk(X(2,0))`, and `mk(X(2,0)) = mk(X(2,0))`
  trivially. -/
theorem t3_mk_X_iter_joint_zero (c0 c1 c2 : Nat → K) (tau : K) (n : Nat)
    (h_n_pos : 0 < n + 1) :
    let mk := Ideal.Quotient.mk
                (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                  (fun r' => c2 r'.val) tau)
    mk (MvPolynomial.X ((0 : Fin 3), ⟨0, h_n_pos⟩))
      = Polynomial.aeval (mk (MvPolynomial.X ((2 : Fin 3), ⟨0, h_n_pos⟩)))
          (Mambo.T3GeneralN.s0_iter K c0 c1 c2 0) ∧
    mk (MvPolynomial.X ((1 : Fin 3), ⟨0, h_n_pos⟩))
      = Polynomial.aeval (mk (MvPolynomial.X ((2 : Fin 3), ⟨0, h_n_pos⟩)))
          (Mambo.T3GeneralN.s1_iter K c0 c1 c2 0) ∧
    mk (MvPolynomial.X ((2 : Fin 3), ⟨0, h_n_pos⟩))
      = Polynomial.aeval (mk (MvPolynomial.X ((2 : Fin 3), ⟨0, h_n_pos⟩)))
          (Mambo.T3GeneralN.s2_iter K c0 c1 c2 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (c=0, r=0): mk(X(0,0)) = 0
    rw [Mambo.T3GeneralN.s0_iter_zero, map_zero]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inr (Or.inl rfl))
  · -- (c=1, r=0): mk(X(1,0)) = mk(X(2,0))
    rw [Mambo.T3GeneralN.s1_iter_zero, Polynomial.aeval_X]
    -- mk(X(1,0)) - mk(X(2,0)) = 0 via cyclicityGenerator
    have h_cy_mem : cyclicityGenerator K n
                    ∈ mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                        (fun r' => c2 r'.val) tau := by
      apply Ideal.mem_sup_right
      exact Ideal.subset_span rfl
    have h_mk : (Ideal.Quotient.mk _) (cyclicityGenerator K n) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr h_cy_mem
    unfold cyclicityGenerator Mambo.T3CicoIdeal.sVar at h_mk
    rw [map_sub] at h_mk
    linear_combination h_mk
  · -- (c=2, r=0): trivial
    rw [Mambo.T3GeneralN.s2_iter_zero, Polynomial.aeval_X]

set_option maxHeartbeats 1600000 in
/-- **s0 inductive step parametrized by `k : Fin n`**.
    Given the joint IH at position `k.castSucc` for cells 0 and 2, derive
    the s0 identity at position `k.succ`. Uses roundConstraint0 ∈ ideal. -/
theorem t3_general_mk_X0_step (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (k : Fin n)
    (h_ih_s0 :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (MvPolynomial.X ((0 : Fin 3), k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                (fun r' => c2 r'.val) tau))
            (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
          (Mambo.T3GeneralN.s0_iter K c0 c1 c2 k.val))
    (h_ih_s2 :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (MvPolynomial.X ((2 : Fin 3), k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                (fun r' => c2 r'.val) tau))
            (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
          (Mambo.T3GeneralN.s2_iter K c0 c1 c2 k.val)) :
    (Ideal.Quotient.mk
        (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
          (fun r' => c2 r'.val) tau))
      (MvPolynomial.X ((0 : Fin 3), k.succ))
    = Polynomial.aeval
        ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
        (Mambo.T3GeneralN.s0_iter K c0 c1 c2 (k.val + 1)) := by
  -- roundConstraint0 at r=k: X(0, k+1) - 7·X(0, k) - X(2, k)² - C(c0_k)
  -- is in the cyclic ideal (inherited from mamboT3Ideal via mem_sup_left).
  have h_in_ideal :
      Mambo.T3CicoIdeal.roundConstraint0 K n k (c0 k.val)
        ∈ mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau := by
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨k, rfl⟩)))
  have h_mk_zero :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (Mambo.T3CicoIdeal.roundConstraint0 K n k (c0 k.val)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_ideal
  unfold Mambo.T3CicoIdeal.roundConstraint0 Mambo.T3CicoIdeal.sVar at h_mk_zero
  rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl] at h_mk_zero
  simp only [map_sub, map_smul, map_mul, Algebra.smul_def] at h_mk_zero
  -- h_mk_zero after normalization: mk(X(0,k+1)) - 7·mk(X(0,k.castSucc))
  --                               - mk(X(2,k.castSucc))² - algebraMap (c0 k.val) = 0
  -- Unfold s0_iter (k+1) on the RHS:
  rw [Mambo.T3GeneralN.s0_iter_succ]
  -- aeval over (C 7 * s0_iter k + (s2_iter k)² + C (c0 k))
  rw [map_add, map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_C]
  -- Substitute IH for s0 and s2 at k
  rw [← h_ih_s0, ← h_ih_s2]
  -- Normalize algebraMap K MvPoly 7 → mk(C 7) → algebraMap K Quotient 7
  have h_norm_C7 : (Ideal.Quotient.mk
                    (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                      (fun r' => c2 r'.val) tau))
                    ((algebraMap K (MvPolynomial (VarIndex 3 n) K)) 7)
                = algebraMap K _ 7 := rfl
  rw [h_norm_C7] at h_mk_zero
  have h_mk_C : (Ideal.Quotient.mk
                  (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                    (fun r' => c2 r'.val) tau))
                  (MvPolynomial.C (c0 k.val)
                    : MvPolynomial (VarIndex 3 n) K)
                = algebraMap K _ (c0 k.val) := rfl
  rw [h_mk_C] at h_mk_zero
  linear_combination h_mk_zero

set_option maxHeartbeats 1600000 in
/-- **s1 inductive step parametrized by `k : Fin n`**.
    Given the IH for s1 at `k.castSucc` AND the s0 result at `k.succ` (from
    `t3_general_mk_X0_step`), derive the s1 identity at `k.succ`. -/
theorem t3_general_mk_X1_step (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (k : Fin n)
    (h_ih_s1 :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (MvPolynomial.X ((1 : Fin 3), k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                (fun r' => c2 r'.val) tau))
            (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
          (Mambo.T3GeneralN.s1_iter K c0 c1 c2 k.val))
    (h_s0_succ :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (MvPolynomial.X ((0 : Fin 3), k.succ))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                (fun r' => c2 r'.val) tau))
            (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
          (Mambo.T3GeneralN.s0_iter K c0 c1 c2 (k.val + 1))) :
    (Ideal.Quotient.mk
        (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
          (fun r' => c2 r'.val) tau))
      (MvPolynomial.X ((1 : Fin 3), k.succ))
    = Polynomial.aeval
        ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
        (Mambo.T3GeneralN.s1_iter K c0 c1 c2 (k.val + 1)) := by
  have h_in_ideal :
      Mambo.T3CicoIdeal.roundConstraint1 K n k (c1 k.val)
        ∈ mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau := by
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨k, rfl⟩)))
  have h_mk_zero :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (Mambo.T3CicoIdeal.roundConstraint1 K n k (c1 k.val)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_ideal
  unfold Mambo.T3CicoIdeal.roundConstraint1 Mambo.T3CicoIdeal.sVar at h_mk_zero
  rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl] at h_mk_zero
  simp only [map_sub, map_smul, map_mul, Algebra.smul_def] at h_mk_zero
  rw [Mambo.T3GeneralN.s1_iter_succ]
  rw [map_add, map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_C]
  rw [← h_ih_s1, ← h_s0_succ]
  have h_norm_C7 : (Ideal.Quotient.mk
                    (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                      (fun r' => c2 r'.val) tau))
                    ((algebraMap K (MvPolynomial (VarIndex 3 n) K)) 7)
                = algebraMap K _ 7 := rfl
  rw [h_norm_C7] at h_mk_zero
  have h_mk_C : (Ideal.Quotient.mk
                  (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                    (fun r' => c2 r'.val) tau))
                  (MvPolynomial.C (c1 k.val)
                    : MvPolynomial (VarIndex 3 n) K)
                = algebraMap K _ (c1 k.val) := rfl
  rw [h_mk_C] at h_mk_zero
  linear_combination h_mk_zero

set_option maxHeartbeats 1600000 in
/-- **s2 inductive step parametrized by `k : Fin n`**.
    Given the IH for s2 at `k.castSucc` AND the s1 result at `k.succ` (from
    `t3_general_mk_X1_step`), derive the s2 identity at `k.succ`. -/
theorem t3_general_mk_X2_step (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (k : Fin n)
    (h_ih_s2 :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (MvPolynomial.X ((2 : Fin 3), k.castSucc))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                (fun r' => c2 r'.val) tau))
            (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
          (Mambo.T3GeneralN.s2_iter K c0 c1 c2 k.val))
    (h_s1_succ :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (MvPolynomial.X ((1 : Fin 3), k.succ))
      = Polynomial.aeval
          ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                (fun r' => c2 r'.val) tau))
            (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
          (Mambo.T3GeneralN.s1_iter K c0 c1 c2 (k.val + 1))) :
    (Ideal.Quotient.mk
        (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
          (fun r' => c2 r'.val) tau))
      (MvPolynomial.X ((2 : Fin 3), k.succ))
    = Polynomial.aeval
        ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
        (Mambo.T3GeneralN.s2_iter K c0 c1 c2 (k.val + 1)) := by
  have h_in_ideal :
      Mambo.T3CicoIdeal.roundConstraint2 K n k (c2 k.val)
        ∈ mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau := by
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))
  have h_mk_zero :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (Mambo.T3CicoIdeal.roundConstraint2 K n k (c2 k.val)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_ideal
  unfold Mambo.T3CicoIdeal.roundConstraint2 Mambo.T3CicoIdeal.sVar at h_mk_zero
  rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl] at h_mk_zero
  simp only [map_sub, map_smul, map_mul, Algebra.smul_def] at h_mk_zero
  rw [Mambo.T3GeneralN.s2_iter_succ]
  rw [map_add, map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_C]
  rw [← h_ih_s2, ← h_s1_succ]
  have h_norm_C7 : (Ideal.Quotient.mk
                    (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                      (fun r' => c2 r'.val) tau))
                    ((algebraMap K (MvPolynomial (VarIndex 3 n) K)) 7)
                = algebraMap K _ 7 := rfl
  rw [h_norm_C7] at h_mk_zero
  have h_mk_C : (Ideal.Quotient.mk
                  (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                    (fun r' => c2 r'.val) tau))
                  (MvPolynomial.C (c2 k.val)
                    : MvPolynomial (VarIndex 3 n) K)
                = algebraMap K _ (c2 k.val) := rfl
  rw [h_mk_C] at h_mk_zero
  linear_combination h_mk_zero

/-- **Joint inductive identity**: for all `k ≤ n`, the three cells satisfy
    `mk(X(c, k)) = aeval mk(X(2, 0)) (s_c_iter k)` in the cyclic quotient. -/
theorem t3_mk_X_iter_joint (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    ∀ k : Nat, ∀ (hk : k ≤ n),
      ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((0 : Fin 3), ⟨k, Nat.lt_succ_of_le hk⟩))
        = Polynomial.aeval
            ((Ideal.Quotient.mk
                (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                  (fun r' => c2 r'.val) tau))
              (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
            (Mambo.T3GeneralN.s0_iter K c0 c1 c2 k)) ∧
      ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((1 : Fin 3), ⟨k, Nat.lt_succ_of_le hk⟩))
        = Polynomial.aeval
            ((Ideal.Quotient.mk
                (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                  (fun r' => c2 r'.val) tau))
              (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
            (Mambo.T3GeneralN.s1_iter K c0 c1 c2 k)) ∧
      ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((2 : Fin 3), ⟨k, Nat.lt_succ_of_le hk⟩))
        = Polynomial.aeval
            ((Ideal.Quotient.mk
                (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                  (fun r' => c2 r'.val) tau))
              (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
            (Mambo.T3GeneralN.s2_iter K c0 c1 c2 k)) := by
  intro k hk
  induction k with
  | zero => exact t3_mk_X_iter_joint_zero K c0 c1 c2 tau n (Nat.succ_pos n)
  | succ j ih =>
    have hj : j ≤ n := Nat.le_of_succ_le hk
    obtain ⟨ih_s0, ih_s1, ih_s2⟩ := ih hj
    have hj_lt : j < n := hk
    let k_fin : Fin n := ⟨j, hj_lt⟩
    have h_s0_succ := t3_general_mk_X0_step K c0 c1 c2 tau n k_fin ih_s0 ih_s2
    have h_s1_succ := t3_general_mk_X1_step K c0 c1 c2 tau n k_fin ih_s1 h_s0_succ
    have h_s2_succ := t3_general_mk_X2_step K c0 c1 c2 tau n k_fin ih_s2 h_s1_succ
    exact ⟨h_s0_succ, h_s1_succ, h_s2_succ⟩

/-- **The class of s_(2,0) satisfies U_n_t3 in the cyclic quotient** (general n).
    Follows from joint identity at k=n + boundaryEnd ∈ ideal. -/
theorem t3_U_n_root_eq_zero_cyclic (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    Polynomial.aeval
        ((Ideal.Quotient.mk
            (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau))
          (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
        (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n) = 0 := by
  unfold Mambo.T3GeneralN.U_n_t3
  rw [map_sub, Polynomial.aeval_C]
  -- Joint at k=n: aeval (...) (s0_iter n) = mk(X(0, ⟨n, _⟩))
  obtain ⟨h_s0_at_n, _, _⟩ := t3_mk_X_iter_joint K c0 c1 c2 tau n n (le_refl n)
  rw [← h_s0_at_n]
  -- boundaryEnd K n tau = X(0, n) - C tau is in mamboT3Ideal hence cyclic ideal
  have h_bd_kill :
      (Ideal.Quotient.mk
          (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau))
        (Mambo.T3CicoIdeal.boundaryEnd K n tau) = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inr (Or.inr rfl))
  unfold Mambo.T3CicoIdeal.boundaryEnd Mambo.T3CicoIdeal.sVar at h_bd_kill
  rw [map_sub] at h_bd_kill
  have h_mk_C : (Ideal.Quotient.mk
                  (mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
                    (fun r' => c2 r'.val) tau))
                  (MvPolynomial.C tau : MvPolynomial (VarIndex 3 n) K)
                = algebraMap K _ tau := rfl
  rw [h_mk_C] at h_bd_kill
  linear_combination h_bd_kill

/-- **Inverse AlgHom at general n** (cyclic): `AdjoinRoot(U_n_t3) → MvPoly/mamboT3IdealCyclic`,
    sending the AdjoinRoot generator to `mk(X(2, 0))`. -/
noncomputable def t3_cyclic_inverse_general (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n) →ₐ[K]
    (MvPolynomial (VarIndex 3 n) K ⧸
      mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
        (fun r' => c2 r'.val) tau) :=
  AdjoinRoot.liftHom _
    ((Ideal.Quotient.mk _) (MvPolynomial.X ((2 : Fin 3), ⟨0, Nat.succ_pos n⟩)))
    (t3_U_n_root_eq_zero_cyclic K c0 c1 c2 tau n)

set_option maxHeartbeats 4000000 in
/-- **Forward direction at general n**: `bar ∘ inverse = id` on `AdjoinRoot`. -/
theorem t3_general_eval_cyclic_bar_comp_inverse_general (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (t3_general_eval_cyclic_bar K c0 c1 c2 tau n).comp
      (t3_cyclic_inverse_general K c0 c1 c2 tau n)
    = AlgHom.id K (AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n)) := by
  apply AdjoinRoot.algHom_ext
  show t3_general_eval_cyclic_bar K c0 c1 c2 tau n
       (t3_cyclic_inverse_general K c0 c1 c2 tau n
         (AdjoinRoot.root (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n)))
       = AdjoinRoot.root _
  unfold t3_cyclic_inverse_general
  rw [AdjoinRoot.liftHom_root]
  exact t3_general_eval_cyclic_bar_X20_eq_root K _ _ _ _ n (Nat.succ_pos n)

set_option maxHeartbeats 4000000 in
/-- **Reverse direction at general n**: `inverse ∘ bar = id` on the source quotient.
    Reduce via `Ideal.Quotient.algHom_ext` + `MvPolynomial.algHom_ext` to checking
    each variable `X (c, r)`. For each, use the joint identity. -/
theorem t3_cyclic_inverse_comp_eval_bar_general (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (t3_cyclic_inverse_general K c0 c1 c2 tau n).comp
        (t3_general_eval_cyclic_bar K c0 c1 c2 tau n)
      = AlgHom.id K (MvPolynomial (VarIndex 3 n) K ⧸
          mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
            (fun r' => c2 r'.val) tau) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨c, r⟩ := v
  -- Goal: (inverse ∘ bar) (mk(X(c,r))) = mk(X(c,r))
  show t3_cyclic_inverse_general K c0 c1 c2 tau n
        (t3_general_eval_cyclic_bar K c0 c1 c2 tau n
          ((Ideal.Quotient.mk _) (MvPolynomial.X (c, r))))
      = (Ideal.Quotient.mk _) (MvPolynomial.X (c, r))
  -- Compute bar via aeval root (s_c_iter r.val)
  unfold t3_general_eval_cyclic_bar
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  show t3_cyclic_inverse_general K c0 c1 c2 tau n
        ((MvPolynomial.aeval (Mambo.T3GeneralN.t3_general_var_image K c0 c1 c2 tau n))
          (MvPolynomial.X (c, r)))
      = _
  rw [MvPolynomial.aeval_X]
  unfold Mambo.T3GeneralN.t3_general_var_image
  -- Get joint identity at k = r.val (well-defined since r.val < n+1, but
  -- we need r.val ≤ n which is r.val < n+1).
  have hr_le : r.val ≤ n := Nat.lt_succ_iff.mp r.isLt
  obtain ⟨h_s0, h_s1, h_s2⟩ := t3_mk_X_iter_joint K c0 c1 c2 tau n r.val hr_le
  -- Split on c : Fin 3
  fin_cases c
  · -- c = 0: image = aeval root (s0_iter r.val); inverse(aeval root p) = aeval (mk X(2,0)) p
    show t3_cyclic_inverse_general K c0 c1 c2 tau n
          (Polynomial.aeval (AdjoinRoot.root _)
            (Mambo.T3GeneralN.s0_iter K c0 c1 c2 r.val))
          = (Ideal.Quotient.mk _) (MvPolynomial.X (⟨0, by decide⟩, r))
    rw [AdjoinRoot.aeval_eq]
    unfold t3_cyclic_inverse_general
    rw [AdjoinRoot.liftHom_mk]
    -- Goal: aeval (mk X(2,0)) (s0_iter r.val) = mk(X(⟨0,_⟩, r))
    convert h_s0.symm using 2
  · -- c = 1
    show t3_cyclic_inverse_general K c0 c1 c2 tau n
          (Polynomial.aeval (AdjoinRoot.root _)
            (Mambo.T3GeneralN.s1_iter K c0 c1 c2 r.val))
          = (Ideal.Quotient.mk _) (MvPolynomial.X (⟨1, by decide⟩, r))
    rw [AdjoinRoot.aeval_eq]
    unfold t3_cyclic_inverse_general
    rw [AdjoinRoot.liftHom_mk]
    convert h_s1.symm using 2
  · -- c = 2
    show t3_cyclic_inverse_general K c0 c1 c2 tau n
          (Polynomial.aeval (AdjoinRoot.root _)
            (Mambo.T3GeneralN.s2_iter K c0 c1 c2 r.val))
          = (Ideal.Quotient.mk _) (MvPolynomial.X (⟨2, by decide⟩, r))
    rw [AdjoinRoot.aeval_eq]
    unfold t3_cyclic_inverse_general
    rw [AdjoinRoot.liftHom_mk]
    convert h_s2.symm using 2

/-- **The general-n algebra equivalence (cyclic-reduced)**:
    `MvPoly(VarIndex 3 n) / mamboT3IdealCyclic_n ≃ₐ[K] AdjoinRoot(U_n_t3)`.

    Assembled from `t3_general_eval_cyclic_bar` (forward) and
    `t3_cyclic_inverse_general` (reverse). -/
noncomputable def t3_cyclic_general_algEquiv (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (MvPolynomial (VarIndex 3 n) K ⧸
        mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
          (fun r' => c2 r'.val) tau)
      ≃ₐ[K] AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n) :=
  AlgEquiv.ofAlgHom
    (t3_general_eval_cyclic_bar K c0 c1 c2 tau n)
    (t3_cyclic_inverse_general K c0 c1 c2 tau n)
    (t3_general_eval_cyclic_bar_comp_inverse_general K c0 c1 c2 tau n)
    (t3_cyclic_inverse_comp_eval_bar_general K c0 c1 c2 tau n)

/-- **A2 universal-n theorem**: under cyclic reduction, the Mambo t=3 CICO
    quotient at depth `n ≥ 1` has K-finrank `2^(3n − 2)`, matching paper
    `d_reg = 3n − 1`. -/
theorem t3_universal_n_cyclic_finrank (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (hn : 1 ≤ n) :
    Module.finrank K
        (MvPolynomial (VarIndex 3 n) K ⧸
            mamboT3IdealCyclic K n (fun r' => c0 r'.val) (fun r' => c1 r'.val)
              (fun r' => c2 r'.val) tau)
      = 2 ^ (3 * n - 2) := by
  rw [(t3_cyclic_general_algEquiv K c0 c1 c2 tau n).toLinearEquiv.finrank_eq]
  exact Mambo.T3GeneralN.U_n_t3_AdjoinRoot_finrank_closed K c0 c1 c2 tau n hn

end Mambo.T3UniversalN
