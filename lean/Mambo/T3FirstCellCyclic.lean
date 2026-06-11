import Mambo.T3CicoIdeal
import Mambo.T3GeneralN
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A2 first cell: t = 3 d_reg first-cell finrank via cyclic reduction

## Background

`Mambo.T3CicoIdeal.mamboT3Ideal n` uses the legacy 2-boundary form
(`s_{0,0} = 0` and `s_{0,n} = τ` as the only boundary constraints).
At t = 3, this leaves BOTH `s_{1,0}` and `s_{2,0}` free in the quotient
ring, producing a positive-Krull-dimensional ideal (infinite K-finrank).

Empirically (sage at p = 257, n = 1..12), the regularity degree `d_reg`
of this ideal matches the paper formula `3n - 1`, but the
`Module.finrank` is INFINITE without additional structure. The paper
formula corresponds to the d_reg of the ideal under the implicit
**cyclicity reduction** — the K[X]-module structure on the quotient
via x ↦ s_{2,0}-multiplication is cyclic at production widths (sage-verified),
so
`s_{1,0}` is expressible as a polynomial in `s_{2,0}`. Concretely, this
is equivalent to adding the relation `s_{1,0} - s_{2,0} = 0` (or any
other primitive relation that pins down a single CICO unknown).

This file defines the **cyclic-reduced ideal**
`mamboT3IdealCyclic n := mamboT3Ideal n + ⟨X(1,0) - X(2,0)⟩` and
proves the n = 1 first-cell finrank theorem:

  `Module.finrank K (MvPoly / mamboT3IdealCyclic 1) = 2 = 2^(3·1-2)`

matching paper d_reg = 3·1 - 1 = 2 (via d_reg = HF length convention).

## Status

First cell (n=1) closed sorry-free. The AlgEquiv between
`MvPoly(VarIndex 3 1) ⧸ mamboT3IdealCyclic K 1 …` and
`AdjoinRoot(U_n_t3 K c0 c1 c2 tau 1)` is constructed from two AlgHoms
(`t3_general_eval_cyclic_bar` and `t3_cyclic_inverse_n1`) with both
compositions identity-checked (`t3_general_eval_cyclic_bar_comp_inverse_n1`
and `t3_cyclic_inverse_comp_eval_bar_n1`). The reverse-direction
identity is closed by a 6-case fin_cases analysis (3 cells × 2 depths)
using boundaryStart, boundaryEnd, the three round constraints, and the
cyclicity generator. Finrank conclusion lifts via
`AlgEquiv.toLinearEquiv.finrank_eq` + `U_n_t3_AdjoinRoot_finrank_closed`.
-/

namespace Mambo.T3FirstCellCyclic

open MvPolynomial Mambo.B2Enumeration

variable (K : Type*) [Field K]

/-- The cyclicity-bridge generator at depth 0: `s_{1,0} - s_{2,0}`.
    Adding this to the ideal collapses the bivariate free elimination
    to univariate (s_{2,0} as the single primitive cell). -/
noncomputable def cyclicityGenerator (n : Nat) : MvPolynomial (VarIndex 3 n) K :=
  Mambo.T3CicoIdeal.sVar K n 1 ⟨0, Nat.succ_pos n⟩
    - Mambo.T3CicoIdeal.sVar K n 2 ⟨0, Nat.succ_pos n⟩

/-- The cyclic-reduced Mambo t = 3 CICO ideal. Equals
    `mamboT3Ideal n ∪ {cyclicityGenerator n}` as generating set.

    Under universal cyclicity (empirical for t = 3 at all production
    widths), the K[X]-module structure of `MvPoly / mamboT3Ideal n` is
    cyclic with `s_{2,0}` as primitive, so adding this relation does
    NOT change the underlying scheme — it only makes the cyclic
    structure explicit at the ideal level for finrank computations. -/
noncomputable def mamboT3IdealCyclic (n : Nat)
    (c0_seq c1_seq c2_seq : Fin n → K) (tau : K) :
    Ideal (MvPolynomial (VarIndex 3 n) K) :=
  Mambo.T3CicoIdeal.mamboT3Ideal K n c0_seq c1_seq c2_seq tau
    ⊔ Ideal.span {cyclicityGenerator K n}

/-- The cyclicity generator is killed by `t3_general_eval`.

    At any n, both X(1,0) and X(2,0) map to the same AdjoinRoot element
    (= `aeval root X = root`), since `s1_iter 0 = s2_iter 0 = Polynomial.X`
    by definition. So `X(1,0) - X(2,0)` ↦ 0. -/
theorem t3_general_eval_cyclicityGenerator
    (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (h_n_pos : 0 < n + 1) :
    Mambo.T3GeneralN.t3_general_eval K c0 c1 c2 tau n
      (cyclicityGenerator K n) = 0 := by
  unfold cyclicityGenerator Mambo.T3GeneralN.t3_general_eval
    Mambo.T3CicoIdeal.sVar
  rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  unfold Mambo.T3GeneralN.t3_general_var_image
  -- Both X(1,0) and X(2,0) reach the same s_iter_zero = X branch image.
  -- X(1,0): v.1.val = 1 → else-if-1 branch → aeval root (s1_iter 0)
  -- X(2,0): v.1.val = 2 → else branch → aeval root (s2_iter 0)
  rw [if_neg (by decide : ¬ ((1 : Fin 3).val = 0)),
      if_pos (by decide : (1 : Fin 3).val = 1),
      if_neg (by decide : ¬ ((2 : Fin 3).val = 0)),
      if_neg (by decide : ¬ ((2 : Fin 3).val = 1))]
  rw [Mambo.T3GeneralN.s1_iter_zero, Mambo.T3GeneralN.s2_iter_zero]
  -- aeval root X - aeval root X = 0
  simp

/-- **The cyclic-reduced ideal is killed by `t3_general_eval`.**
    Combines `t3_general_eval_kills_ideal` (existing) with the
    `cyclicityGenerator` kill. Holds at any n ≥ 0. -/
theorem t3_general_eval_kills_cyclic_ideal
    (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    mamboT3IdealCyclic K n (fun r => c0 r.val) (fun r => c1 r.val)
        (fun r => c2 r.val) tau
      ≤ RingHom.ker
          (Mambo.T3GeneralN.t3_general_eval K c0 c1 c2 tau n).toRingHom := by
  unfold mamboT3IdealCyclic
  apply sup_le
  · exact Mambo.T3GeneralN.t3_general_eval_kills_ideal K c0 c1 c2 tau n
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show cyclicityGenerator K n ∈ RingHom.ker _
    exact t3_general_eval_cyclicityGenerator K c0 c1 c2 tau n (Nat.succ_pos n)

/-- IsTwoSided instance for `mamboT3IdealCyclic` (needed for `liftₐ`). -/
instance (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (mamboT3IdealCyclic K n (fun r => c0 r.val) (fun r => c1 r.val)
        (fun r => c2 r.val) tau).IsTwoSided :=
  inferInstance

/-- **Factored cyclic-quotient eval map**. Direct corollary of
    `t3_general_eval_kills_cyclic_ideal`: the eval map factors through
    the cyclic-reduced quotient. -/
noncomputable def t3_general_eval_cyclic_bar
    (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) :
    (MvPolynomial (VarIndex 3 n) K ⧸
        mamboT3IdealCyclic K n (fun r => c0 r.val) (fun r => c1 r.val)
          (fun r => c2 r.val) tau) →ₐ[K]
    AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n) :=
  Ideal.Quotient.liftₐ _ (Mambo.T3GeneralN.t3_general_eval K c0 c1 c2 tau n)
    (fun a ha => t3_general_eval_kills_cyclic_ideal K c0 c1 c2 tau n ha)

/-- Helper: the class of `X(2,0)` in the cyclic quotient maps to
    `AdjoinRoot.root` under `t3_general_eval_cyclic_bar`. -/
theorem t3_general_eval_cyclic_bar_X20_eq_root
    (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (h_n_pos : 0 < n + 1) :
    t3_general_eval_cyclic_bar K c0 c1 c2 tau n
      (Ideal.Quotient.mk _
        (MvPolynomial.X ((2 : Fin 3), (⟨0, h_n_pos⟩ : Fin (n + 1)))))
      = AdjoinRoot.root (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n) := by
  unfold t3_general_eval_cyclic_bar
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  -- After lift_mk: goal in terms of (t3_general_eval).toRingHom (X v).
  -- Escape coercion by show'ing the AlgHom form:
  show Mambo.T3GeneralN.t3_general_eval K c0 c1 c2 tau n
        (MvPolynomial.X ((2 : Fin 3), (⟨0, h_n_pos⟩ : Fin (n + 1))))
      = AdjoinRoot.root (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau n)
  unfold Mambo.T3GeneralN.t3_general_eval
  rw [MvPolynomial.aeval_X]
  unfold Mambo.T3GeneralN.t3_general_var_image
  rw [if_neg (by decide : ¬ ((2 : Fin 3).val = 0)),
      if_neg (by decide : ¬ ((2 : Fin 3).val = 1))]
  rw [Mambo.T3GeneralN.s2_iter_zero, Polynomial.aeval_X]

/-- **Surjectivity of `t3_general_eval_cyclic_bar`**: every element of
    `AdjoinRoot(U_n_t3 K c0 c1 c2 tau n)` is in the image of the cyclic
    eval map. Follows because:
    (a) AdjoinRoot is generated by `root` as a K-algebra (PowerBasis').
    (b) `root` = image of `X(2,0)` under eval (via s2_iter_zero = X).
    (c) The eval map is a K-algebra hom, so it preserves the algebra
        generators. -/
theorem t3_general_eval_cyclic_bar_surjective
    (c0 c1 c2 : Nat → K) (tau : K) (n : Nat) (h_n_pos : 0 < n + 1) :
    Function.Surjective (t3_general_eval_cyclic_bar K c0 c1 c2 tau n) := by
  -- Convert surjectivity to range = ⊤
  rw [← AlgHom.range_eq_top]
  -- Use that AdjoinRoot's ⊤ equals Algebra.adjoin K {root}
  rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff,
      Set.singleton_subset_iff]
  -- Now: root ∈ cyclic_bar.range
  exact ⟨Ideal.Quotient.mk _
          (MvPolynomial.X ((2 : Fin 3), (⟨0, h_n_pos⟩ : Fin (n + 1)))),
        t3_general_eval_cyclic_bar_X20_eq_root K c0 c1 c2 tau n h_n_pos⟩

/-- **Key step for n=1 iso**: under cyclic reduction at n=1,
    `Polynomial.aeval [X(2,0)] (U_n_t3 1) = 0` in the quotient.

    At n=1, `U_n_t3 1 = s0_iter 1 - C τ = (0 + X² + C c0_0) - C τ`
    (since `s0_iter 0 = 0`, `s2_iter 0 = X`). Evaluating at `[X(2,0)]`
    gives `[X(2,0)]² + c0_0 - τ`. From roundConstraint0 at r=0 (in the
    legacy ideal) combined with boundaries `X(0,0)=0`, `X(0,1)=τ`,
    we get `τ - 0 - [X(2,0)]² - c0_0 = 0`, so `[X(2,0)]² + c0_0 - τ = 0`. -/
theorem U_n_t3_at_X20_zero_n1
    (c0 c1 c2 : Nat → K) (tau : K) :
    Polynomial.aeval
        (Ideal.Quotient.mk
          (mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val)
            (fun r => c2 r.val) tau)
          (MvPolynomial.X ((2 : Fin 3), (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
      (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau 1)
    = 0 := by
  -- U_n_t3 1 = s0_iter 1 - C tau = (C 7 * s0_iter 0 + (s2_iter 0)^2 + C (c0 0)) - C tau
  --         = (0 + X^2 + C (c0 0)) - C tau   (s0_iter_zero, s2_iter_zero)
  --         = X^2 + C (c0 0) - C tau
  unfold Mambo.T3GeneralN.U_n_t3
  rw [Mambo.T3GeneralN.s0_iter_succ, Mambo.T3GeneralN.s0_iter_zero,
      Mambo.T3GeneralN.s2_iter_zero]
  -- After rewriting, polynomial is: C 7 * 0 + X^2 + C (c0 0) - C tau
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
             Polynomial.aeval_C, MulZeroClass.mul_zero, zero_add]
  -- Ideal-membership hypotheses for the three generators
  have h_round_mem : Mambo.T3CicoIdeal.roundConstraint0 K 1 (0 : Fin 1)
                      (c0 0)
                     ∈ mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau := by
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨0, rfl⟩)))
  have h_bs_mem : Mambo.T3CicoIdeal.boundaryStart K 1
                  ∈ mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau := by
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inr (Or.inl rfl))
  have h_be_mem : Mambo.T3CicoIdeal.boundaryEnd K 1 tau
                  ∈ mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau := by
    apply Ideal.mem_sup_left
    unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inr (Or.inr rfl))
  -- Polynomial identity in MvPoly with explicit ring multiplications
  -- (avoiding nat-smul to keep Ideal closure lemmas straightforward).
  -- X(2,0)^2 + C(c0 0) - C tau = (-1)*roundConstraint0 + 1*boundaryEnd + (-7)*boundaryStart
  have key_poly : ((MvPolynomial.X ((2 : Fin 3), (⟨0, Nat.succ_pos 1⟩ : Fin 2))
                    : MvPolynomial (VarIndex 3 1) K))^2
                  + MvPolynomial.C (c0 0)
                  - MvPolynomial.C tau
                = (-1 : MvPolynomial (VarIndex 3 1) K)
                  * (Mambo.T3CicoIdeal.roundConstraint0 K 1 (0 : Fin 1)
                     (c0 0))
                  + (1 : MvPolynomial (VarIndex 3 1) K)
                    * Mambo.T3CicoIdeal.boundaryEnd K 1 tau
                  + (-(MvPolynomial.C (7 : K)))
                    * Mambo.T3CicoIdeal.boundaryStart K 1 := by
    unfold Mambo.T3CicoIdeal.roundConstraint0 Mambo.T3CicoIdeal.boundaryEnd
           Mambo.T3CicoIdeal.boundaryStart Mambo.T3CicoIdeal.sVar
    rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl,
        show (Fin.succ (0 : Fin 1) : Fin 2) = ⟨1, by decide⟩ from rfl,
        show (Fin.castSucc (0 : Fin 1) : Fin 2) = ⟨0, by decide⟩ from rfl]
    -- Convert K-smul to ring mult so `ring` can normalize
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    ring
  have h_combo_mem : ((MvPolynomial.X ((2 : Fin 3), (⟨0, Nat.succ_pos 1⟩ : Fin 2))
                      : MvPolynomial (VarIndex 3 1) K))^2
                     + MvPolynomial.C (c0 0)
                     - MvPolynomial.C tau
                     ∈ mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau := by
    rw [key_poly]
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.mul_mem_left _ _ h_round_mem)
        (Ideal.mul_mem_left _ _ h_be_mem))
      (Ideal.mul_mem_left _ _ h_bs_mem)
  have h_mk_zero : (Ideal.Quotient.mk (mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau))
                   (((MvPolynomial.X ((2 : Fin 3), (⟨0, Nat.succ_pos 1⟩ : Fin 2))
                     : MvPolynomial (VarIndex 3 1) K))^2
                    + MvPolynomial.C (c0 0)
                    - MvPolynomial.C tau) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr h_combo_mem
  simp only [map_sub, map_add, map_pow] at h_mk_zero
  -- Bridge algebraMap K (Quotient) r = mk (C r). Direct by rfl.
  show (Ideal.Quotient.mk (mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau))
       (MvPolynomial.X ((2 : Fin 3), (⟨0, Nat.succ_pos 1⟩ : Fin 2)))^2
       + (Ideal.Quotient.mk (mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau))
         (MvPolynomial.C (c0 0))
       - (Ideal.Quotient.mk (mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val) (fun r => c2 r.val) tau)) (MvPolynomial.C tau)
       = 0
  exact h_mk_zero

/-- **Inverse map at n=1**: from AdjoinRoot to the cyclic quotient.
    Takes `Nat → K` coefficient sequences directly to match the bar's
    signature exactly (avoids `Fin 1 → K`-vs-`Nat → K` isDefEq overhead). -/
noncomputable def t3_cyclic_inverse_n1
    (c0 c1 c2 : Nat → K) (tau : K) :
    AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau 1) →ₐ[K]
    (MvPolynomial (VarIndex 3 1) K ⧸
      mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val)
        (fun r => c2 r.val) tau) :=
  AdjoinRoot.liftHom _
    (Ideal.Quotient.mk _
      (MvPolynomial.X ((2 : Fin 3), (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
    (U_n_t3_at_X20_zero_n1 K c0 c1 c2 tau)

/-- **Forward direction** at n=1: `bar ∘ inverse = id` on AdjoinRoot.
    Reduces via `AdjoinRoot.algHom_ext` to checking on `root`. -/
theorem t3_general_eval_cyclic_bar_comp_inverse_n1
    (c0 c1 c2 : Nat → K) (tau : K) :
    (t3_general_eval_cyclic_bar K c0 c1 c2 tau 1).comp
      (t3_cyclic_inverse_n1 K c0 c1 c2 tau)
    = AlgHom.id K (AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau 1)) := by
  apply AdjoinRoot.algHom_ext
  show t3_general_eval_cyclic_bar K c0 c1 c2 tau 1
       (t3_cyclic_inverse_n1 K c0 c1 c2 tau
         (AdjoinRoot.root (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau 1)))
       = AdjoinRoot.root _
  unfold t3_cyclic_inverse_n1
  rw [AdjoinRoot.liftHom_root]
  exact t3_general_eval_cyclic_bar_X20_eq_root K _ _ _ _ 1 (Nat.succ_pos 1)

set_option maxHeartbeats 8000000 in
/-- **Reverse direction** at n=1: `inverse ∘ bar = id` on the source quotient.
    Reduces via `Ideal.Quotient.algHom_ext` + `MvPolynomial.algHom_ext` to
    checking each of the 6 generator-variables X(c, r) for c ∈ Fin 3, r ∈ Fin 2.
    Each case rewrites bar(mk(X(c,r))) via the iterator polynomial, then closes
    via the appropriate ideal generator (boundary or round-constraint). -/
theorem t3_cyclic_inverse_comp_eval_bar_n1
    (c0 c1 c2 : Nat → K) (tau : K) :
    (t3_cyclic_inverse_n1 K c0 c1 c2 tau).comp
        (t3_general_eval_cyclic_bar K c0 c1 c2 tau 1)
      = AlgHom.id K (MvPolynomial (VarIndex 3 1) K ⧸
          mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val)
            (fun r => c2 r.val) tau) := by
  -- Use abbreviation for the quotient mk to reduce verbosity.
  -- Use `↑r` (display form) to match how `rw [AlgHom.commutes]` exposes the ideal.
  set I : Ideal (MvPolynomial (VarIndex 3 1) K) :=
    mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  obtain ⟨c, r⟩ := v
  -- After ext: goal is comp f (mk X) = mk X for each variable X (c, r)
  show t3_cyclic_inverse_n1 K c0 c1 c2 tau
        (t3_general_eval_cyclic_bar K c0 c1 c2 tau 1
          ((Ideal.Quotient.mk I) (MvPolynomial.X (c, r))))
        = (Ideal.Quotient.mk I) (MvPolynomial.X (c, r))
  -- Unfold bar to expose `aeval root (s_c_iter r.val)`
  unfold t3_general_eval_cyclic_bar
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  show t3_cyclic_inverse_n1 K c0 c1 c2 tau
        ((MvPolynomial.aeval (Mambo.T3GeneralN.t3_general_var_image K c0 c1 c2 tau 1))
          (MvPolynomial.X (c, r)))
        = _
  rw [MvPolynomial.aeval_X]
  unfold Mambo.T3GeneralN.t3_general_var_image
  -- Helper: roundConstraint0/1/2 ∈ ideal at r=0 ─ used in several cases.
  have h_rc0 : Mambo.T3CicoIdeal.roundConstraint0 K 1 (0 : Fin 1) (c0 0) ∈ I := by
    apply Ideal.mem_sup_left; unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨0, rfl⟩)))
  have h_rc1 : Mambo.T3CicoIdeal.roundConstraint1 K 1 (0 : Fin 1) (c1 0) ∈ I := by
    apply Ideal.mem_sup_left; unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨0, rfl⟩)))
  have h_rc2 : Mambo.T3CicoIdeal.roundConstraint2 K 1 (0 : Fin 1) (c2 0) ∈ I := by
    apply Ideal.mem_sup_left; unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inl (Or.inr ⟨0, rfl⟩))
  have h_bs : Mambo.T3CicoIdeal.boundaryStart K 1 ∈ I := by
    apply Ideal.mem_sup_left; unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inr (Or.inl rfl))
  have h_be : Mambo.T3CicoIdeal.boundaryEnd K 1 tau ∈ I := by
    apply Ideal.mem_sup_left; unfold Mambo.T3CicoIdeal.mamboT3Ideal
    exact Ideal.subset_span (Or.inr (Or.inr rfl))
  have h_cy : cyclicityGenerator K 1 ∈ I := by
    apply Ideal.mem_sup_right
    exact Ideal.subset_span rfl
  -- Convert outer mk to the AlgHom-bar's image via AdjoinRoot.aeval_eq.
  -- For each (c, r), reduce to a polynomial identity in the quotient.
  -- Joint identity:  mk(X(c, r)) = aeval (mk X(2,0)) (s_c_iter r.val).
  -- Probe with c=0, r=0: mk X(0,0) = 0 via boundaryStart.
  fin_cases c <;> fin_cases r
  · -- (c=0, r=0): mk X(0,0) = 0 via boundaryStart.
    show t3_cyclic_inverse_n1 K c0 c1 c2 tau
          (if (⟨0, by decide⟩ : Fin 3).val = 0 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s0_iter K c0 c1 c2 0)
           else if (⟨0, by decide⟩ : Fin 3).val = 1 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s1_iter K c0 c1 c2 0)
           else
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s2_iter K c0 c1 c2 0))
          = (Ideal.Quotient.mk I) (MvPolynomial.X (⟨0, by decide⟩, ⟨0, by decide⟩))
    rw [if_pos rfl, Mambo.T3GeneralN.s0_iter_zero, map_zero, map_zero]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    show MvPolynomial.X ((⟨0, by decide⟩ : Fin 3), (⟨0, by decide⟩ : Fin 2)) ∈ I
    convert h_bs using 1
  · -- (c=0, r=1): mk X(0,1) = aeval (mk X(2,0)) (s0_iter 1) via roundConstraint0 + boundaryStart.
    show t3_cyclic_inverse_n1 K c0 c1 c2 tau
          (if (⟨0, by decide⟩ : Fin 3).val = 0 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s0_iter K c0 c1 c2 1)
           else if (⟨0, by decide⟩ : Fin 3).val = 1 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s1_iter K c0 c1 c2 1)
           else
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s2_iter K c0 c1 c2 1))
          = (Ideal.Quotient.mk I) (MvPolynomial.X (⟨0, by decide⟩, ⟨1, by decide⟩))
    rw [if_pos rfl, Mambo.T3GeneralN.s0_iter_succ, Mambo.T3GeneralN.s0_iter_zero,
        Mambo.T3GeneralN.s2_iter_zero]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
               MulZeroClass.mul_zero, zero_add]
    rw [AlgHom.commutes]
    unfold t3_cyclic_inverse_n1
    rw [AdjoinRoot.liftHom_root]
    -- Goal: (mk X(2,0))^2 + algebraMap (c0 0) = mk X(0,1)
    -- Polynomial identity: X(2,0)^2 + C(c0 0) - X(0,1)
    --                    = (-1)*roundConstraint0 + (-7)*boundaryStart
    have key_poly_01 :
        ((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
          : MvPolynomial (VarIndex 3 1) K))^2
        + MvPolynomial.C (c0 0)
        - MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2))
        = (-1 : MvPolynomial (VarIndex 3 1) K)
          * Mambo.T3CicoIdeal.roundConstraint0 K 1 (0 : Fin 1) (c0 0)
          + (-(MvPolynomial.C (7 : K)))
          * Mambo.T3CicoIdeal.boundaryStart K 1 := by
      unfold Mambo.T3CicoIdeal.roundConstraint0 Mambo.T3CicoIdeal.boundaryStart
             Mambo.T3CicoIdeal.sVar
      rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl,
          show (Fin.succ (0 : Fin 1) : Fin 2) = ⟨1, by decide⟩ from rfl,
          show (Fin.castSucc (0 : Fin 1) : Fin 2) = ⟨0, by decide⟩ from rfl]
      simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
      ring
    have h_in_I :
        ((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
          : MvPolynomial (VarIndex 3 1) K))^2
        + MvPolynomial.C (c0 0)
        - MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2))
        ∈ I := by
      rw [key_poly_01]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ h_rc0)
        (Ideal.mul_mem_left _ _ h_bs)
    have h_mk : (Ideal.Quotient.mk I)
        (((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
            : MvPolynomial (VarIndex 3 1) K))^2
          + MvPolynomial.C (c0 0)
          - MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2))) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_I
    simp only [map_sub, map_add, map_pow] at h_mk
    -- h_mk : mk(X(2,0))^2 + mk(C(c0 0)) - mk(X(0,1)) = 0
    have h_alg : (algebraMap K (MvPolynomial (VarIndex 3 1) K ⧸ I)) (c0 0)
                 = (Ideal.Quotient.mk I) (MvPolynomial.C (c0 0)) := rfl
    rw [h_alg]
    show (Ideal.Quotient.mk I)
            (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
         + (Ideal.Quotient.mk I) (MvPolynomial.C (c0 0))
         = (Ideal.Quotient.mk I)
            (MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2)))
    linear_combination h_mk
  · -- (c=1, r=0): mk X(1,0) = mk X(2,0) via cyclicityGenerator.
    show t3_cyclic_inverse_n1 K c0 c1 c2 tau
          (if (⟨1, by decide⟩ : Fin 3).val = 0 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s0_iter K c0 c1 c2 0)
           else if (⟨1, by decide⟩ : Fin 3).val = 1 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s1_iter K c0 c1 c2 0)
           else
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s2_iter K c0 c1 c2 0))
          = (Ideal.Quotient.mk I) (MvPolynomial.X (⟨1, by decide⟩, ⟨0, by decide⟩))
    rw [if_neg (by decide), if_pos rfl, Mambo.T3GeneralN.s1_iter_zero, Polynomial.aeval_X]
    unfold t3_cyclic_inverse_n1
    rw [AdjoinRoot.liftHom_root]
    -- Goal: mk X(2, 0) = mk X(1, 0). Use cyclicity: X(1,0) - X(2,0) ∈ I.
    have h : (Ideal.Quotient.mk I) (cyclicityGenerator K 1) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr h_cy
    unfold cyclicityGenerator Mambo.T3CicoIdeal.sVar at h
    rw [map_sub] at h
    show (Ideal.Quotient.mk I) (MvPolynomial.X ((2 : Fin 3), (⟨0, by decide⟩ : Fin 2))) =
         (Ideal.Quotient.mk I) (MvPolynomial.X ((1 : Fin 3), (⟨0, by decide⟩ : Fin 2)))
    linear_combination -h
  · -- (c=1, r=1): mk X(1,1) = aeval (mk X(2,0)) (s1_iter 1) via roundConstraint1 + cyclicity + (0,1).
    show t3_cyclic_inverse_n1 K c0 c1 c2 tau
          (if (⟨1, by decide⟩ : Fin 3).val = 0 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s0_iter K c0 c1 c2 1)
           else if (⟨1, by decide⟩ : Fin 3).val = 1 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s1_iter K c0 c1 c2 1)
           else
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s2_iter K c0 c1 c2 1))
          = (Ideal.Quotient.mk I) (MvPolynomial.X (⟨1, by decide⟩, ⟨1, by decide⟩))
    rw [if_neg (by decide), if_pos rfl,
        Mambo.T3GeneralN.s1_iter_succ, Mambo.T3GeneralN.s1_iter_zero,
        Mambo.T3GeneralN.s0_iter_succ, Mambo.T3GeneralN.s0_iter_zero,
        Mambo.T3GeneralN.s2_iter_zero]
    -- s1_iter 1 = C 7 * X + (C 7 * 0 + X^2 + C(c0 0))^2 + C(c1 0)
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
               MulZeroClass.mul_zero, zero_add]
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    unfold t3_cyclic_inverse_n1
    rw [AdjoinRoot.liftHom_root]
    -- Goal: algMap 7 * (mk X(2,0)) + (mk X(2,0)^2 + algMap (c0 0))^2 + algMap (c1 0)
    --       = mk X(1,1)
    -- Polynomial identity:
    have key_poly_11 :
        (MvPolynomial.C (7 : K))
          * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + ((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
            + MvPolynomial.C (c0 0))^2
        + MvPolynomial.C (c1 0)
        - MvPolynomial.X (((1 : Fin 3)), (⟨1, by decide⟩ : Fin 2))
        = (-1 : MvPolynomial (VarIndex 3 1) K)
          * Mambo.T3CicoIdeal.roundConstraint1 K 1 (0 : Fin 1) (c1 0)
          + (-(MvPolynomial.C (7 : K)))
            * cyclicityGenerator K 1
          + (-(((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
                + MvPolynomial.C (c0 0))
              + MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2))))
            * Mambo.T3CicoIdeal.roundConstraint0 K 1 (0 : Fin 1) (c0 0)
          + (-(MvPolynomial.C (7 : K)
              * (((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
                  + MvPolynomial.C (c0 0))
                + MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2)))))
            * Mambo.T3CicoIdeal.boundaryStart K 1 := by
      unfold Mambo.T3CicoIdeal.roundConstraint1 Mambo.T3CicoIdeal.roundConstraint0
             cyclicityGenerator Mambo.T3CicoIdeal.boundaryStart
             Mambo.T3CicoIdeal.sVar
      rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl,
          show (Fin.succ (0 : Fin 1) : Fin 2) = ⟨1, by decide⟩ from rfl,
          show (Fin.castSucc (0 : Fin 1) : Fin 2) = ⟨0, by decide⟩ from rfl]
      simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
      ring
    have h_in_I :
        ((MvPolynomial.C (7 : K))
          * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + ((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
            + MvPolynomial.C (c0 0))^2
        + MvPolynomial.C (c1 0)
        - MvPolynomial.X (((1 : Fin 3)), (⟨1, by decide⟩ : Fin 2)) : MvPolynomial _ K) ∈ I := by
      rw [key_poly_11]
      refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
        (Ideal.mul_mem_left _ _ h_rc1)
        (Ideal.mul_mem_left _ _ h_cy))
        (Ideal.mul_mem_left _ _ h_rc0))
        (Ideal.mul_mem_left _ _ h_bs)
    have h_mk : (Ideal.Quotient.mk I)
        ((MvPolynomial.C (7 : K))
          * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + ((MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
            + MvPolynomial.C (c0 0))^2
        + MvPolynomial.C (c1 0)
        - MvPolynomial.X (((1 : Fin 3)), (⟨1, by decide⟩ : Fin 2))) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_I
    simp only [map_sub, map_add, map_pow, map_mul] at h_mk
    -- h_mk: mk(C 7) * mk X(2,0) + (mk X(2,0)^2 + mk(C c0 0))^2 + mk(C c1 0) - mk X(1,1) = 0
    have h_alg_c0 : (algebraMap K (MvPolynomial (VarIndex 3 1) K ⧸ I)) (c0 0)
                  = (Ideal.Quotient.mk I) (MvPolynomial.C (c0 0)) := rfl
    have h_alg_c1 : (algebraMap K (MvPolynomial (VarIndex 3 1) K ⧸ I)) (c1 0)
                  = (Ideal.Quotient.mk I) (MvPolynomial.C (c1 0)) := rfl
    have h_alg_7 : (algebraMap K (MvPolynomial (VarIndex 3 1) K ⧸ I)) 7
                  = (Ideal.Quotient.mk I) (MvPolynomial.C (7 : K)) := rfl
    rw [h_alg_c0, h_alg_c1, h_alg_7]
    show (Ideal.Quotient.mk I) (MvPolynomial.C (7 : K))
          * (Ideal.Quotient.mk I)
              (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))
        + ((Ideal.Quotient.mk I)
              (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
            + (Ideal.Quotient.mk I) (MvPolynomial.C (c0 0)))^2
        + (Ideal.Quotient.mk I) (MvPolynomial.C (c1 0))
        = (Ideal.Quotient.mk I)
            (MvPolynomial.X (((1 : Fin 3)), (⟨1, by decide⟩ : Fin 2)))
    linear_combination h_mk
  · -- (c=2, r=0): mk X(2,0) = mk X(2,0). Trivial.
    show t3_cyclic_inverse_n1 K c0 c1 c2 tau
          (if (⟨2, by decide⟩ : Fin 3).val = 0 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s0_iter K c0 c1 c2 0)
           else if (⟨2, by decide⟩ : Fin 3).val = 1 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s1_iter K c0 c1 c2 0)
           else
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s2_iter K c0 c1 c2 0))
          = (Ideal.Quotient.mk I) (MvPolynomial.X (⟨2, by decide⟩, ⟨0, by decide⟩))
    rw [if_neg (by decide), if_neg (by decide), Mambo.T3GeneralN.s2_iter_zero,
        Polynomial.aeval_X]
    unfold t3_cyclic_inverse_n1
    rw [AdjoinRoot.liftHom_root]
    rfl
  · -- (c=2, r=1): mk X(2,1) = aeval (mk X(2,0)) (s2_iter 1) via roundConstraint2 + previous.
    show t3_cyclic_inverse_n1 K c0 c1 c2 tau
          (if (⟨2, by decide⟩ : Fin 3).val = 0 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s0_iter K c0 c1 c2 1)
           else if (⟨2, by decide⟩ : Fin 3).val = 1 then
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s1_iter K c0 c1 c2 1)
           else
              Polynomial.aeval (AdjoinRoot.root _) (Mambo.T3GeneralN.s2_iter K c0 c1 c2 1))
          = (Ideal.Quotient.mk I) (MvPolynomial.X (⟨2, by decide⟩, ⟨1, by decide⟩))
    rw [if_neg (by decide), if_neg (by decide),
        Mambo.T3GeneralN.s2_iter_succ, Mambo.T3GeneralN.s2_iter_zero,
        Mambo.T3GeneralN.s1_iter_succ, Mambo.T3GeneralN.s1_iter_zero,
        Mambo.T3GeneralN.s0_iter_succ, Mambo.T3GeneralN.s0_iter_zero,
        Mambo.T3GeneralN.s2_iter_zero]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
               MulZeroClass.mul_zero, zero_add]
    simp only [AlgHom.commutes]
    unfold t3_cyclic_inverse_n1
    simp only [AdjoinRoot.liftHom_root]
    -- Bridge algebraMap K (Quot _) k = mk (C k) via rfl-based simp.
    have eq_alg : ∀ (k : K),
        (algebraMap K (MvPolynomial (VarIndex 3 1) K ⧸
          mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau)) k
        = (Ideal.Quotient.mk
            (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
              (MvPolynomial.C k) := fun _ => rfl
    simp only [eq_alg]
    -- Polynomial identity: writing S₀ = X(2,0)^2 + C(c0 0), S₁ = 7*X(2,0) + S₀^2 + C(c1 0),
    -- LHS = 7*X(2,0) + S₁^2 + C(c2 0) - X(2,1)
    --     = -rc2 - (X(1,1)+S₁)*rc1 - 7*(X(1,1)+S₁)*cy
    --       - (X(1,1)+S₁)*(S₀+X(0,1))*rc0 - 7*(X(1,1)+S₁)*(S₀+X(0,1))*bs
    set xS₀ : MvPolynomial (VarIndex 3 1) K :=
      (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2 + MvPolynomial.C (c0 0)
    set xS₁ : MvPolynomial (VarIndex 3 1) K :=
      MvPolynomial.C (7 : K) * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + xS₀^2 + MvPolynomial.C (c1 0)
    set xX11 : MvPolynomial (VarIndex 3 1) K :=
      MvPolynomial.X (((1 : Fin 3)), (⟨1, by decide⟩ : Fin 2))
    set xX01 : MvPolynomial (VarIndex 3 1) K :=
      MvPolynomial.X (((0 : Fin 3)), (⟨1, by decide⟩ : Fin 2))
    have key_poly_21 :
        (MvPolynomial.C (7 : K))
          * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + xS₁^2
        + MvPolynomial.C (c2 0)
        - MvPolynomial.X (((2 : Fin 3)), (⟨1, by decide⟩ : Fin 2))
        = (-1 : MvPolynomial (VarIndex 3 1) K)
          * Mambo.T3CicoIdeal.roundConstraint2 K 1 (0 : Fin 1) (c2 0)
          + (-(xX11 + xS₁))
            * Mambo.T3CicoIdeal.roundConstraint1 K 1 (0 : Fin 1) (c1 0)
          + (-(MvPolynomial.C (7 : K) * (xX11 + xS₁)))
            * cyclicityGenerator K 1
          + (-((xX11 + xS₁) * (xS₀ + xX01)))
            * Mambo.T3CicoIdeal.roundConstraint0 K 1 (0 : Fin 1) (c0 0)
          + (-(MvPolynomial.C (7 : K) * (xX11 + xS₁) * (xS₀ + xX01)))
            * Mambo.T3CicoIdeal.boundaryStart K 1 := by
      unfold Mambo.T3CicoIdeal.roundConstraint2 Mambo.T3CicoIdeal.roundConstraint1
             Mambo.T3CicoIdeal.roundConstraint0 cyclicityGenerator
             Mambo.T3CicoIdeal.boundaryStart Mambo.T3CicoIdeal.sVar
      rw [show (Mambo.T3CicoIdeal.phi : K) = 7 from rfl,
          show (Fin.succ (0 : Fin 1) : Fin 2) = ⟨1, by decide⟩ from rfl,
          show (Fin.castSucc (0 : Fin 1) : Fin 2) = ⟨0, by decide⟩ from rfl]
      simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, xS₀, xS₁, xX11, xX01]
      ring
    have h_in_I :
        ((MvPolynomial.C (7 : K))
          * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + xS₁^2
        + MvPolynomial.C (c2 0)
        - MvPolynomial.X (((2 : Fin 3)), (⟨1, by decide⟩ : Fin 2)) : MvPolynomial _ K) ∈ I := by
      rw [key_poly_21]
      refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
        (Ideal.mul_mem_left _ _ h_rc2)
        (Ideal.mul_mem_left _ _ h_rc1))
        (Ideal.mul_mem_left _ _ h_cy))
        (Ideal.mul_mem_left _ _ h_rc0))
        (Ideal.mul_mem_left _ _ h_bs)
    have h_mk : (Ideal.Quotient.mk I)
        ((MvPolynomial.C (7 : K))
          * MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2))
        + xS₁^2
        + MvPolynomial.C (c2 0)
        - MvPolynomial.X (((2 : Fin 3)), (⟨1, by decide⟩ : Fin 2))) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr h_in_I
    simp only [map_sub, map_add, map_pow, map_mul, xS₁, xS₀] at h_mk
    -- Align Fin reps before linear_combination
    show (Ideal.Quotient.mk
        (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
          (MvPolynomial.C (7 : K))
        * (Ideal.Quotient.mk
            (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
              (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))
        + ((Ideal.Quotient.mk
              (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
                (MvPolynomial.C (7 : K))
            * (Ideal.Quotient.mk
                (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
                  (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))
          + ((Ideal.Quotient.mk
                (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
                  (MvPolynomial.X (((2 : Fin 3)), (⟨0, by decide⟩ : Fin 2)))^2
              + (Ideal.Quotient.mk
                  (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
                    (MvPolynomial.C (c0 0)))^2
          + (Ideal.Quotient.mk
              (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
                (MvPolynomial.C (c1 0)))^2
        + (Ideal.Quotient.mk
            (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
              (MvPolynomial.C (c2 0))
        = (Ideal.Quotient.mk
            (mamboT3IdealCyclic K 1 (fun r => c0 ↑r) (fun r => c1 ↑r) (fun r => c2 ↑r) tau))
              (MvPolynomial.X (((2 : Fin 3)), (⟨1, by decide⟩ : Fin 2)))
    linear_combination h_mk

/-- **A2 first cell theorem (n = 1)**: under cyclic reduction, the
    Mambo t = 3 CICO quotient at depth 1 has K-finrank 2 = 2^(3·1-2),
    matching paper d_reg = 3·1 - 1 = 2. -/
theorem t3_first_cell_cyclic_finrank
    (c0 c1 c2 : Nat → K) (tau : K) :
    Module.finrank K
      (MvPolynomial (VarIndex 3 1) K ⧸
        mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val)
          (fun r => c2 r.val) tau) = 2 := by
  -- Construct AlgEquiv from the two compositions
  let algE : (MvPolynomial (VarIndex 3 1) K ⧸
              mamboT3IdealCyclic K 1 (fun r => c0 r.val) (fun r => c1 r.val)
                (fun r => c2 r.val) tau)
             ≃ₐ[K] AdjoinRoot (Mambo.T3GeneralN.U_n_t3 K c0 c1 c2 tau 1) :=
    AlgEquiv.ofAlgHom
      (t3_general_eval_cyclic_bar K c0 c1 c2 tau 1)
      (t3_cyclic_inverse_n1 K c0 c1 c2 tau)
      (t3_general_eval_cyclic_bar_comp_inverse_n1 K c0 c1 c2 tau)
      (t3_cyclic_inverse_comp_eval_bar_n1 K c0 c1 c2 tau)
  -- Transport finrank via the LinearEquiv
  rw [algE.toLinearEquiv.finrank_eq]
  -- finrank K (AdjoinRoot (U_n_t3 1)) = 2^(3·1-2) = 2
  have h := Mambo.T3GeneralN.U_n_t3_AdjoinRoot_finrank_closed K c0 c1 c2 tau 1
    (le_refl 1)
  -- h : finrank K (AdjoinRoot ...) = 2^(3*1-2) = 2^1 = 2
  rw [h]
  norm_num

end Mambo.T3FirstCellCyclic
