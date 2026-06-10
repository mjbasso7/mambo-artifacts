import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mambo.MathlibBridgeDim

/-!
# Mambo — Multi-Variable Boolean Quotient Dimension

Extends the single-variable dim-2 result from `Mambo.MathlibBridgeDim`
to multi-variable: the Boolean quotient

  K[X_0, ..., X_{n-1}] / (X_0² − X_0, ..., X_{n-1}² − X_{n-1})

has dimension `2^n` over the base field `K`.

This is the full B.1 dimension claim at multi-variable level: each Boolean
residual variable contributes a factor `(1+z)` to the Hilbert series, so
`n` independent ones contribute `(1+z)^n`, giving total dimension `2^n`
at `z = 1`.

**Status:** fully proven for all `n` (2026-05-17, zero sorrys, std
axioms only). Induction-on-n proof uses `MvPolynomial.finSuccEquiv`
to peel one variable, then `Ideal.quotientEquivAlg` +
`DoubleQuot.quotQuotEquivQuotSupₐ` +
`polynomialQuotientEquivQuotientPolynomial` + `AdjoinRoot.powerBasis'`
+ the tower rule `Module.finrank_mul_finrank`.
-/

namespace Mambo.MathlibBridge.MultiDim

open MvPolynomial

variable (K : Type*) [Field K]

/-- The Boolean polynomial for variable `X_i` in `MvPolynomial (Fin n) K`. -/
noncomputable def boolGen (n : Nat) (i : Fin n) : MvPolynomial (Fin n) K :=
  let x : MvPolynomial (Fin n) K := X i
  x * x - x

/-- The Boolean ideal: span of `{X_i² − X_i : i ∈ Fin n}`. -/
noncomputable def boolIdeal (n : Nat) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range (boolGen K n))

/-- `boolIdeal K n` is a proper ideal (does not contain `1`).
    Proof: every generator vanishes at the all-zero point, so the entire ideal lies
    in the kernel of `eval 0`. But `eval 0 1 = 1 ≠ 0`, so `1 ∉ boolIdeal`. -/
theorem boolIdeal_ne_top (n : Nat) : boolIdeal K n ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one]
  intro h_one
  have h_le : boolIdeal K n ≤ RingHom.ker (MvPolynomial.eval (fun _ => (0 : K))) := by
    rw [boolIdeal, Ideal.span_le]
    rintro y ⟨i, rfl⟩
    unfold boolGen
    simp [RingHom.mem_ker]
  have := h_le h_one
  simp [RingHom.mem_ker] at this

/-- Quotient by a proper Boolean ideal is nontrivial. -/
instance boolQuot_nontrivial (n : Nat) :
    Nontrivial (MvPolynomial (Fin n) K ⧸ boolIdeal K n) :=
  Submodule.Quotient.nontrivial_of_lt_top _ (lt_top_iff_ne_top.mpr (boolIdeal_ne_top K n))

set_option maxHeartbeats 1600000 in
/-- **Main theorem (statement):** the Boolean quotient
    `MvPolynomial (Fin n) K ⧸ boolIdeal K n` has dimension `2^n` over K.

    Proof strategy: induction on `n`.
    - Base `n = 0`: empty product, `MvPolynomial (Fin 0) K ≃ K`, ideal is
      `⊥`, quotient `K`, dim `1 = 2^0`.
    - Step `n → n+1`: via `MvPolynomial.finSuccEquiv`, peel off one variable
      and combine the single-variable result
      `Mambo.MathlibBridge.Dim.boolQuot_finrank` with the inductive hypothesis
      via tensor / `Polynomial.lift` machinery.

    The inductive step uses DoubleQuot + polynomialQuotientEquivQuotientPolynomial
    + AdjoinRoot tower rule. Axiom dependency: only the 3 standard Lean axioms
    (propext, Classical.choice, Quot.sound). -/
theorem boolQuot_finrank (n : Nat) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ boolIdeal K n) = 2 ^ n := by
  induction n with
  | zero =>
    -- At n = 0: Fin 0 is empty, so the boolGen function has empty range,
    -- so boolIdeal = Ideal.span ∅ = ⊥, so the quotient is the original ring,
    -- which is MvPolynomial (Fin 0) K ≃[K] K, so finrank = 1 = 2^0.
    have h_range : Set.range (boolGen K 0) = ∅ := by
      apply Set.range_eq_empty
    have h_ideal : boolIdeal K 0 = ⊥ := by
      unfold boolIdeal
      rw [h_range, Ideal.span_empty]
    have h_iso : (MvPolynomial (Fin 0) K ⧸ boolIdeal K 0) ≃ₗ[K] K := by
      rw [h_ideal]
      exact (Submodule.quotEquivOfEqBot ⊥ rfl).trans
            (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toLinearEquiv
    rw [h_iso.finrank_eq, Module.finrank_self, pow_zero]
  | succ n ih =>
    -- Strategy: build the algebra-equiv from `MvP (Fin (n+1)) K ⧸ boolIdeal K (n+1)`
    -- to `Polynomial (MvP (Fin n) K) ⧸ J` via `Ideal.quotientEquivAlg`, then transfer
    -- finrank via `LinearEquiv.finrank_eq`, then compute the polynomial-quotient dim.

    -- Step A: define the target ideal J in Polynomial (MvP (Fin n) K)
    let J : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
      Ideal.span {(Polynomial.X * Polynomial.X - Polynomial.X :
        Polynomial (MvPolynomial (Fin n) K))} ⊔
      (boolIdeal K n).map Polynomial.C

    -- Step B (claim): under `finSuccEquiv K n`, the ideal maps as expected.
    -- This requires unfolding `Ideal.map` on the span and computing the image of
    -- each generator. The image of `boolGen K (n+1) 0` is `Polynomial.X² − X`;
    -- the image of `boolGen K (n+1) (Fin.succ j)` is `Polynomial.C (boolGen K n j)`.
    --
    -- Foundation lemmas (proven, no sorry): per-generator image equations under
    -- finSuccEquiv. These reduce the h_map sorry to an ideal-span equality which
    -- is one mathlib-API-navigation step away (Ideal.map_span + Ideal.span_union
    -- + the antisymmetric image argument).
    have eq_zero :
        (MvPolynomial.finSuccEquiv K n).toRingEquiv (boolGen K (n+1) 0)
          = Polynomial.X * Polynomial.X - Polynomial.X := by
      unfold boolGen
      simp [MvPolynomial.finSuccEquiv_X_zero]
    have eq_succ : ∀ (j : Fin n),
        (MvPolynomial.finSuccEquiv K n).toRingEquiv (boolGen K (n+1) j.succ)
          = Polynomial.C (boolGen K n j) := by
      intro j
      unfold boolGen
      simp [MvPolynomial.finSuccEquiv_X_succ]
    have h_map : (boolIdeal K (n+1)).map (MvPolynomial.finSuccEquiv K n).toRingEquiv
                  = J := by
      apply le_antisymm
      · -- ⊆: every generator's image lands in J.
        rw [boolIdeal, Ideal.map_span, Ideal.span_le]
        rintro y ⟨x, ⟨i, rfl⟩, rfl⟩
        -- y = finSuccEquiv (boolGen K (n+1) i), case split on i
        refine Fin.cases ?_ ?_ i
        · -- i = 0: rewrite via eq_zero, land in ⟨X²-X⟩ which is in J
          rw [eq_zero]
          exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
        · -- i = Fin.succ j: rewrite via eq_succ, land in C-mapped piece
          intro j
          rw [eq_succ j]
          refine Ideal.mem_sup_right ?_
          exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
      · -- ⊇: each generator of J comes from an element of boolIdeal K (n+1).
        refine sup_le ?_ ?_
        · -- ⟨X²-X⟩ ⊆ image: X²-X = finSuccEquiv (boolGen K (n+1) 0) which is in the image.
          rw [Ideal.span_singleton_le_iff_mem]
          exact eq_zero ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨0, rfl⟩)
        · -- C-mapped piece ⊆ image: convert to comap-form then check generators
          rw [Ideal.map_le_iff_le_comap, boolIdeal, Ideal.span_le]
          rintro y ⟨j, rfl⟩
          show Polynomial.C (boolGen K n j) ∈ Ideal.map (MvPolynomial.finSuccEquiv K n).toRingEquiv (boolIdeal K (n+1))
          exact eq_succ j ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j.succ, rfl⟩)

    -- Step C: quotient compatibility — via `Ideal.quotientEquivAlg` + h_map
    have h_iso : (MvPolynomial (Fin (n+1)) K ⧸ boolIdeal K (n+1))
                  ≃ₐ[K]
                 (Polynomial (MvPolynomial (Fin n) K) ⧸ J) :=
      Ideal.quotientEquivAlg (boolIdeal K (n+1)) J
        (MvPolynomial.finSuccEquiv K n) h_map.symm

    -- Step D: transfer finrank
    rw [h_iso.toLinearEquiv.finrank_eq]

    -- Step E: compute finrank of `Polynomial (MvP (Fin n) K) ⧸ J` = 2^(n+1).
    -- Helpers (boolIdeal_ne_top + boolQuot_nontrivial instance) now provide
    -- the Nontrivial typeclass for the quotient ring, unblocking degree/monic lemmas.
    set R' := MvPolynomial (Fin n) K ⧸ boolIdeal K n with hR'
    -- X²-X in R'[X] equals X^2 - X.
    have hX_eq : (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R')
        = Polynomial.X ^ 2 - Polynomial.X := by ring
    -- natDegree of X²-X is 2.
    have hX_natDegree : (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R').natDegree = 2 := by
      rw [hX_eq, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow 2
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        decide
    -- X²-X is monic.
    have hX_monic : (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R').Monic := by
      rw [hX_eq]
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      decide
    -- AdjoinRoot of monic X²-X has R'-finrank = natDegree = 2.
    have hAdj_finrank :
        Module.finrank R'
          (AdjoinRoot (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R')) = 2 := by
      rw [PowerBasis.finrank (AdjoinRoot.powerBasis' hX_monic)]
      simp [AdjoinRoot.powerBasis'_dim, hX_natDegree]
    -- PowerBasis gives Module.Free instance for AdjoinRoot over R'.
    haveI : Module.Free R'
        (AdjoinRoot (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R')) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' hX_monic).basis
    -- Tower-rule scalar tower K → R' → AdjoinRoot, derivable from algebra chain.
    haveI : IsScalarTower K R'
        (AdjoinRoot (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R')) :=
      inferInstance
    -- Tower rule: K-finrank of AdjoinRoot = (K-finrank R') · (R'-finrank AdjoinRoot) = 2^n · 2 = 2^(n+1).
    have hAdj_K_finrank :
        Module.finrank K
          (AdjoinRoot (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R'))
        = 2 ^ (n+1) := by
      rw [← Module.finrank_mul_finrank K R' _, ih, hAdj_finrank]
      ring
    -- Bridge (Polynomial R / J) finrank to AdjoinRoot finrank via DoubleQuot + polyQuot iso.
    -- Step 1: J = (map C I) ⊔ ⟨X²-X⟩. DoubleQuot rewrites this two-step quotient.
    -- Step 2: Polynomial R / (map C I) ≃ Polynomial R' (polynomialQuotientEquivQuotientPolynomial).
    -- Step 3: lift the X²-X quotient through; lands at Polynomial R' / ⟨X²-X⟩ = AdjoinRoot (X²-X) def.
    -- The composition is a RingEquiv between K-algebras; lifts to LinearEquiv K via algebra structure.
    have h_chain : (Polynomial (MvPolynomial (Fin n) K) ⧸ J) ≃ₗ[K]
        AdjoinRoot (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R') := by
      -- DoubleQuot iso: A / (I ⊔ J') ≃ₐ[K] (A / I) / J'.map (mkₐ K I)
      let I₁ : Ideal (Polynomial (MvPolynomial (Fin n) K)) := (boolIdeal K n).map Polynomial.C
      let J' : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X}
      -- J = J' ⊔ I₁ = I₁ ⊔ J' (sup commutes)
      have hJ_eq : J = I₁ ⊔ J' := by
        show _ ⊔ _ = _ ⊔ _
        rw [sup_comm]
      -- Step 1 (alg-equiv): rewrite J then apply DoubleQuot to split A / (I₁ ⊔ J').
      let step1 : (Polynomial (MvPolynomial (Fin n) K) ⧸ J) ≃ₐ[K]
          ((Polynomial (MvPolynomial (Fin n) K) ⧸ I₁) ⧸
            J'.map (Ideal.Quotient.mkₐ K I₁)) :=
        (Ideal.quotientEquivAlgOfEq K hJ_eq).trans
          (DoubleQuot.quotQuotEquivQuotSupₐ K I₁ J').symm
      -- Step 2 attempt: lift polynomialQuotientEquivQuotientPolynomial RingEquiv to AlgEquiv
      -- using the polynomial+quotient simp lemmas to discharge K-scalar compatibility.
      -- Step 2: lift polynomialQuotientEquivQuotientPolynomial.symm to AlgEquiv.
      -- K-scalar compat: trace through `algebraMap K = Quotient.mk ∘ C ∘ algebraMap K R`
      -- and use polynomialQuotientEquivQuotientPolynomial_symm_mk to get f.map (Quotient.mk I).
      let step2 :
          (Polynomial (MvPolynomial (Fin n) K) ⧸ I₁) ≃ₐ[K] Polynomial R' :=
        AlgEquiv.ofRingEquiv
          (f := ((boolIdeal K n).polynomialQuotientEquivQuotientPolynomial).symm)
          (fun k => by
            show ((boolIdeal K n).polynomialQuotientEquivQuotientPolynomial).symm
                  (Ideal.Quotient.mk _ (Polynomial.C (algebraMap K _ k)))
                = Polynomial.C (algebraMap K _ k)
            rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]
            rfl)
      -- Step 3 prep: the underlying RingEquiv ∘ mkₐ_I₁ = Polynomial.mapRingHom (mk I)
      -- Prove on the bare RingEquiv first to avoid forcing the elaborator to unfold
      -- the AlgEquiv.ofRingEquiv wrapper inside `step2`.
      have h_comp_raw :
          (((boolIdeal K n).polynomialQuotientEquivQuotientPolynomial).symm :
              (Polynomial (MvPolynomial (Fin n) K) ⧸ I₁) →+* Polynomial R').comp
                (Ideal.Quotient.mk I₁ : _ →+* _)
            = Polynomial.mapRingHom (Ideal.Quotient.mk (boolIdeal K n)) := by
        apply Polynomial.ringHom_ext
        · intro a
          show ((boolIdeal K n).polynomialQuotientEquivQuotientPolynomial.symm)
                  ((Ideal.Quotient.mk ((boolIdeal K n).map Polynomial.C)) (Polynomial.C a))
              = (Polynomial.mapRingHom (Ideal.Quotient.mk (boolIdeal K n))) (Polynomial.C a)
          rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C,
              Polynomial.coe_mapRingHom, Polynomial.map_C]
        · show ((boolIdeal K n).polynomialQuotientEquivQuotientPolynomial.symm)
                  ((Ideal.Quotient.mk ((boolIdeal K n).map Polynomial.C)) Polynomial.X)
              = (Polynomial.mapRingHom (Ideal.Quotient.mk (boolIdeal K n))) Polynomial.X
          rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_X,
              Polynomial.coe_mapRingHom, Polynomial.map_X]
      -- Promote: step2 underlying RingHom = polynomialQuotientEquivQuotientPolynomial.symm RingHom
      -- (true by defeq through AlgEquiv.ofRingEquiv).
      have h_comp : (step2 : Polynomial (MvPolynomial (Fin n) K) ⧸ I₁ →+* Polynomial R').comp
                      (Ideal.Quotient.mkₐ K I₁ : _ →+* _)
                  = Polynomial.mapRingHom (Ideal.Quotient.mk (boolIdeal K n)) := h_comp_raw
      -- Image of J' = span{X²-X} under the composite RingHom equals span{X²-X} in Polynomial R'.
      have h_J'_image :
          (J' : Ideal _).map (Polynomial.mapRingHom (Ideal.Quotient.mk (boolIdeal K n)))
            = Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X} := by
        show (Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X}).map
                (Polynomial.mapRingHom (Ideal.Quotient.mk (boolIdeal K n)))
              = Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X}
        rw [Ideal.map_span]
        congr 1
        ext y
        simp only [Set.mem_image, Set.mem_singleton_iff, Polynomial.coe_mapRingHom]
        constructor
        · rintro ⟨_, rfl, hy⟩
          rw [← hy]
          simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X]
        · rintro rfl
          exact ⟨_, rfl, by simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X]⟩
      -- Bridge AlgHom mkₐ to RingHom mk (they are defeq on the underlying function).
      have h_mkₐ_eq_mk : (Ideal.Quotient.mkₐ K I₁ :
          Polynomial (MvPolynomial (Fin n) K) →+* (Polynomial (MvPolynomial (Fin n) K) ⧸ I₁))
            = Ideal.Quotient.mk I₁ := rfl
      have h_step3_eq : (Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X} :
          Ideal (Polynomial R')) =
          (J'.map (Ideal.Quotient.mkₐ K I₁)).map (step2 : _ →+* _) := by
        -- Replace AlgHom-form .map with RingHom-form .map so map_map applies.
        change Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X}
            = ((J' : Ideal _).map (Ideal.Quotient.mk I₁ : _ →+* _)).map
                (((boolIdeal K n).polynomialQuotientEquivQuotientPolynomial).symm :
                  _ →+* Polynomial R')
        rw [Ideal.map_map, h_comp_raw, h_J'_image]
      -- Two-sided instance (commutative ring): needed by Ideal.quotientEquivAlg.
      haveI : (J'.map (Ideal.Quotient.mkₐ K I₁)).IsTwoSided := inferInstance
      haveI : (Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X} :
          Ideal (Polynomial R')).IsTwoSided := inferInstance
      -- Step 3: (Polynomial _ ⧸ I₁) ⧸ J'.map mkₐ_I₁  ≃ₐ[K]  Polynomial R' ⧸ span{X²-X}
      let step3 :
          ((Polynomial (MvPolynomial (Fin n) K) ⧸ I₁) ⧸
              J'.map (Ideal.Quotient.mkₐ K I₁))
            ≃ₐ[K]
          (Polynomial R' ⧸
              (Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X} : Ideal (Polynomial R'))) :=
        Ideal.quotientEquivAlg (J'.map (Ideal.Quotient.mkₐ K I₁))
          (Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X}) step2 h_step3_eq
      -- Step 4: AdjoinRoot (X²-X) is defeq to Polynomial R' ⧸ span{X²-X}.
      let step4 :
          (Polynomial R' ⧸
              (Ideal.span {Polynomial.X * Polynomial.X - Polynomial.X} : Ideal (Polynomial R')))
            ≃ₐ[K]
          AdjoinRoot (Polynomial.X * Polynomial.X - Polynomial.X : Polynomial R') :=
        AlgEquiv.refl
      exact (step1.trans (step3.trans step4)).toLinearEquiv
    -- Transfer finrank via the K-linear equiv and reuse hAdj_K_finrank.
    rw [h_chain.finrank_eq, hAdj_K_finrank]

/-! ### Explicit small-n cases via reduction to single-variable dim=2

Each small-n cell is reduced to the proven single-variable result
`Mambo.MathlibBridge.Dim.boolQuot_finrank` together with the appropriate
mathlib isomorphism. -/

/-- **n = 1 case (fully proven):** the single-variable Boolean quotient
    in `MvPolynomial` types has dimension 2 over K.

    Proof: via the chain of K-algebra isos
      `MvPolynomial (Fin 1) K  ≃  Polynomial (MvPolynomial (Fin 0) K)
                              ≃  Polynomial K`
    The Boolean ideal `(X 0 * (X 0 - 1))` maps to the corresponding
    single-variable ideal `(X * (X - 1))` in `Polynomial K`, whose
    `AdjoinRoot` quotient has dimension 2 by
    `Mambo.MathlibBridge.Dim.boolQuot_finrank`. -/
theorem boolQuot_finrank_one :
    Module.finrank K (MvPolynomial (Fin 1) K ⧸ boolIdeal K 1) = 2 := by
  -- This follows from boolQuot_finrank with n = 1; deferred until the
  -- general inductive step is discharged. Stated separately to mark the
  -- target value (= 2 = 2^1) explicitly.
  have h := boolQuot_finrank K 1
  rw [show (2 : Nat)^1 = 2 from rfl] at h
  exact h

/-- **n = 2 case (fully proven):** dimension 4 = 2². -/
theorem boolQuot_finrank_two :
    Module.finrank K (MvPolynomial (Fin 2) K ⧸ boolIdeal K 2) = 4 := by
  have h := boolQuot_finrank K 2
  rw [show (2 : Nat)^2 = 4 from rfl] at h
  exact h

/-- **n = 3 case (fully proven):** dimension 8 = 2³. -/
theorem boolQuot_finrank_three :
    Module.finrank K (MvPolynomial (Fin 3) K ⧸ boolIdeal K 3) = 8 := by
  have h := boolQuot_finrank K 3
  rw [show (2 : Nat)^3 = 8 from rfl] at h
  exact h

/-- **n = 4 case (fully proven):** dimension 16 = 2⁴. -/
theorem boolQuot_finrank_four :
    Module.finrank K (MvPolynomial (Fin 4) K ⧸ boolIdeal K 4) = 16 := by
  have h := boolQuot_finrank K 4
  rw [show (2 : Nat)^4 = 16 from rfl] at h
  exact h

/-- **n = 5 case (fully proven):** dimension 32 = 2⁵. -/
theorem boolQuot_finrank_five :
    Module.finrank K (MvPolynomial (Fin 5) K ⧸ boolIdeal K 5) = 32 := by
  have h := boolQuot_finrank K 5
  rw [show (2 : Nat)^5 = 32 from rfl] at h
  exact h

/-- **n = 10 case (fully proven):** dimension 1024 = 2¹⁰. -/
theorem boolQuot_finrank_ten :
    Module.finrank K (MvPolynomial (Fin 10) K ⧸ boolIdeal K 10) = 1024 := by
  have h := boolQuot_finrank K 10
  rw [show (2 : Nat)^10 = 1024 from rfl] at h
  exact h

end Mambo.MathlibBridge.MultiDim
