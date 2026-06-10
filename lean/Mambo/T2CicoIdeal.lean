import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mambo.B2Enumeration
import Mambo.DegreeGrowth

/-!
# Mambo t = 2 CICO Ideal (Paper Coupled-Sequential Round)

Formalizes the paper's t = 2 Mambo CICO ideal using the canonical
coupled-sequential round from `mambo_tosc_2026.tex` lines 316-319:

  θ' = φ·θ + ψ²    + c_i      (eq:theta)
  ψ' = φ·ψ + (θ')² + d_i      (eq:psi)

The defining feature: ψ' uses the FRESHLY COMPUTED θ' (eq:psi reads
the just-updated θ' on the RHS), not the original θ. This is the
"sequential coupling" the paper emphasizes (line 320-323).

NOTE: `Mambo.MamboIdeal.roundConstraint` encodes a DIFFERENT variant
(uses `s_prev = X (c-1, r.castSucc)`, i.e., previous-round value). That
"transposed" form is convenient for B.2 enumeration accounting but
gives a different Hilbert series than the paper's coupled-sequential.
For the paper-grade `dim K (R/I) = 2^{2n-1}` (Thm `thm:hilb_closed`)
we use the coupled-sequential round encoded here.

This file is t = 2 specific (just 2 cells); the wider-state t ≥ 3
generalization (`prop:wider_alfom`) needs its own coupled-sequential
encoding.
-/

namespace Mambo.T2CicoIdeal

open MvPolynomial Mambo.B2Enumeration

variable (K : Type*) [Field K]

/-- A t = 2 Mambo state variable: `s_{c, r}` for cell `c ∈ {0, 1}` and
    round `r ∈ {0, ..., n}`. Wraps `MvPolynomial.X` over `VarIndex 2 n`. -/
noncomputable def sVar (n : Nat) (c : Fin 2) (r : Fin (n + 1)) :
    MvPolynomial (VarIndex 2 n) K :=
  X (c, r)

/-- Mambo multiplier φ = 7 (paper default). -/
def phi : Nat := 7

/-- Coupled-sequential round constraint at cell 0 (θ' update):
    `s_{0, r+1} = φ · s_{0, r} + s_{1, r}² + c_r`.
    As a polynomial in the ideal: `s_{0, r+1} − φ·s_{0, r} − s_{1, r}² − c_r`. -/
noncomputable def roundConstraintTheta (n : Nat) (r : Fin n) (c_r : K) :
    MvPolynomial (VarIndex 2 n) K :=
  sVar K n 0 r.succ - (phi : K) • sVar K n 0 r.castSucc
    - sVar K n 1 r.castSucc * sVar K n 1 r.castSucc - C c_r

/-- Coupled-sequential round constraint at cell 1 (ψ' update):
    `s_{1, r+1} = φ · s_{1, r} + (s_{0, r+1})² + d_r`.
    Crucially uses the FRESHLY COMPUTED `s_{0, r+1}` (paper line 320).
    As a polynomial in the ideal:
    `s_{1, r+1} − φ·s_{1, r} − (s_{0, r+1})² − d_r`. -/
noncomputable def roundConstraintPsi (n : Nat) (r : Fin n) (d_r : K) :
    MvPolynomial (VarIndex 2 n) K :=
  sVar K n 1 r.succ - (phi : K) • sVar K n 1 r.castSucc
    - sVar K n 0 r.succ * sVar K n 0 r.succ - C d_r

/-- Boundary constraint at start: `s_{0, 0} = 0`. -/
noncomputable def boundaryStart (n : Nat) : MvPolynomial (VarIndex 2 n) K :=
  sVar K n 0 ⟨0, Nat.succ_pos n⟩

/-- Boundary constraint at end: `s_{0, n} = τ` (target).
    Polynomial form: `s_{0, n} − C τ`. -/
noncomputable def boundaryEnd (n : Nat) (tau : K) : MvPolynomial (VarIndex 2 n) K :=
  sVar K n 0 ⟨n, Nat.lt_succ_self n⟩ - C tau

/-- The paper's t = 2 Mambo CICO ideal: span of all round constraints
    (θ and ψ updates for r ∈ Fin n) plus the two boundary constraints. -/
noncomputable def mamboT2Ideal (n : Nat) (c_seq d_seq : Fin n → K) (tau : K) :
    Ideal (MvPolynomial (VarIndex 2 n) K) :=
  Ideal.span (
    Set.range (fun r : Fin n => roundConstraintTheta K n r (c_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraintPsi K n r (d_seq r))
    ∪ {boundaryStart K n, boundaryEnd K n tau})

/-! ### t = 2 n = 1 dim theorem (smallest non-trivial CICO case)

The smallest n ≥ 1 case of paper Thm `thm:hilb_closed`. Expected dim:
2^{2·1−1} = 2.

After eliminating s_{0,0} = 0 (boundary start), s_{0,1} = τ (boundary
end), and substituting via the θ-round constraint, we get
`s_{1,0}^2 = τ − c_0` in the quotient. The ψ-round constraint
then determines s_{1,1} = 7·s_{1,0} + τ² + d_0 (no extra restriction).

So the quotient ring is K-algebra-isomorphic to `K[X] / (X² − C(τ − c_0))`,
which is `AdjoinRoot (X² − C(τ − c_0))`. By
`AdjoinRoot.powerBasis'` applied to the monic degree-2 polynomial,
this has K-finrank 2.

The fact that `s_{1,0}^2 − C(τ − c_0)` lies in `mamboT2Ideal 1 c d τ`:
    `s_{1,0}^2 − C(τ − c_0)`
  = `−(θ-constraint) + (boundary_end) − 7·(boundary_start)`
  = `−(s_{0,1} − 7·s_{0,0} − s_{1,0}^2 − C c_0)
      + (s_{0,1} − C τ) − 7·s_{0,0}`
  = `s_{1,0}^2 + C c_0 − C τ`
  = `s_{1,0}^2 − C(τ − c_0)`. ✓
-/

/-- The defining polynomial of the t = 2 n = 1 CICO elimination:
    `X² − C(τ − c_0)`. -/
noncomputable def t2_n1_defining_poly (c_0 tau : K) : Polynomial K :=
  Polynomial.X ^ 2 - Polynomial.C (tau - c_0)

/-- The defining polynomial is monic of natDegree 2. -/
theorem t2_n1_defining_poly_monic (c_0 tau : K) :
    (t2_n1_defining_poly K c_0 tau).Monic := by
  unfold t2_n1_defining_poly
  exact Polynomial.monic_X_pow_sub_C (tau - c_0) (by decide)

theorem t2_n1_defining_poly_natDegree (c_0 tau : K) :
    (t2_n1_defining_poly K c_0 tau).natDegree = 2 := by
  unfold t2_n1_defining_poly
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 2
  · rw [Polynomial.natDegree_X_pow]
    have h : (Polynomial.C (tau - c_0)).natDegree = 0 := Polynomial.natDegree_C _
    omega

/-- **AdjoinRoot of the t = 2 n = 1 defining polynomial has K-finrank 2
    (assuming K is a field).**
    This is the AdjoinRoot half of the t = 2 n = 1 dim theorem; the
    full Mambo iso step (showing the quotient is iso to this AdjoinRoot)
    is the structural CICO lift work for the next phase. -/
theorem t2_n1_AdjoinRoot_finrank (c_0 tau : K) :
    Module.finrank K
      (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0) : Polynomial K)) = 2 := by
  have h_monic : (Polynomial.X ^ 2 - Polynomial.C (tau - c_0) : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub_C (tau - c_0) (by decide)
  have h_natDeg : (Polynomial.X ^ 2 - Polynomial.C (tau - c_0) : Polynomial K).natDegree = 2 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 2
    · rw [Polynomial.natDegree_X_pow]
      have h : (Polynomial.C (tau - c_0)).natDegree = 0 := Polynomial.natDegree_C _
      omega
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis' h_monic),
      AdjoinRoot.powerBasis'_dim, h_natDeg]

/-! ### Evaluation map MvPoly(VarIndex 2 1) → AdjoinRoot

The map sends each Mambo variable to its post-elimination image:
- s_{0,0} → 0           (boundary start)
- s_{0,1} → C τ          (boundary end)
- s_{1,0} → root         (the AdjoinRoot generator α with α² = τ − c_0)
- s_{1,1} → 7·root + C(τ² + d_0)  (computed via ψ-round at α)
-/

/-- The post-elimination image of a variable under the t = 2 n = 1 eval map. -/
noncomputable def t2_n1_var_image (c_0 d_0 tau : K) :
    VarIndex 2 1 → AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))
  | (⟨0, _⟩, ⟨0, _⟩) => 0
  | (⟨0, _⟩, ⟨1, _⟩) => algebraMap K _ tau
  | (⟨1, _⟩, ⟨0, _⟩) => AdjoinRoot.root _
  | (⟨1, _⟩, ⟨1, _⟩) =>
      (7 : K) • AdjoinRoot.root _ + algebraMap K _ (tau ^ 2 + d_0)
  | _ => 0  -- unreachable; satisfies pattern completeness

/-- The eval map MvPoly(VarIndex 2 1) → AdjoinRoot of the defining polynomial.
    Will be shown to factor through mamboT2Ideal (next phase). -/
noncomputable def t2_n1_eval (c_0 d_0 tau : K) :
    MvPolynomial (VarIndex 2 1) K →ₐ[K]
    AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) :=
  MvPolynomial.aeval (t2_n1_var_image K c_0 d_0 tau)

/-- **Boundary start is killed by the eval map.** -/
theorem t2_n1_eval_boundaryStart (c_0 d_0 tau : K) :
    t2_n1_eval K c_0 d_0 tau (boundaryStart K 1) = 0 := by
  unfold t2_n1_eval boundaryStart sVar
  rw [MvPolynomial.aeval_X]
  rfl

/-- **Boundary end is killed by the eval map.** -/
theorem t2_n1_eval_boundaryEnd (c_0 d_0 tau : K) :
    t2_n1_eval K c_0 d_0 tau (boundaryEnd K 1 tau) = 0 := by
  unfold t2_n1_eval boundaryEnd sVar
  simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
             Algebra.id.map_eq_self]
  show t2_n1_var_image K c_0 d_0 tau _ - algebraMap K _ tau = 0
  unfold t2_n1_var_image
  simp

/-- **Key AdjoinRoot identity:** root² = algebraMap K _ (τ − c_0).
    Derives from `AdjoinRoot.aeval_eq` + `mk_self`: aeval(root) at f = 0. -/
theorem t2_n1_root_sq_eq (c_0 tau : K) :
    (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))) ^ 2
      = algebraMap K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))) (tau - c_0) := by
  have h : (Polynomial.aeval
              (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))))
              (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  -- h : root^2 - (algebraMap _ tau - algebraMap _ c_0) = 0
  -- Goal: root^2 = algebraMap _ (tau - c_0)
  -- Use map_sub on algebraMap to match h.
  have h_map : algebraMap K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))) (tau - c_0)
             = algebraMap K _ tau - algebraMap K _ c_0 := map_sub _ _ _
  rw [h_map]
  exact sub_eq_zero.mp h

/-- **The θ-round constraint at (r=0) is killed by the eval map.** -/
theorem t2_n1_eval_roundTheta (c_0 d_0 tau : K) :
    t2_n1_eval K c_0 d_0 tau (roundConstraintTheta K 1 0 c_0) = 0 := by
  unfold t2_n1_eval roundConstraintTheta sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
             Algebra.id.map_eq_self]
  -- After simp: image of s_(0,1) − 7 • image of s_(0,0) − image of s_(1,0) * image of s_(1,0)
  --             − algebraMap K _ c_0 = 0
  -- Substitute t2_n1_var_image values:
  show algebraMap K _ tau - (7 : K) • (0 : AdjoinRoot _)
       - (AdjoinRoot.root _) * (AdjoinRoot.root _) - algebraMap K _ c_0 = 0
  rw [smul_zero, sub_zero]
  -- root * root = root^2
  rw [show (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)))
        * (AdjoinRoot.root _)
       = (AdjoinRoot.root _) ^ 2 from (pow_two _).symm]
  rw [t2_n1_root_sq_eq]
  -- Now: algebraMap K _ tau + (-algebraMap K _ (tau - c_0) - algebraMap K _ c_0) = 0
  -- Use simp to normalize algebraMap (tau - c_0) → algebraMap tau - algebraMap c_0, then ring.
  simp only [map_sub]
  ring

/-- **The ψ-round constraint at (r=0) is killed by the eval map.** -/
theorem t2_n1_eval_roundPsi (c_0 d_0 tau : K) :
    t2_n1_eval K c_0 d_0 tau (roundConstraintPsi K 1 0 d_0) = 0 := by
  unfold t2_n1_eval roundConstraintPsi sVar
  simp only [map_sub, map_smul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
             Algebra.id.map_eq_self]
  -- After simp: image of s_(1,1) − 7 • image of s_(1,0) − (image of s_(0,1))^2 − algebraMap K _ d_0 = 0
  show ((7 : K) • (AdjoinRoot.root _) + algebraMap K _ (tau ^ 2 + d_0))
       - (7 : K) • (AdjoinRoot.root _)
       - (algebraMap K _ tau) * (algebraMap K _ tau)
       - algebraMap K _ d_0 = 0
  -- (algebraMap _ tau) * (algebraMap _ tau) = algebraMap _ (tau^2)
  rw [show (algebraMap K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))) tau)
        * (algebraMap K _ tau)
       = algebraMap K _ (tau^2) by
        rw [← map_mul]; ring_nf]
  -- algebraMap _ (tau^2 + d_0) - algebraMap _ tau^2 - algebraMap _ d_0
  -- = algebraMap _ (tau^2 + d_0 - tau^2 - d_0) = 0
  simp only [map_add, map_sub]
  ring

/-- **The full mamboT2Ideal at n=1 is killed by the eval map.**
    Combines all 4 generator-killings via `Ideal.span_le`. -/
theorem t2_n1_eval_kills_ideal (c_0 d_0 tau : K) :
    mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau
      ≤ RingHom.ker ((t2_n1_eval K c_0 d_0 tau).toRingHom) := by
  unfold mamboT2Ideal
  rw [Ideal.span_le]
  rintro p (((⟨r, rfl⟩ | ⟨r, rfl⟩) | (rfl | rfl)))
  · -- roundTheta r case
    fin_cases r
    exact t2_n1_eval_roundTheta K c_0 d_0 tau
  · -- roundPsi r case
    fin_cases r
    exact t2_n1_eval_roundPsi K c_0 d_0 tau
  · -- boundaryStart
    exact t2_n1_eval_boundaryStart K c_0 d_0 tau
  · -- boundaryEnd
    exact t2_n1_eval_boundaryEnd K c_0 d_0 tau

/-- **Factored eval map:** `MvPoly / mamboT2Ideal → AdjoinRoot`.
    Uses `Ideal.Quotient.lift` with the ideal-kill lemma. -/
noncomputable def t2_n1_eval_bar (c_0 d_0 tau : K) :
    (MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau) →+*
    AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) :=
  Ideal.Quotient.lift _ (t2_n1_eval K c_0 d_0 tau).toRingHom
    (fun a ha => t2_n1_eval_kills_ideal K c_0 d_0 tau ha)

/-- The quotient class of `s_(1,0)` satisfies `X² − C(τ − c_0) = 0`
    (since `s_(1,0)² − C(τ − c_0) = boundary_end − 7·boundary_start − roundTheta`,
    a combination of generators all in `mamboT2Ideal`). Foundation for
    building the AdjoinRoot.lift inverse. -/
theorem t2_n1_s10_sq_in_ideal (c_0 d_0 tau : K) :
    (sVar K 1 1 0 * sVar K 1 1 0 - MvPolynomial.C (tau - c_0) :
        MvPolynomial (VarIndex 2 1) K)
      ∈ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau := by
  -- Express s_(1,0)² − C(τ − c_0) as − roundTheta + boundary_end − 7•boundary_start
  -- (with rcs all 0 → c_0 the constant). The signs and coefficients work out.
  have h_express :
      (sVar K 1 1 0 * sVar K 1 1 0 - MvPolynomial.C (tau - c_0)
          : MvPolynomial (VarIndex 2 1) K)
      = -(roundConstraintTheta K 1 0 c_0)
        + boundaryEnd K 1 tau - (phi : K) • boundaryStart K 1 := by
    unfold roundConstraintTheta boundaryEnd boundaryStart sVar phi
    simp only [map_sub]
    push_cast
    ring
  rw [h_express]
  -- All three pieces are in the ideal.
  unfold mamboT2Ideal
  refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · -- -roundTheta ∈ span
    exact Submodule.neg_mem _ (Ideal.subset_span (Or.inl (Or.inl ⟨0, rfl⟩)))
  · -- boundary_end ∈ span
    exact Ideal.subset_span (Or.inr (Or.inr rfl))
  · -- (phi : K) • boundary_start ∈ span; use scalar-tower smul.
    exact Submodule.smul_of_tower_mem _ _ (Ideal.subset_span (Or.inr (Or.inl rfl)))

/-- The class of `s_(1,0)` in the Mambo quotient ring. -/
noncomputable abbrev t2_n1_s10_class (c_0 d_0 tau : K) :
    MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau :=
  Ideal.Quotient.mk _ (sVar K 1 1 0)

/-- The class `s_(1,0)` is a root of `X² − C(τ − c_0)` in the quotient ring. -/
theorem t2_n1_s10_class_isRoot (c_0 d_0 tau : K) :
    (Polynomial.aeval (t2_n1_s10_class K c_0 d_0 tau))
      (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) = 0 := by
  -- Reduce to membership in mamboT2Ideal via Quotient.mk and t2_n1_s10_sq_in_ideal.
  unfold t2_n1_s10_class
  rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
  -- Goal: mk(s10)^2 - (algebraMap K _ ∘ C of (tau-c_0)) = 0
  -- algebraMap of constants in MvPoly K ⧸ I equals mk ∘ MvPoly.C
  show (Ideal.Quotient.mk _ (sVar K 1 1 0)) ^ 2
       - Ideal.Quotient.mk _ (MvPolynomial.C (tau - c_0)) = 0
  rw [pow_two, ← map_mul, ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (t2_n1_s10_sq_in_ideal K c_0 d_0 tau)

/-- **Inverse map:** `AdjoinRoot (X² − C(τ − c_0)) → MvPoly / mamboT2Ideal`
    via `AdjoinRoot.liftHom`, sending `root` to the class of `s_(1,0)`. -/
noncomputable def t2_n1_inverse (c_0 d_0 tau : K) :
    AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) →ₐ[K]
    (MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau) :=
  AdjoinRoot.liftHom _ (t2_n1_s10_class K c_0 d_0 tau)
    (t2_n1_s10_class_isRoot K c_0 d_0 tau)

/-- IsTwoSided instance for `mamboT2Ideal` (commutative ring). -/
instance (c_0 d_0 tau : K) :
    (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau).IsTwoSided := inferInstance

/-- **Factored eval map as an AlgHom** (rather than just a RingHom). -/
noncomputable def t2_n1_eval_bar_alg (c_0 d_0 tau : K) :
    (MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau) →ₐ[K]
    AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) :=
  Ideal.Quotient.liftₐ _ (t2_n1_eval K c_0 d_0 tau)
    (fun a ha => t2_n1_eval_kills_ideal K c_0 d_0 tau ha)

/-! ### Variable-image identities in the quotient ring

For each of the 4 Mambo variables, mk(X v) in the quotient equals
the same image as eval(X v) under inverse ∘ var_image. These 4 lemmas
discharge the case-analysis branches in the AlgEquiv assembly. -/

/-- `mk(s_(0,0)) = 0` (boundary start is in the ideal). -/
theorem t2_n1_mk_X_00 (c_0 d_0 tau : K) :
    (Ideal.Quotient.mk (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau))
      (sVar K 1 0 0) = 0 := by
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  unfold mamboT2Ideal
  exact Ideal.subset_span (Or.inr (Or.inl rfl))

/-- `mk(s_(0,1)) = algebraMap K _ τ` (boundary end forces this in the quotient). -/
theorem t2_n1_mk_X_01 (c_0 d_0 tau : K) :
    (Ideal.Quotient.mk (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau))
      (sVar K 1 0 1)
    = algebraMap K _ tau := by
  -- mk(s_(0,1) - C tau) = mk(boundary_end) = 0
  rw [show algebraMap K (MvPolynomial (VarIndex 2 1) K ⧸ _) tau
        = Ideal.Quotient.mk _ (MvPolynomial.C tau) from rfl]
  rw [← sub_eq_zero, ← map_sub]
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  unfold mamboT2Ideal
  exact Ideal.subset_span (Or.inr (Or.inr rfl))

/-- `mk(s_(1,1)) = 7·mk(s_(1,0)) + algebraMap K _ (τ² + d_0)`. -/
theorem t2_n1_mk_X_11 (c_0 d_0 tau : K) :
    (Ideal.Quotient.mk (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau))
      (sVar K 1 1 1)
    = (phi : K) • (Ideal.Quotient.mk _ (sVar K 1 1 0))
      + algebraMap K _ (tau ^ 2 + d_0) := by
  have h_psi : (Ideal.Quotient.mk (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau))
                  (roundConstraintPsi K 1 0 d_0) = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    unfold mamboT2Ideal
    exact Ideal.subset_span (Or.inl (Or.inr ⟨0, rfl⟩))
  unfold roundConstraintPsi sVar at h_psi
  simp only [map_sub, map_smul, map_mul, Algebra.smul_def, Fin.succ_zero_eq_one,
             Fin.castSucc_zero] at h_psi
  have h_01 := t2_n1_mk_X_01 K c_0 d_0 tau
  unfold sVar at h_01
  rw [h_01] at h_psi
  -- h_psi: mk(X(1,1)) - phi•mk(X(1,0)) - algebraMap _ tau * algebraMap _ tau - mk(C d_0) = 0
  have h_mul : (algebraMap K (MvPolynomial (VarIndex 2 1) K ⧸
                  mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau)) tau
              * algebraMap K _ tau
              = algebraMap K _ (tau ^ 2) := by
    rw [← map_mul]; congr 1; ring
  rw [h_mul] at h_psi
  -- h_psi: mk(X(1,1)) - phi•mk(X(1,0)) - algebraMap _ (tau^2) - mk(C d_0) = 0
  -- mk(C d_0) = algebraMap _ d_0 definitionally
  -- Combine: algebraMap _ (tau^2) + algebraMap _ d_0 = algebraMap _ (tau^2 + d_0)
  rw [show ((Ideal.Quotient.mk (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau))
              (MvPolynomial.C d_0))
       = algebraMap K _ d_0 from rfl] at h_psi
  rw [map_add, Algebra.smul_def]
  unfold sVar
  have h_norm : (Ideal.Quotient.mk (mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau))
                  ((algebraMap K (MvPolynomial (VarIndex 2 1) K)) ↑phi)
              = algebraMap K _ ↑phi := rfl
  rw [h_norm] at h_psi
  linear_combination h_psi

/-! ### The AlgEquiv assembly -/

/-- Forward direction: `eval_bar_alg ∘ inverse = AlgHom.id`. -/
theorem t2_n1_eval_bar_alg_comp_inverse (c_0 d_0 tau : K) :
    (t2_n1_eval_bar_alg K c_0 d_0 tau).comp (t2_n1_inverse K c_0 d_0 tau)
      = AlgHom.id K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0))) := by
  apply AdjoinRoot.algHom_ext
  -- check on root
  show t2_n1_eval_bar_alg K c_0 d_0 tau
          (t2_n1_inverse K c_0 d_0 tau (AdjoinRoot.root _))
        = AdjoinRoot.root _
  -- inverse(root) = t2_n1_s10_class by liftHom_root (@[simp])
  unfold t2_n1_inverse
  rw [AdjoinRoot.liftHom_root]
  -- eval_bar_alg(t2_n1_s10_class) = eval_bar_alg(mk(s_(1,0))) = eval(s_(1,0)) = root
  show t2_n1_eval_bar_alg K c_0 d_0 tau
          (Ideal.Quotient.mk _ (sVar K 1 1 0)) = AdjoinRoot.root _
  unfold t2_n1_eval_bar_alg
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  -- t2_n1_eval(sVar K 1 1 0) = aeval(var_image)(X(1, 0)) = var_image(1, 0) = root
  unfold t2_n1_eval sVar
  show (MvPolynomial.aeval (t2_n1_var_image K c_0 d_0 tau))
          (MvPolynomial.X (1, 0)) = AdjoinRoot.root _
  rw [MvPolynomial.aeval_X]
  rfl

/-- Reverse direction: `inverse ∘ eval_bar_alg = AlgHom.id`. -/
theorem t2_n1_inverse_comp_eval_bar_alg (c_0 d_0 tau : K) :
    (t2_n1_inverse K c_0 d_0 tau).comp (t2_n1_eval_bar_alg K c_0 d_0 tau)
      = AlgHom.id K
          (MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  -- For each v : VarIndex 2 1 = Fin 2 × Fin 2, show inverse(eval(X v)) = mk(X v).
  -- Helper: evaluate the LHS for any v, reducing to inverse(var_image v) = mk(X v).
  have h_step : ∀ v : VarIndex 2 1,
      ((t2_n1_inverse K c_0 d_0 tau).comp (t2_n1_eval_bar_alg K c_0 d_0 tau)).comp
          (Ideal.Quotient.mkₐ K _) (MvPolynomial.X v)
      = t2_n1_inverse K c_0 d_0 tau (t2_n1_var_image K c_0 d_0 tau v) := by
    intro w
    show t2_n1_inverse K c_0 d_0 tau
            (t2_n1_eval_bar_alg K c_0 d_0 tau
              ((Ideal.Quotient.mkₐ K _) (MvPolynomial.X w)))
          = _
    unfold t2_n1_eval_bar_alg t2_n1_eval
    show t2_n1_inverse K c_0 d_0 tau
            (Ideal.Quotient.liftₐ _ _ _ ((Ideal.Quotient.mk _) (MvPolynomial.X w)))
          = _
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    show t2_n1_inverse K c_0 d_0 tau
            ((MvPolynomial.aeval (t2_n1_var_image K c_0 d_0 tau)) (MvPolynomial.X w)) = _
    rw [MvPolynomial.aeval_X]
  rw [h_step v]
  -- Now: inverse(var_image v) = mkₐ (X v), case analyze on v.
  match v with
  | (⟨0, _⟩, ⟨0, _⟩) =>
    show t2_n1_inverse K c_0 d_0 tau (0 : AdjoinRoot _)
          = (Ideal.Quotient.mkₐ K _) (MvPolynomial.X _)
    rw [map_zero]
    exact (t2_n1_mk_X_00 K c_0 d_0 tau).symm
  | (⟨0, _⟩, ⟨1, _⟩) =>
    show t2_n1_inverse K c_0 d_0 tau (algebraMap K _ tau)
          = (Ideal.Quotient.mkₐ K _) (MvPolynomial.X _)
    rw [AlgHom.commutes]
    exact (t2_n1_mk_X_01 K c_0 d_0 tau).symm
  | (⟨1, _⟩, ⟨0, _⟩) =>
    show t2_n1_inverse K c_0 d_0 tau (AdjoinRoot.root _)
          = (Ideal.Quotient.mkₐ K _) (MvPolynomial.X _)
    unfold t2_n1_inverse
    rw [AdjoinRoot.liftHom_root]
    rfl
  | (⟨1, _⟩, ⟨1, _⟩) =>
    show t2_n1_inverse K c_0 d_0 tau
            ((7 : K) • AdjoinRoot.root _ + algebraMap K _ (tau ^ 2 + d_0))
          = (Ideal.Quotient.mkₐ K _) (MvPolynomial.X _)
    rw [map_add, map_smul]
    unfold t2_n1_inverse
    rw [AdjoinRoot.liftHom_root, AlgHom.commutes]
    show (7 : K) • t2_n1_s10_class K c_0 d_0 tau + algebraMap K _ (tau^2 + d_0)
        = (Ideal.Quotient.mk _) (MvPolynomial.X (1, 1))
    have h := t2_n1_mk_X_11 K c_0 d_0 tau
    unfold sVar at h
    rw [show ((7 : K) : K) = (phi : K) from rfl]
    exact h.symm

/-- **THE CLIMACTIC THEOREM:** the Mambo CICO quotient ring is K-algebra
    isomorphic to `AdjoinRoot (X² − C(τ − c_0))` at t = 2 n = 1. -/
noncomputable def t2_n1_algEquiv (c_0 d_0 tau : K) :
    (MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau)
      ≃ₐ[K] AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (tau - c_0)) :=
  AlgEquiv.ofAlgHom (t2_n1_eval_bar_alg K c_0 d_0 tau) (t2_n1_inverse K c_0 d_0 tau)
    (t2_n1_eval_bar_alg_comp_inverse K c_0 d_0 tau)
    (t2_n1_inverse_comp_eval_bar_alg K c_0 d_0 tau)

/-- **FINAL DIM THEOREM at t = 2 n = 1:** `dim_K (MvPoly(VarIndex 2 1) K ⧸ mamboT2Ideal_n=1) = 2`.
    Matches paper Thm `thm:hilb_closed` at n = 1: `2 = 2^{2·1−1}`. First fully formal
    SEMANTIC Mambo CICO ideal dim theorem. -/
theorem t2_n1_dim (c_0 d_0 tau : K) :
    Module.finrank K
      (MvPolynomial (VarIndex 2 1) K ⧸ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau) = 2 := by
  rw [(t2_n1_algEquiv K c_0 d_0 tau).toLinearEquiv.finrank_eq]
  exact t2_n1_AdjoinRoot_finrank K c_0 tau

/-! ### t = 2 n = 2 — scaling up the elimination (scaffold)

At n = 2: 4 round constraints + 2 boundaries in 6 variables. Eliminations:
- s_{0,0} = 0; s_{0,1} = X² + c_0; s_{1,1} = 7X + s_{0,1}² + d_0;
- s_{0,2} forced = τ; s_{1,2} = 7·s_{1,1} + τ² + d_1.

θ-round at r=1 gives defining polynomial:
  U_2(X) = 7(X²+c_0) + (7X + (X²+c_0)² + d_0)² + c_1 − τ

monic of degree 8 = d_θ(2). AdjoinRoot(U_2) has K-finrank 8 = 2^{2·2-1}.

Definition of U_2 (full iso assembly mirrors n=1, ~300 more lines, deferred). -/

/-- The defining univariate polynomial at t = 2 n = 2. Monic of degree 8
    (leading term `X^8` from `((X²+c_0)²)²` in the ψ-recurrence squaring).
    Full natDegree proof + iso construction deferred to next iteration. -/
noncomputable def t2_n2_defining_poly (c_0 d_0 c_1 tau : K) : Polynomial K :=
  let X := Polynomial.X
  let s01 := X ^ 2 + Polynomial.C c_0
  let s11 := (Polynomial.C 7) * X + s01 ^ 2 + Polynomial.C d_0
  (Polynomial.C 7) * s01 + s11 ^ 2 + Polynomial.C c_1 - Polynomial.C tau

/-! ### Paper lem:sq_reduction at n = 1 (single-variable degenerate case)

Paper Lemma `lem:sq_reduction` (mambo_tosc_2026.tex line 2473): for every
free variable x ∈ F_n at t = 2, x² ≡ a_0 + Σ a_y · y (mod I) for some
scalars a_0, a_y ∈ F_p.

At t = 2 n = 1: F_n = {s_(1,0)} (single free variable), so the lemma
reduces to: `s_(1,0)² ≡ a_0 (mod I)` for some constant a_0 (the linear
combination is trivial since |F_n| = 1 and a_0 is the constant term).

From `t2_n1_s10_sq_in_ideal` above: `s_(1,0)² − C(τ − c_0) ∈ mamboT2Ideal`,
hence `s_(1,0)² ≡ C(τ − c_0) (mod I)` with a_0 = τ − c_0. This IS the
n = 1 instance of paper lem:sq_reduction. The general-n case (4-case
proof structure in the paper) is the natural extension for B (general-n
induction). -/

/-- **Paper Lemma `lem:sq_reduction` at n = 1:** the free variable
    s_(1,0) satisfies a Boolean-style reduction `s_(1,0)² ≡ a_0 (mod I)`
    with `a_0 = τ − c_0`. -/
theorem t2_n1_sq_reduction_at_s10 (c_0 d_0 tau : K) :
    (sVar K 1 1 0 * sVar K 1 1 0 - MvPolynomial.C (tau - c_0)
        : MvPolynomial (VarIndex 2 1) K)
      ∈ mamboT2Ideal K 1 (fun _ => c_0) (fun _ => d_0) tau :=
  t2_n1_s10_sq_in_ideal K c_0 d_0 tau

end Mambo.T2CicoIdeal
