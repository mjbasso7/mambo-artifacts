import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Span
import Mambo.B2Enumeration

/-!
# Mambo t = 4 CICO Ideal (Paper Coupled-Sequential Round)

Formalises the paper's t = 4 Mambo CICO ideal using the canonical
coupled-sequential round generalised to width 4:

  s_{0,r+1} = φ · s_{0,r} + s_{3,r}^2     + c_{0,r}
  s_{1,r+1} = φ · s_{1,r} + s_{0,r+1}^2   + c_{1,r}
  s_{2,r+1} = φ · s_{2,r} + s_{1,r+1}^2   + c_{2,r}
  s_{3,r+1} = φ · s_{3,r} + s_{2,r+1}^2   + c_{3,r}

(Each subsequent cell squaring of the FRESHLY computed previous cell —
the paper's sequential-coupling structure extended to width 4.)

Plus boundary constraints `s_{0,0} = 0` and `s_{0,n} = τ` for the CICO
preimage problem.

This file mirrors the `Mambo.T2CicoIdeal` and `Mambo.T3CicoIdeal`
patterns at width 4. The general-n dim formula `2^{4n - 3}` (sage-
verified at 5 cells n = 3..8, Q_4-corrected) is the target for a
future `T4GeneralN.lean` analogous to the t=2 proof in
`Mambo.T2GeneralN.t2_general_dim`. Per-cell native_decide closure at
specific small n is a tractable intermediate step.
-/

namespace Mambo.T4CicoIdeal

open MvPolynomial Mambo.B2Enumeration

variable (K : Type*) [Field K]

/-- A t = 4 Mambo state variable: `s_{c, r}` for cell `c ∈ {0, 1, 2, 3}`
    and round `r ∈ {0, ..., n}`. -/
noncomputable def sVar (n : Nat) (c : Fin 4) (r : Fin (n + 1)) :
    MvPolynomial (VarIndex 4 n) K :=
  X (c, r)

/-- Mambo multiplier φ = 7 (paper default). -/
def phi : Nat := 7

/-- Round constraint at cell 0 (uses s_{t-1,r}² = s_{3,r}² for t = 4):
    `s_{0, r+1} = φ·s_{0, r} + s_{3, r}^2 + c_{0,r}`. -/
noncomputable def roundConstraint0 (n : Nat) (r : Fin n) (c0_r : K) :
    MvPolynomial (VarIndex 4 n) K :=
  sVar K n 0 r.succ - (phi : K) • sVar K n 0 r.castSucc
    - sVar K n 3 r.castSucc * sVar K n 3 r.castSucc - C c0_r

/-- Round constraint at cell 1 (uses FRESHLY computed s_{0, r+1}²):
    `s_{1, r+1} = φ·s_{1, r} + (s_{0, r+1})^2 + c_{1,r}`. -/
noncomputable def roundConstraint1 (n : Nat) (r : Fin n) (c1_r : K) :
    MvPolynomial (VarIndex 4 n) K :=
  sVar K n 1 r.succ - (phi : K) • sVar K n 1 r.castSucc
    - sVar K n 0 r.succ * sVar K n 0 r.succ - C c1_r

/-- Round constraint at cell 2 (uses FRESHLY computed s_{1, r+1}²):
    `s_{2, r+1} = φ·s_{2, r} + (s_{1, r+1})^2 + c_{2,r}`. -/
noncomputable def roundConstraint2 (n : Nat) (r : Fin n) (c2_r : K) :
    MvPolynomial (VarIndex 4 n) K :=
  sVar K n 2 r.succ - (phi : K) • sVar K n 2 r.castSucc
    - sVar K n 1 r.succ * sVar K n 1 r.succ - C c2_r

/-- Round constraint at cell 3 (uses FRESHLY computed s_{2, r+1}²):
    `s_{3, r+1} = φ·s_{3, r} + (s_{2, r+1})^2 + c_{3,r}`. -/
noncomputable def roundConstraint3 (n : Nat) (r : Fin n) (c3_r : K) :
    MvPolynomial (VarIndex 4 n) K :=
  sVar K n 3 r.succ - (phi : K) • sVar K n 3 r.castSucc
    - sVar K n 2 r.succ * sVar K n 2 r.succ - C c3_r

/-- Boundary at start: `s_{0, 0} = 0`. -/
noncomputable def boundaryStart (n : Nat) : MvPolynomial (VarIndex 4 n) K :=
  sVar K n 0 ⟨0, Nat.succ_pos n⟩

/-- Boundary at end: `s_{0, n} = τ`. -/
noncomputable def boundaryEnd (n : Nat) (tau : K) :
    MvPolynomial (VarIndex 4 n) K :=
  sVar K n 0 ⟨n, Nat.lt_succ_self n⟩ - C tau

/-- The paper's t = 4 Mambo CICO ideal: span of all 4 round-constraint
    families (constraint0/1/2/3 for r ∈ Fin n) plus the two boundary
    constraints. -/
noncomputable def mamboT4Ideal (n : Nat)
    (c0_seq c1_seq c2_seq c3_seq : Fin n → K) (tau : K) :
    Ideal (MvPolynomial (VarIndex 4 n) K) :=
  Ideal.span (
    Set.range (fun r : Fin n => roundConstraint0 K n r (c0_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint1 K n r (c1_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint2 K n r (c2_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint3 K n r (c3_seq r))
    ∪ {boundaryStart K n, boundaryEnd K n tau})

/-- Sanity: variable count at t = 4 is `4·(n+1)`. -/
example (n : Nat) : Fintype.card (VarIndex 4 n) = 4 * (n + 1) := by
  rw [card_VarIndex 4 n]
  unfold numStateVars
  ring

/-- Sanity: at production cell n = 18, the t = 4 polynomial ring has 76 variables. -/
example : Fintype.card (VarIndex 4 18) = 76 := by
  rw [card_VarIndex 4 18]
  unfold numStateVars
  ring

end Mambo.T4CicoIdeal
