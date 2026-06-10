import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Span
import Mambo.B2Enumeration

/-!
# Mambo t = 3 CICO Ideal (Paper Coupled-Sequential Round)

Formalises the paper's t = 3 Mambo CICO ideal using the canonical
coupled-sequential round generalised to width 3:

  s_{0,r+1} = φ · s_{0,r} + s_{2,r}^2     + c_{0,r}
  s_{1,r+1} = φ · s_{1,r} + s_{0,r+1}^2   + c_{1,r}
  s_{2,r+1} = φ · s_{2,r} + s_{1,r+1}^2   + c_{2,r}

(Each subsequent cell squaring of the FRESHLY computed previous cell —
the paper's sequential-coupling structure extended to width 3.)

Paper sponge CICO convention at t = 3 (rate = 1, capacity = t - 1 = 2):
fix the two cap-in cells at depth 0 (`s_{1,0} = 0`, `s_{2,0} = 0`) and
the rate-out cell at depth n (`s_{0,n} = τ`). The free variable for
elimination is `s_{0,0}` (the rate-in cell — the CICO unknown).

This matches `mambo_tosc_2026.tex` line 1870-1883 verbatim: rate=1,
capacity=t-1, fix `x_2(0) = ... = x_t(0) = 0` and `x_1(n) = τ`.

This file mirrors the `Mambo.T2CicoIdeal` pattern at width 3. The
general-n dim formula `2^{3(n-1)}` (empirical, paper-additive) is the
target for a future `T3GeneralN.lean` analogous to the t=2 proof of
`Mambo.T2GeneralN.t2_general_dim`.
-/

namespace Mambo.T3CicoIdeal

open MvPolynomial Mambo.B2Enumeration

variable (K : Type*) [Field K]

/-- A t = 3 Mambo state variable: `s_{c, r}` for cell `c ∈ {0, 1, 2}` and
    round `r ∈ {0, ..., n}`. -/
noncomputable def sVar (n : Nat) (c : Fin 3) (r : Fin (n + 1)) :
    MvPolynomial (VarIndex 3 n) K :=
  X (c, r)

/-- Mambo multiplier φ = 7 (paper default). -/
def phi : Nat := 7

/-- Round constraint at cell 0 (uses s_{t-1,r}² = s_{2,r}² for t = 3):
    `s_{0, r+1} = φ·s_{0, r} + s_{2, r}^2 + c_{0,r}`. -/
noncomputable def roundConstraint0 (n : Nat) (r : Fin n) (c0_r : K) :
    MvPolynomial (VarIndex 3 n) K :=
  sVar K n 0 r.succ - (phi : K) • sVar K n 0 r.castSucc
    - sVar K n 2 r.castSucc * sVar K n 2 r.castSucc - C c0_r

/-- Round constraint at cell 1 (uses FRESHLY computed s_{0, r+1}²):
    `s_{1, r+1} = φ·s_{1, r} + (s_{0, r+1})^2 + c_{1,r}`. -/
noncomputable def roundConstraint1 (n : Nat) (r : Fin n) (c1_r : K) :
    MvPolynomial (VarIndex 3 n) K :=
  sVar K n 1 r.succ - (phi : K) • sVar K n 1 r.castSucc
    - sVar K n 0 r.succ * sVar K n 0 r.succ - C c1_r

/-- Round constraint at cell 2 (uses FRESHLY computed s_{1, r+1}²):
    `s_{2, r+1} = φ·s_{2, r} + (s_{1, r+1})^2 + c_{2,r}`. -/
noncomputable def roundConstraint2 (n : Nat) (r : Fin n) (c2_r : K) :
    MvPolynomial (VarIndex 3 n) K :=
  sVar K n 2 r.succ - (phi : K) • sVar K n 2 r.castSucc
    - sVar K n 1 r.succ * sVar K n 1 r.succ - C c2_r

/-- Legacy 2-boundary definition (cell 0 at depth 0 = 0). Kept for
    downstream compatibility (`Mambo.T3GeneralN` references); the
    canonical paper-convention ideal `mamboT3Ideal` uses the 3-boundary
    set below. -/
noncomputable def boundaryStart (n : Nat) : MvPolynomial (VarIndex 3 n) K :=
  sVar K n 0 ⟨0, Nat.succ_pos n⟩

/-- Legacy 2-boundary definition (cell 0 at depth n = τ). Kept for
    downstream compatibility. -/
noncomputable def boundaryEnd (n : Nat) (tau : K) :
    MvPolynomial (VarIndex 3 n) K :=
  sVar K n 0 ⟨n, Nat.lt_succ_self n⟩ - C tau

/-- Cap-in boundary at start (cell 1): `s_{1, 0} = 0` (paper convention). -/
noncomputable def boundaryCapIn1 (n : Nat) : MvPolynomial (VarIndex 3 n) K :=
  sVar K n 1 ⟨0, Nat.succ_pos n⟩

/-- Cap-in boundary at start (cell 2): `s_{2, 0} = 0` (paper convention). -/
noncomputable def boundaryCapIn2 (n : Nat) : MvPolynomial (VarIndex 3 n) K :=
  sVar K n 2 ⟨0, Nat.succ_pos n⟩

/-- Rate-out boundary at end (cell 0): `s_{0, n} = τ` (paper convention). -/
noncomputable def boundaryRateOut (n : Nat) (tau : K) :
    MvPolynomial (VarIndex 3 n) K :=
  sVar K n 0 ⟨n, Nat.lt_succ_self n⟩ - C tau

/-- The t = 3 Mambo CICO ideal (legacy 2-boundary form, downstream-compat).

    The legacy form uses {boundaryStart, boundaryEnd} (cell 0 only at depths 0
    and n). This matches the iterator base cases in `Mambo.T3GeneralN`
    (`s1_iter 0 = s2_iter 0 = Polynomial.X` — free placeholders for the
    capacity cells).

    The paper-exact 3-boundary form `mamboT3IdealPaperExact` below uses the
    cap-in zeros (`s_{1,0} = s_{2,0} = 0`) instead; that form requires
    `s1_iter`/`s2_iter` base cases to be 0, a downstream migration. -/
noncomputable def mamboT3Ideal (n : Nat)
    (c0_seq c1_seq c2_seq : Fin n → K) (tau : K) :
    Ideal (MvPolynomial (VarIndex 3 n) K) :=
  Ideal.span (
    Set.range (fun r : Fin n => roundConstraint0 K n r (c0_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint1 K n r (c1_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint2 K n r (c2_seq r))
    ∪ {boundaryStart K n, boundaryEnd K n tau})

/-- The paper-exact t = 3 Mambo CICO ideal (3-boundary form).

    Matches `mambo_tosc_2026.tex` line 1870-1883 verbatim: rate = 1,
    capacity = t-1 = 2, fix `x_2(0) = x_3(0) = 0` (cap-in) and
    `x_1(n) = τ` (rate-out). Requires downstream migration of
    `s1_iter`/`s2_iter` base cases to 0 for the eval-bridge to apply. -/
noncomputable def mamboT3IdealPaperExact (n : Nat)
    (c0_seq c1_seq c2_seq : Fin n → K) (tau : K) :
    Ideal (MvPolynomial (VarIndex 3 n) K) :=
  Ideal.span (
    Set.range (fun r : Fin n => roundConstraint0 K n r (c0_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint1 K n r (c1_seq r))
    ∪ Set.range (fun r : Fin n => roundConstraint2 K n r (c2_seq r))
    ∪ {boundaryCapIn1 K n, boundaryCapIn2 K n, boundaryRateOut K n tau})

/-- Sanity: variable count at t = 3 is `3·(n+1)`. -/
example (n : Nat) : Fintype.card (VarIndex 3 n) = 3 * (n + 1) := by
  rw [card_VarIndex 3 n]
  unfold numStateVars
  ring

end Mambo.T3CicoIdeal
