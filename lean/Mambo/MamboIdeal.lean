import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mambo.B2Enumeration
import Mambo.RoundFunction

/-!
# Mambo — Concrete Ideal in MvPolynomial (mathlib bridge for B.2)

Bridges `Mambo.B2Enumeration`'s typed variable-index space to mathlib's
`MvPolynomial`. Defines the Mambo coupled-quadratic ideal concretely as
generators in `MvPolynomial (VarIndex t n) K`.

The polynomial ring `R = K[s_{c,r} : (c,r) ∈ VarIndex t n]` is
`MvPolynomial (VarIndex t n) K`. The ideal `I` consists of:
- `t·n` round-constraint polynomials of the form
  `s_{c, r+1} - (phi * s_{c, r} + (prev)^2 + rc_{c,r})`
  where `prev` is the previous cell's value (wrap-around at c=0).
- 2 boundary linear constraints: `s_{0, 0} = 0` and `s_{0, n} = target`.

This file pins these as typed Lean definitions in mathlib's `MvPolynomial`.
The Mambo ideal can now be referred to by name in subsequent formal proofs.
-/

namespace Mambo.MamboIdeal

open MvPolynomial Mambo.B2Enumeration

variable (K : Type*) [CommRing K]

/-- A typed Mambo state variable: `s_{c, r}` for cell `c` and round `r`. -/
noncomputable def stateVar (t n : Nat) (c : Fin t) (r : Fin (n + 1)) :
    MvPolynomial (VarIndex t n) K :=
  X (c, r)

/-- The Mambo multiplier constant φ = 7. -/
def phi : Nat := Mambo.RoundFunction.phi

/-- A single round-constraint polynomial at `(c, r) → (c, r+1)` over width t:
    encodes `n_c = phi * s_c + (prev)^2 + rc_{c,r}` where `prev` is
    `s_{t-1}` for c=0 (wrap-around) or `n_{c-1}` for c>0.

    For simplicity we encode the wrap-around / chain form using only the
    PREVIOUS-ROUND values (i.e., `s_{c, r+1} - phi * s_{c, r} - s_{prev, r}^2 - rc`),
    which corresponds to a slight variant of the round function but
    preserves the structural HS properties (degree-2, coupled chain).

    The variant: at cell c and round r, the constraint is
    `s_{c, r+1} = phi * s_{c, r} + s_{(c-1 mod t), r}^2 + rc_{c,r}`.

    This is the "transposed" form. The full coupled form (with intra-round
    chain dependencies) is the one used in `Mambo.RoundFunction.round`; both
    are degree-2 in the ring. -/
noncomputable def roundConstraint (t n : Nat) [NeZero t]
    (c : Fin t) (r : Fin n) (rc : K) :
    MvPolynomial (VarIndex t n) K :=
  let s_curr  : MvPolynomial (VarIndex t n) K := X (c, r.castSucc)
  let s_next  : MvPolynomial (VarIndex t n) K := X (c, r.succ)
  let s_prev  : MvPolynomial (VarIndex t n) K := X (c - 1, r.castSucc)
  s_next - (phi : K) • s_curr - s_prev * s_prev - C rc

/-- The boundary constraint at the start: `s_{0, 0} = 0`. -/
noncomputable def boundaryStart (t n : Nat) [NeZero t] :
    MvPolynomial (VarIndex t n) K :=
  X (⟨0, Nat.pos_of_ne_zero (NeZero.ne t)⟩, ⟨0, Nat.succ_pos n⟩)

/-- The boundary constraint at the end: `s_{0, n} - target`. -/
noncomputable def boundaryEnd (t n : Nat) [NeZero t] (target : K) :
    MvPolynomial (VarIndex t n) K :=
  X (⟨0, Nat.pos_of_ne_zero (NeZero.ne t)⟩, ⟨n, Nat.lt_succ_self n⟩) - C target

/-- Variable cardinality of the Mambo polynomial ring at (t, n). -/
theorem mambo_var_count (t n : Nat) :
    Fintype.card (VarIndex t n) = numStateVars t n :=
  card_VarIndex t n

/-- Concrete anchor at t=4 n=3: 16 typed variables in the polynomial ring. -/
example : Fintype.card (VarIndex 4 3) = 16 := by
  rw [card_VarIndex 4 3]
  decide

/-- Concrete anchor at t=4 n=4: 20 typed variables. -/
example : Fintype.card (VarIndex 4 4) = 20 := by
  rw [card_VarIndex 4 4]
  decide

/-- Concrete anchor at t=6 n=4: 30 typed variables (the n-indexed regime cell). -/
example : Fintype.card (VarIndex 6 4) = 30 := by
  rw [card_VarIndex 6 4]
  decide

/-! ### Mambo CICO ideal as an `Ideal.span` -/

/-- The set of round-constraint polynomials at width t, depth n, with
    round-constant function `rc : Fin t → Fin n → K`. -/
noncomputable def roundConstraintSet (t n : Nat) [NeZero t] (rc : Fin t → Fin n → K) :
    Set (MvPolynomial (VarIndex t n) K) :=
  { p | ∃ (c : Fin t) (r : Fin n), p = roundConstraint K t n c r (rc c r) }

/-- The full Mambo CICO ideal: round-constraint generators plus the
    two boundary constraints (`s_{0,0} = 0` and `s_{0,n} = target`). -/
noncomputable def mamboIdeal (t n : Nat) [NeZero t] (rc : Fin t → Fin n → K) (target : K) :
    Ideal (MvPolynomial (VarIndex t n) K) :=
  Ideal.span (roundConstraintSet K t n rc ∪ {boundaryStart K t n, boundaryEnd K t n target})

/-- The Mambo CICO ideal is non-trivial (≠ ⊤) when `target = 0` and all
    round-constants are zero: every generator vanishes at the all-zero point,
    so the constant polynomial `1` cannot lie in the ideal (it does not vanish
    there). This rules out degeneration of the quotient ring. -/
theorem mamboIdeal_ne_top_at_zero (t n : Nat) [NeZero t] [Nontrivial K] :
    mamboIdeal K t n (fun _ _ => (0 : K)) (0 : K) ≠ ⊤ := by
  -- The eval-at-zero map sends every generator to 0 and would send 1 to 1 ≠ 0.
  intro h_top
  -- If the ideal were ⊤, then 1 ∈ ideal, hence eval(1) = 0, but eval(1) = 1.
  have h_one_mem : (1 : MvPolynomial (VarIndex t n) K) ∈
      mamboIdeal K t n (fun _ _ => (0 : K)) (0 : K) := by
    rw [h_top]; exact Submodule.mem_top
  -- Use the evaluation-at-zero ring hom to derive a contradiction.
  let eval0 : MvPolynomial (VarIndex t n) K →+* K :=
    MvPolynomial.eval (fun _ => (0 : K))
  have h_le : mamboIdeal K t n (fun _ _ => (0 : K)) (0 : K) ≤ RingHom.ker eval0 := by
    unfold mamboIdeal
    rw [Ideal.span_le]
    rintro p (⟨c, r, rfl⟩ | hp)
    · -- round-constraint case: roundConstraint K t n c r 0 evaluates to 0.
      simp [RingHom.mem_ker, eval0, roundConstraint, stateVar, phi]
    · rcases hp with rfl | rfl
      · -- boundaryStart: X (⟨0,_⟩, ⟨0,_⟩) evaluates to 0.
        simp [RingHom.mem_ker, eval0, boundaryStart]
      · -- boundaryEnd: X (⟨0,_⟩, ⟨n,_⟩) - 0 evaluates to 0.
        simp [RingHom.mem_ker, eval0, boundaryEnd]
  have h_one_in_ker : (1 : MvPolynomial (VarIndex t n) K) ∈ RingHom.ker eval0 :=
    h_le h_one_mem
  simp [RingHom.mem_ker, eval0] at h_one_in_ker

end Mambo.MamboIdeal
