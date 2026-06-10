/-!
# Mambo Round Function (Deliverable C)

Lean 4 definition of the Mambo t=4 coupled-quadratic permutation round.
Field arithmetic done in `Nat` with explicit modular reduction by prime `p`.

This file is self-contained (no mathlib dependency). It mirrors the
production t = 4 round function.

Round (width t=4, coupled-quadratic, multiplier φ = 7):

  n₀ = φ·s₀ + s₃²  + rc₀
  n₁ = φ·s₁ + n₀² + rc₁
  n₂ = φ·s₂ + n₁² + rc₂
  n₃ = φ·s₃ + n₂² + rc₃
-/

namespace Mambo.RoundFunction

/-- Mambo multiplier constant (φ in the paper). -/
def phi : Nat := 7

/-- One Mambo coupled-quadratic round at width t=4, working in ℤ/pℤ
    represented as `Nat` with explicit modular reduction. -/
def round (p : Nat) (s rc : List Nat) : List Nat :=
  match s, rc with
  | [s0, s1, s2, s3], [r0, r1, r2, r3] =>
      let n0 := (phi * s0 + s3 * s3 + r0) % p
      let n1 := (phi * s1 + n0 * n0 + r1) % p
      let n2 := (phi * s2 + n1 * n1 + r2) % p
      let n3 := (phi * s3 + n2 * n2 + r3) % p
      [n0, n1, n2, n3]
  | _, _ => []

/-- N-round Mambo permutation. -/
def perm (p : Nat) (N : Nat) (s : List Nat) (RC : Nat → List Nat) : List Nat :=
  match N with
  | 0 => s
  | k+1 => round p (perm p k s RC) (RC k)

/-- Sanity: applying the round to the zero state with zero RC produces zero. -/
example : round 2130706433 [0, 0, 0, 0] [0, 0, 0, 0] = [0, 0, 0, 0] := by rfl

/-- Sanity: round preserves length-4. -/
theorem round_length (p : Nat) :
    ∀ (s rc : List Nat), s.length = 4 → rc.length = 4 → (round p s rc).length = 4
  | [_,_,_,_], [_,_,_,_], _, _ => rfl

/-- The algebraic degree of one round, viewed as a polynomial map, is 2.
    This is the defining feature of the Mambo coupled-quadratic construction. -/
def algebraic_degree_per_round : Nat := 2

/-- Reference KoalaBear prime (p = 2^31 - 2^24 + 1). -/
def koalabear_prime : Nat := 2130706433

end Mambo.RoundFunction
