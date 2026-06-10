/-!
# Mambo Round Function at width t = 3

Lean 4 definition of the Mambo t = 3 coupled-quadratic permutation round.
Mirror of `Mambo.RoundFunction` (which targets t = 4), at the chained-three
configuration used in the production t = 3 deployment (paper Table 7,
N = 23 / 33 / 44 for L1 / L3 / L5).

Round (width t = 3, coupled-quadratic, multiplier φ = 7):

  n₀ = φ·s₀ + s₂² + rc₀     -- wrap-around: predecessor of cell 0 is cell t-1
  n₁ = φ·s₁ + n₀² + rc₁
  n₂ = φ·s₂ + n₁² + rc₂
-/

namespace Mambo.T3RoundFunction

/-- Mambo multiplier constant; same value across all widths. -/
def phi : Nat := 7

/-- One Mambo coupled-quadratic round at width t = 3, working modulo `p`. -/
def round (p : Nat) (s rc : List Nat) : List Nat :=
  match s, rc with
  | [s0, s1, s2], [r0, r1, r2] =>
      let n0 := (phi * s0 + s2 * s2 + r0) % p
      let n1 := (phi * s1 + n0 * n0 + r1) % p
      let n2 := (phi * s2 + n1 * n1 + r2) % p
      [n0, n1, n2]
  | _, _ => []

/-- N-round Mambo permutation at t = 3. -/
def perm (p : Nat) (N : Nat) (s : List Nat) (RC : Nat → List Nat) : List Nat :=
  match N with
  | 0 => s
  | k+1 => round p (perm p k s RC) (RC k)

/-- Sanity: the round preserves length-3 lists. -/
theorem round_length (p : Nat) :
    ∀ (s rc : List Nat), s.length = 3 → rc.length = 3 → (round p s rc).length = 3
  | [_,_,_], [_,_,_], _, _ => rfl

/-- Sanity: applying the round to the zero state with zero RC produces zero. -/
example : round 2130706433 [0, 0, 0] [0, 0, 0] = [0, 0, 0] := by rfl

/-- Algebraic degree per round: degree-2 (the coupled-quadratic invariant
    that defines Mambo across all widths). -/
def algebraic_degree_per_round : Nat := 2

/-- Reference KoalaBear prime. -/
def koalabear_prime : Nat := 2130706433

/-- Reference BabyBear prime. -/
def babybear_prime : Nat := 2013265921

end Mambo.T3RoundFunction
