/-!
# Mambo Degree Growth Theorem (paper Thm `thm:degree`)

Formalizes the paper's "Degree growth" theorem (Section 3,
`mambo_tosc_2026.tex` line 504): for the Mambo coupled-quadratic
permutation P_{φ, n} applied for n rounds starting from
(θ₀, ψ₀) of degree 1, the polynomial degrees grow as

  d_ψ(n) = 4ⁿ,
  d_θ(n) = 2·4ⁿ⁻¹ = 4ⁿ/2.

Derivation: by paper Lem `lem:recurrence`
  d_θ(n) = max(d_θ(n−1), 2·d_ψ(n−1)),
  d_ψ(n) = 2·d_θ(n).

Together with base d_θ(0) = d_ψ(0) = 1, the recurrence implies the
closed form by strong induction on n ≥ 1.

ALFOM corollary (paper Cor `cor:alfom`): η = log₂(d_ψ(n))/C
= log₂(4ⁿ)/(2n) = 2n/(2n) = 1.0.
-/

namespace Mambo.DegreeGrowth

/-- Degree of θₙ: closed form `dTheta 0 = 1`, `dTheta (n+1) = 2·4ⁿ`. -/
def dTheta : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * 4 ^ n

/-- Degree of ψₙ: closed form `dPsi 0 = 1`, `dPsi n = 4ⁿ` for n ≥ 1. -/
def dPsi : Nat → Nat
  | 0     => 1
  | n + 1 => 4 ^ (n + 1)

/-- Sanity: d_θ(1) = 2, d_ψ(1) = 4. (Paper base case.) -/
example : dTheta 1 = 2 := by rfl
example : dPsi 1 = 4 := by rfl

/-- Sanity: d_θ(2) = 8, d_ψ(2) = 16. -/
example : dTheta 2 = 8 := by rfl
example : dPsi 2 = 16 := by rfl

/-- Sanity: d_θ(3) = 32, d_ψ(3) = 64. -/
example : dTheta 3 = 32 := by rfl
example : dPsi 3 = 64 := by rfl

/-- Sanity: d_θ(4) = 128, d_ψ(4) = 256. -/
example : dTheta 4 = 128 := by rfl
example : dPsi 4 = 256 := by rfl

/-- **Paper Thm `thm:degree`, ψ closed form:** d_ψ(n) = 4ⁿ for n ≥ 1.
    (Trivial from the closed-form definition.) -/
theorem dPsi_closed_form (n : Nat) : dPsi (n + 1) = 4 ^ (n + 1) := rfl

/-- **Paper Thm `thm:degree`, θ closed form:** d_θ(n) = 2·4ⁿ⁻¹ for n ≥ 1.
    (Trivial from the closed-form definition.) -/
theorem dTheta_closed_form (n : Nat) : dTheta (n + 1) = 2 * 4 ^ n := rfl

/-- **Paper Lem `lem:recurrence` (verification):** the closed-form
    definitions satisfy the recurrence
    `d_ψ(n) = 2·d_θ(n)`. -/
theorem dPsi_eq_two_dTheta (n : Nat) : dPsi (n + 1) = 2 * dTheta (n + 1) := by
  show 4 ^ (n + 1) = 2 * (2 * 4 ^ n)
  rw [Nat.pow_succ, Nat.mul_comm (4^n) 4]
  show 4 * 4 ^ n = 2 * (2 * 4 ^ n)
  rw [← Nat.mul_assoc]

/-- **Paper Lem `lem:recurrence` (verification):** the closed-form
    definitions satisfy
    `d_θ(n) = max(d_θ(n−1), 2·d_ψ(n−1))`. -/
theorem dTheta_recurrence (n : Nat) :
    dTheta (n + 1) = max (dTheta n) (2 * dPsi n) := by
  cases n with
  | zero =>
    -- d_θ(1) = max(d_θ(0), 2·d_ψ(0)) = max(1, 2) = 2 ✓
    rfl
  | succ k =>
    -- d_θ(k+2) = max(d_θ(k+1), 2·d_ψ(k+1))
    -- LHS: 2·4^(k+1)
    -- d_θ(k+1) = 2·4^k, 2·d_ψ(k+1) = 2·4^(k+1)
    -- max(2·4^k, 2·4^(k+1)) = 2·4^(k+1) since 4^k ≤ 4^(k+1)
    show 2 * 4 ^ (k + 1) = max (2 * 4 ^ k) (2 * 4 ^ (k + 1))
    have h_le : 2 * 4 ^ k ≤ 2 * 4 ^ (k + 1) := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
    omega

/-- **ALFOM = 1.0 (paper Cor `cor:alfom`, numerical core):**
    d_ψ(n) = 2^(2n) for n ≥ 1, so log₂(d_ψ(n)) = 2n. With the Mambo
    per-round R1CS cost C = 2n, the algebraic-degree-to-cost ratio is
    log₂(d_ψ(n))/C = 2n/2n = 1. -/
theorem dPsi_log_eq_2n (n : Nat) : dPsi (n + 1) = 2 ^ (2 * (n + 1)) := by
  show 4 ^ (n + 1) = 2 ^ (2 * (n + 1))
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]

end Mambo.DegreeGrowth
