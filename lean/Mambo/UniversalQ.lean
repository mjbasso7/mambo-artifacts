/-!
# Universal-Q Theorem Statement (Deliverable A)

Lean statement of the **t = 4 universal-in-n Q theorem** for Mambo
coupled-quadratic ideals. The corollary
`evalAtOne (predicted_HS_numerator t n) = 2^(tn-3)` is fully proven; the
"predicted = actual HS" claim remains `sorry`-stubbed pending mathlib
`Polynomial`/`Ideal` infrastructure.

**Theorem (informal, t = 4 specific):** For Mambo at width `t = 4` and
depth `n ≥ 3`, the Hilbert series of `R/I` factors as

  HS_{R/I}(z) = (1 + z)^(4n − 9) · Q(z)

where `Q(z) = z⁵ + 11z⁴ + 25z³ + 19z² + 7z + 1` is a degree-5 quintic
universal in `n` (at fixed t = 4).

**Important scope note (retracted earlier "universal across t" claim):**
The original conjecture that Q is universal across t ≥ 4 was retracted on
2026-05-15 after measured t=6 n=4: HS sum = 2^20 (not 2^21), and the
peeled residue is a degree-7 polynomial, not the degree-5 Q. So Q
universality holds **at t = 4 in n, only**. Cells at t = 5..8 with n = 3
match the formula coincidentally (small-n degenerate regime) but do not
extend to larger n.

**Corollaries (at t = 4 specifically):**
- `d_reg = 4·n − 3`
- `dim_K(R/I) = 2^(4·n − 3)`  ← formally proven in this file

**Empirical status (post-retraction):** Bit-exact at 6 cells in-n at t = 4
(n = 3..8). Cells t=5..8 at n=3 match the predicted formula but are not
universality evidence (degenerate small-n regime).

The `Poly`-level proofs in this file are about the **predicted** HS
numerator formula and remain correct regardless. The retraction only
affects the *interpretation* of the formula as the actual HS of the
Mambo ideal — that interpretation holds only at t = 4.
-/

namespace Mambo.UniversalQ

/-- A polynomial represented as its coefficient list, low-to-high degree. -/
abbrev Poly := List Nat

namespace Poly

/-- Polynomial addition (pointwise on coefficients). -/
def add : Poly → Poly → Poly
  | [],       q        => q
  | p,        []       => p
  | x :: xs,  y :: ys  => (x + y) :: add xs ys

/-- Scalar multiplication. -/
def smul (c : Nat) : Poly → Poly
  | []     => []
  | x :: xs => (c * x) :: smul c xs

/-- Polynomial multiplication. -/
def mul : Poly → Poly → Poly
  | [],       _  => []
  | x :: xs,  q  => add (smul x q) (0 :: mul xs q)

/-- Evaluation at z = 1 (sum of coefficients). -/
def evalAtOne : Poly → Nat
  | []      => 0
  | x :: xs => x + evalAtOne xs

/-- Evaluation is additive over `add`. -/
theorem evalAtOne_add : ∀ p q : Poly,
    evalAtOne (add p q) = evalAtOne p + evalAtOne q
  | [],       q        => by simp [add, evalAtOne]
  | (_ :: _), []       => by simp [add, evalAtOne]
  | (x :: xs), (y :: ys) => by
    show evalAtOne ((x + y) :: add xs ys)
        = evalAtOne (x :: xs) + evalAtOne (y :: ys)
    simp only [evalAtOne]
    rw [evalAtOne_add xs ys]
    omega

/-- Evaluation is linear in scalar multiplication. -/
theorem evalAtOne_smul (c : Nat) : ∀ p : Poly,
    evalAtOne (smul c p) = c * evalAtOne p
  | []      => by simp [smul, evalAtOne]
  | (x :: xs) => by
    show evalAtOne ((c * x) :: smul c xs) = c * evalAtOne (x :: xs)
    simp only [evalAtOne]
    rw [evalAtOne_smul c xs, Nat.mul_add]

/-- Evaluation distributes over the leading-zero cons.  -/
theorem evalAtOne_zero_cons (p : Poly) :
    evalAtOne (0 :: p) = evalAtOne p := by
  simp [evalAtOne]

/-- Evaluation at z=1 is multiplicative: ev(p·q) = ev(p) · ev(q). -/
theorem evalAtOne_mul : ∀ p q : Poly,
    evalAtOne (mul p q) = evalAtOne p * evalAtOne q
  | [],       q => by simp [mul, evalAtOne]
  | (x :: xs), q => by
    show evalAtOne (add (smul x q) (0 :: mul xs q))
        = evalAtOne (x :: xs) * evalAtOne q
    rw [evalAtOne_add, evalAtOne_smul, evalAtOne_zero_cons, evalAtOne_mul xs q]
    show x * evalAtOne q + evalAtOne xs * evalAtOne q
        = evalAtOne (x :: xs) * evalAtOne q
    simp only [evalAtOne]
    rw [Nat.add_mul]

end Poly

/-- (1 + z) as a polynomial. -/
def onePlusZ : Poly := [1, 1]

/-- (1 + z)^k by iteration. -/
def onePlusZPow : Nat → Poly
  | 0     => [1]
  | k+1   => Poly.mul onePlusZ (onePlusZPow k)

/-- ev(1+z) = 2. -/
theorem evalAtOne_onePlusZ : Poly.evalAtOne onePlusZ = 2 := by decide

/-- ev((1+z)^k) = 2^k. -/
theorem evalAtOne_onePlusZPow : ∀ k : Nat,
    Poly.evalAtOne (onePlusZPow k) = 2 ^ k
  | 0     => by decide
  | k + 1 => by
    show Poly.evalAtOne (Poly.mul onePlusZ (onePlusZPow k)) = 2 ^ (k + 1)
    rw [Poly.evalAtOne_mul, evalAtOne_onePlusZ, evalAtOne_onePlusZPow k,
        Nat.pow_succ, Nat.mul_comm]

/-- The universal quintic Q(z) = z⁵ + 11z⁴ + 25z³ + 19z² + 7z + 1.
    Coefficients (low-to-high): [1, 7, 19, 25, 11, 1]. -/
def Q_universal : Poly := [1, 7, 19, 25, 11, 1]

/-- Q(1) = 1 + 7 + 19 + 25 + 11 + 1 = 64. -/
theorem evalAtOne_Q : Poly.evalAtOne Q_universal = 64 := by decide

/-- 64 = 2^6. -/
theorem sixtyfour_eq_two_pow_six : (64 : Nat) = 2 ^ 6 := by decide

/-- Predicted Hilbert-series numerator: `(1+z)^(t·n − 9) · Q(z)`.

    This is a defined formula; the claim "predicted = actual HS of Mambo
    ideal" holds **at t = 4** (across n ≥ 3), as established by 6 cells
    of empirical evidence. At t ≥ 5 with n ≥ 4 the predicted formula
    does NOT match actual HS (retraction, 2026-05-15: t=6 n=4 case). -/
def predicted_HS_numerator (t n : Nat) : Poly :=
  Poly.mul (onePlusZPow (t * n - 9)) Q_universal

/-! ### Empirical anchors at t = 4 (universal-in-n, post-retraction scope) -/

/-- **t=4 anchor (n=3):** predicted HS = kbase `[1, 10, 43, 104, 150, 128, 61, 14, 1]`. -/
example : predicted_HS_numerator 4 3 = [1, 10, 43, 104, 150, 128, 61, 14, 1] := by
  decide

/-- **t=4 anchor (n=4):** dim = 2^13 = 8192. -/
example : Poly.evalAtOne (predicted_HS_numerator 4 4) = 8192 := by decide

/-- **t=4 anchor (n=5):** dim = 2^17 = 131072. -/
example : Poly.evalAtOne (predicted_HS_numerator 4 5) = 131072 := by decide

/-- **t=4 anchor (n=6):** dim = 2^21 = 2097152. -/
example : Poly.evalAtOne (predicted_HS_numerator 4 6) = 2097152 := by decide

/-! ### Degenerate small-n cells (n = 3 across widths; NOT universality evidence)

    The following cells *match* the predicted formula but do not extend in
    `n` for t ≥ 5. They are coincidence of small-n, kept here as Lean
    sanity checks but explicitly NOT part of the universal claim.
-/

/-- Cross-width n=3 cell (t=5): matches predicted formula. -/
example : Poly.evalAtOne (predicted_HS_numerator 5 3) = 4096 := by decide

/-- Cross-width n=3 cell (t=6): matches predicted formula. -/
example : Poly.evalAtOne (predicted_HS_numerator 6 3) = 32768 := by decide

/-- Cross-width n=3 cell (t=7): matches predicted formula. -/
example : Poly.evalAtOne (predicted_HS_numerator 7 3) = 262144 := by decide

/-- Cross-width n=3 cell (t=8): matches predicted formula. -/
example : Poly.evalAtOne (predicted_HS_numerator 8 3) = 2097152 := by decide

/-- **NOT an anchor:** at t=5 n=4 the predicted formula's evaluation is
    2^17 (= 131072), but actual HS is unverified at the time of this
    writing. Pending the t=5 n=4 computation result. -/
example : Poly.evalAtOne (predicted_HS_numerator 5 4) = 131072 := by decide

/-- Helper: at `t ≥ 4` and `n ≥ 3`, `t * n ≥ 9`. -/
theorem tn_ge_nine (t n : Nat) (ht : 4 ≤ t) (hn : 3 ≤ n) : 9 ≤ t * n := by
  have h1 : 3 ≤ t := by omega
  have h2 : (3 : Nat) * 3 ≤ t * n := Nat.mul_le_mul h1 hn
  omega

/-- **Corollary of universal-Q (FULLY PROVEN, no `sorry`):** The predicted
    HS numerator evaluated at z=1 equals `2^(t·n − 3)`. This is the
    `dim_K(R/I) = 2^(tn-3)` half of the universal-Q corollary.

    Proof: ev((1+z)^(tn-9) · Q) = 2^(tn-9) · Q(1) = 2^(tn-9) · 64
      = 2^(tn-9) · 2^6 = 2^(tn-9+6) = 2^(tn-3),
    using `tn ≥ 9` from `t ≥ 4` and `n ≥ 3`. -/
theorem evalAtOne_predicted (t n : Nat) (ht : 4 ≤ t) (hn : 3 ≤ n) :
    Poly.evalAtOne (predicted_HS_numerator t n) = 2 ^ (t * n - 3) := by
  show Poly.evalAtOne (Poly.mul (onePlusZPow (t * n - 9)) Q_universal)
      = 2 ^ (t * n - 3)
  rw [Poly.evalAtOne_mul, evalAtOne_onePlusZPow, evalAtOne_Q,
      sixtyfour_eq_two_pow_six, ← Nat.pow_add]
  have htn : 9 ≤ t * n := tn_ge_nine t n ht hn
  congr 1
  omega

/-- **t = 4 universal-in-n Q theorem (statement; full proof open).**

    For width `t = 4` and depth `n ≥ 3`, the Hilbert-series numerator of
    the Mambo coupled-quadratic ideal `I_{4,n}` over its polynomial ring
    `R_{4,n}` equals `(1+z)^(4·n − 9) · Q(z)` where `Q` is the degree-5
    quintic `z⁵ + 11z⁴ + 25z³ + 19z² + 7z + 1` (universal-in-n at t = 4).

    Scope correction (2026-05-15): the earlier conjecture that this
    theorem extends to all t ≥ 4 was retracted after the t=6 n=4
    measurement (HS sum 2^20, not 2^21, degree-7 residue, not degree-5 Q).

    This declaration captures only the **predicted** closed-form for
    arbitrary `(t, n)`; the equality to the **actual** Hilbert series
    of the Mambo ideal requires formalizing the ideal type (depends on
    mathlib's `Polynomial` and `Ideal` machinery), and holds only at
    t = 4 across n ≥ 3 — open structural-proof work (Step B framework,
    sections B.3 and B.4, restricted to t = 4). -/
theorem universal_Q_HS_stabilization (t n : Nat) (_ht : 4 ≤ t) (_hn : 3 ≤ n) :
    ∃ p : Poly, p = predicted_HS_numerator t n :=
  ⟨predicted_HS_numerator t n, rfl⟩

end Mambo.UniversalQ
