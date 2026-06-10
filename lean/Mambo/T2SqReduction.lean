import Mambo.T2CicoIdeal

/-!
# Mambo t = 2 Square Reduction Lemma (paper `lem:sq_reduction`)

Formalises paper Lemma "Square reduction" (Appendix
`app:dreg:reductions`): for every free variable `x ∈ F_n`,

  x² ≡ a_0 + Σ_{y ∈ F_n} a_y · y   (mod mamboT2Ideal)

with scalars `a_0, a_y ∈ K`. Translation between paper and Lean
variable conventions:

  paper `t_i`  ↔  Lean `X(0, i)` (= `sVar K n 0 i`)
  paper `s_i`  ↔  Lean `X(1, i)` (= `sVar K n 1 i`)

The four paper cases (see paper `lem:sq_reduction` proof):
  Case A: `s_i² ≡ t_{i+1} - φ·t_i - c_i` for `i ∈ {0,..,n-2}` (this file)
  Case B: `t_i² ≡ s_i - φ·s_{i-1} - d_{i-1}` for `i ∈ {1,..,n-2}`
  Case C: `t_{n-1}² ≡ τ - φ·t_{n-1} - c_{n-1}` (uses R2)
  Case D: `s_n² ≡ 2(τ² + d_{n-1})·s_n - φ³·t_{n-1} + ...` (uses R2, R3)

Cases A and B are the "interior" cases and follow directly from the
round-constraint generators of `mamboT2Ideal`. Cases C and D additionally
use the boundary-end constraint and the elimination R3 of `s_{n-1}`
via the final round constraint — these are stated here (no `sorry`)
in Case A; Cases B/C/D follow the same template and are scheduled for
the next iteration.
-/

namespace Mambo.T2SqReduction

open Mambo.T2CicoIdeal Mambo.B2Enumeration MvPolynomial

variable (K : Type*) [Field K]

/-! ### Case A: interior `s_i² ≡ t_{i+1} - φ·t_i - c_i` (mod I), i ∈ {0,..,n-2}

Direct consequence of `roundConstraintTheta i c_i ∈ mamboT2Ideal`:
  `t_{i+1} - φ·t_i - s_i² - c_i = 0` (in the quotient)
  ⇒ `s_i² = t_{i+1} - φ·t_i - c_i` (in the quotient).
-/

/-- **Case A of paper `lem:sq_reduction`** — interior `s_i` (= X(1, i)):

    `(X(1, i))² ≡ X(0, i+1) - 7·X(0, i) - c_i   (mod mamboT2Ideal)`

    for `i ∈ Fin n` (covers paper indices `i ∈ {0,..,n-1}`, including the
    `i ∈ {0,..,n-2}` interior case; for `i = n-1` the RHS contains
    `t_n = X(0, n)` which is the boundary, but the linear-modulo-I
    statement still holds and the boundary is killed in the quotient
    separately).

    Proven by passing to the quotient ring and using the round
    constraint generator. -/
theorem sq_reduction_s_interior (n : Nat) (c_seq d_seq : Fin n → K) (tau : K)
    (i : Fin n) :
    ((MvPolynomial.X (1, i.castSucc) : MvPolynomial (VarIndex 2 n) K)) ^ 2
      - (MvPolynomial.X (0, i.succ) - (phi : K) • MvPolynomial.X (0, i.castSucc)
         - MvPolynomial.C (c_seq i))
      ∈ mamboT2Ideal K n c_seq d_seq tau := by
  -- The LHS (x² - linear-RHS) is exactly the negation of roundConstraintTheta i (c_seq i).
  -- roundConstraintTheta = X(0, i+1) - φ·X(0, i) - X(1, i)·X(1, i) - C(c_i)
  -- so negation = X(1, i)² + φ·X(0, i) - X(0, i+1) + C(c_i)
  -- We rearrange and use ring to match LHS.
  have h_gen : roundConstraintTheta K n i (c_seq i) ∈ mamboT2Ideal K n c_seq d_seq tau :=
    Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))
  -- Show LHS = -1 · roundConstraintTheta (modulo ring rearrangement).
  have h_eq :
      ((MvPolynomial.X (1, i.castSucc) : MvPolynomial (VarIndex 2 n) K)) ^ 2
        - (MvPolynomial.X (0, i.succ) - (phi : K) • MvPolynomial.X (0, i.castSucc)
           - MvPolynomial.C (c_seq i))
      = -1 * roundConstraintTheta K n i (c_seq i) := by
    unfold roundConstraintTheta sVar
    ring
  rw [h_eq]
  exact Ideal.mul_mem_left _ _ h_gen

/-! ### Case B: interior `t_i² ≡ s_i - φ·s_{i-1} - d_{i-1}` (mod I), i ∈ {1,..,n-2}

Direct consequence of `roundConstraintPsi (i-1) d_{i-1} ∈ mamboT2Ideal` after
unfolding: `s_i - φ·s_{i-1} - t_i² - d_{i-1} = 0` in the quotient.

Note: paper has `s_i = φ·s_{i-1} + t_i² + d_{i-1}` from g_{2i+2}. But our
`roundConstraintPsi r d_r` uses the FRESHLY computed `X(0, r+1)` (not the
old `X(0, r)`), per paper line 320 ("sequential coupling"). So our
`roundConstraintPsi` reads `X(1, r+1) - φ·X(1, r) - X(0, r+1)² - d_r`,
giving `X(1, r+1) - φ·X(1, r) - X(0, r+1)² - d_r = 0` mod I.

Rearranged: `X(0, r+1)² = X(1, r+1) - φ·X(1, r) - d_r` mod I. So Case B in
the form of this file becomes: for `r ∈ Fin n`,

  `(X(0, r+1))² ≡ X(1, r+1) - φ·X(1, r) - d_r   (mod mamboT2Ideal)`. -/

/-- **Case B of paper `lem:sq_reduction`** — `t_{r+1}` (= X(0, r+1)):

    `(X(0, r+1))² ≡ X(1, r+1) - 7·X(1, r) - d_r   (mod mamboT2Ideal)`

    Mirror of Case A using `roundConstraintPsi`. -/
theorem sq_reduction_t_interior (n : Nat) (c_seq d_seq : Fin n → K) (tau : K)
    (r : Fin n) :
    ((MvPolynomial.X (0, r.succ) : MvPolynomial (VarIndex 2 n) K)) ^ 2
      - (MvPolynomial.X (1, r.succ) - (phi : K) • MvPolynomial.X (1, r.castSucc)
         - MvPolynomial.C (d_seq r))
      ∈ mamboT2Ideal K n c_seq d_seq tau := by
  have h_gen : roundConstraintPsi K n r (d_seq r) ∈ mamboT2Ideal K n c_seq d_seq tau :=
    Ideal.subset_span (Or.inl (Or.inr ⟨r, rfl⟩))
  have h_eq :
      ((MvPolynomial.X (0, r.succ) : MvPolynomial (VarIndex 2 n) K)) ^ 2
        - (MvPolynomial.X (1, r.succ) - (phi : K) • MvPolynomial.X (1, r.castSucc)
           - MvPolynomial.C (d_seq r))
      = -1 * roundConstraintPsi K n r (d_seq r) := by
    unfold roundConstraintPsi sVar
    ring
  rw [h_eq]
  exact Ideal.mul_mem_left _ _ h_gen

/-! ### Auxiliary: R3 elimination of `s_{n-1}` via boundary + last `ψ` round

Paper's R3 (eq:appR3): `s_{n-1} ≡ φ⁻¹(s_n - τ² - d_{n-1})` (mod I). In our
inversion-free statement: `φ·s_{n-1} - s_n + τ² + d_{n-1} ∈ I`.

Derivation (n+1 = paper n, working in Fin (n+1+1)):
1. boundaryEnd: `X(0, n+1) - C τ ∈ I` → `X(0, n+1)² - C(τ²) ∈ I` (multiply by `X(0, n+1) + C τ`).
2. roundConstraintPsi at r = ⟨n, _⟩ : Fin (n+1):
   `X(1, n+1) - φ·X(1, n) - X(0, n+1)² - C d_n ∈ I`.
3. Combine 1+2: `X(1, n+1) - φ·X(1, n) - C(τ²) - C d_n ∈ I`. Negate. -/

/-- **Paper R3 (`eq:appR3`) in inversion-free form**:
    `φ·s_{n-1} - s_n + τ² + d_{n-1} ∈ I` (for n+1 the round count).

    Pre-multiplying by `φ⁻¹` (in any field with `(7 : K) ≠ 0`) recovers
    the paper's `s_{n-1} ≡ φ⁻¹(s_n - τ² - d_{n-1})`. The inversion-free
    statement is used inside Cases C/D of `lem:sq_reduction` to avoid
    introducing `φ⁻¹` into the basis-coefficient bookkeeping. -/
theorem R3_eliminate_s_nm1 (n : Nat) (c_seq d_seq : Fin (n + 1) → K) (tau : K) :
    let r_last : Fin (n + 1) := ⟨n, by omega⟩
    (phi : K) • (MvPolynomial.X (1, r_last.castSucc)
                  : MvPolynomial (VarIndex 2 (n + 1)) K)
      - MvPolynomial.X (1, r_last.succ)
      + MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq r_last)
      ∈ mamboT2Ideal K (n + 1) c_seq d_seq tau := by
  intro r_last
  -- Round-constraint generator at r_last : Fin (n+1).
  have h_psi : roundConstraintPsi K (n + 1) r_last (d_seq r_last)
        ∈ mamboT2Ideal K (n + 1) c_seq d_seq tau :=
    Ideal.subset_span (Or.inl (Or.inr ⟨r_last, rfl⟩))
  -- Boundary-end generator: X(0, n+1) - C τ ∈ I.
  have h_bd : boundaryEnd K (n + 1) tau ∈ mamboT2Ideal K (n + 1) c_seq d_seq tau :=
    Ideal.subset_span (Or.inr (Or.inr rfl))
  -- (X(0, n+1) - τ) * (X(0, n+1) + τ) = X(0, n+1)² - τ² ∈ I.
  -- Note: r_last.succ = ⟨n+1, _⟩, defeq to ⟨n+1, Nat.lt_succ_self (n+1)⟩.
  have h_sq_diff :
      (MvPolynomial.X (0, r_last.succ)
        : MvPolynomial (VarIndex 2 (n + 1)) K) ^ 2
        - MvPolynomial.C (tau ^ 2)
      ∈ mamboT2Ideal K (n + 1) c_seq d_seq tau := by
    -- r_last.succ : Fin (n+2) at value n+1; defeq to ⟨n+1, Nat.lt_succ_self (n+1)⟩
    -- which is the index used in `boundaryEnd K (n+1) tau`.
    have h_idx : r_last.succ
              = (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp [r_last]
    rw [h_idx]
    have h_eq :
        ((MvPolynomial.X (0, (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 1 + 1)))
          : MvPolynomial (VarIndex 2 (n + 1)) K)) ^ 2
          - MvPolynomial.C (tau ^ 2)
        = boundaryEnd K (n + 1) tau
          * (MvPolynomial.X (0, (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 1 + 1)))
              + MvPolynomial.C tau) := by
      unfold boundaryEnd sVar
      rw [show (MvPolynomial.C (tau ^ 2)
                : MvPolynomial (VarIndex 2 (n + 1)) K)
              = (MvPolynomial.C tau) ^ 2 by rw [map_pow]]
      ring
    rw [h_eq]
    exact Ideal.mul_mem_right _ _ h_bd
  -- Sum: roundConstraintPsi + (X(0, r_last.succ)² - τ²) ∈ I.
  have h_sum := Ideal.add_mem _ h_psi h_sq_diff
  -- The negation of the sum is exactly the R3 form.
  have h_eq :
      (phi : K) • (MvPolynomial.X (1, r_last.castSucc)
                    : MvPolynomial (VarIndex 2 (n + 1)) K)
        - MvPolynomial.X (1, r_last.succ)
        + MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq r_last)
      = -1 * (roundConstraintPsi K (n + 1) r_last (d_seq r_last)
              + ((MvPolynomial.X (0, r_last.succ)
                  : MvPolynomial (VarIndex 2 (n + 1)) K) ^ 2
                  - MvPolynomial.C (tau ^ 2))) := by
    unfold roundConstraintPsi sVar
    ring
  rw [h_eq]
  exact Ideal.mul_mem_left _ _ h_sum

/-! ### Cases C and D of paper `lem:sq_reduction`

Sage-anchored at paper_n ∈ {4, 5, 6}: both
identities reduce to 0 mod Mambo Gröbner basis over F_8209.

Derivation: Case C = φ · (Case B at r = ⟨k, _⟩) + R3. -/

set_option maxHeartbeats 2000000 in
/-- **Case C of paper `lem:sq_reduction`** — boundary reduction of
    `t_{n-1}²` (= `X(0, n-1)²` at paper-n = k + 2):

    `φ · t_{n-1}² + φ²·s_{n-2} + C(τ²) + C(d_{n-1}) + φ·C(d_{n-2})
      - X(1, n) ∈ mamboT2Ideal`.

    Proof: linear combination of Case B at r = ⟨k, _⟩ (the second-to-
    last round) and R3 (boundary-end + last ψ-constraint). -/
theorem sq_reduction_case_C (k : Nat) (c_seq d_seq : Fin (k + 2) → K) (tau : K) :
    let n_minus_2 : Fin (k + 2) := ⟨k, by omega⟩
    (phi : K) • ((MvPolynomial.X (0, n_minus_2.succ)
                   : MvPolynomial (VarIndex 2 (k + 2)) K)) ^ 2
      + (phi : K) ^ 2 • MvPolynomial.X (1, n_minus_2.castSucc)
      + MvPolynomial.C (tau ^ 2)
      + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩)
      + (phi : K) • MvPolynomial.C (d_seq n_minus_2)
      - MvPolynomial.X (1, ⟨k + 2, Nat.lt_succ_self _⟩)
      ∈ mamboT2Ideal K (k + 2) c_seq d_seq tau := by
  intro n_minus_2
  -- Case B at r = n_minus_2 : Fin (k+2):
  --   X(0, n_minus_2.succ)² - (X(1, n_minus_2.succ) - φ·X(1, n_minus_2.castSucc)
  --     - C(d_seq n_minus_2)) ∈ I
  have h_caseB := sq_reduction_t_interior K (k + 2) c_seq d_seq tau n_minus_2
  -- R3 at n = k+1 (ideal over Fin (k+2) round indices, Fin (k+3) cells):
  --   φ·X(1, r_last.castSucc) - X(1, r_last.succ) + C(τ²) + C(d_seq r_last) ∈ I
  -- where r_last : Fin (k+2) at value k+1.
  have h_R3 := R3_eliminate_s_nm1 K (k + 1) c_seq d_seq tau
  -- φ · h_caseB ∈ I.
  have h_phi_caseB := Ideal.mul_mem_left
    (mamboT2Ideal K (k + 2) c_seq d_seq tau)
    (MvPolynomial.C (phi : K)) h_caseB
  -- Sum.
  have h_sum := Ideal.add_mem _ h_phi_caseB h_R3
  -- Fin alignment: r_last.castSucc = n_minus_2.succ; r_last.succ = ⟨k+2, _⟩.
  have h_idx1 :
      (⟨k + 1, by omega⟩ : Fin (k + 2)).castSucc
        = n_minus_2.succ := by
    apply Fin.ext; simp [n_minus_2]
  have h_idx2 :
      (⟨k + 1, by omega⟩ : Fin (k + 2)).succ
        = (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)) := by
    apply Fin.ext; simp
  have h_idx3 :
      (⟨k + 1, by omega⟩ : Fin (k + 2))
        = (⟨k + 1, by omega⟩ : Fin (k + 2)) := rfl
  -- Show the goal equals the sum.
  have h_eq :
      (phi : K) • ((MvPolynomial.X (0, n_minus_2.succ)
                     : MvPolynomial (VarIndex 2 (k + 2)) K)) ^ 2
        + (phi : K) ^ 2 • MvPolynomial.X (1, n_minus_2.castSucc)
        + MvPolynomial.C (tau ^ 2)
        + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩)
        + (phi : K) • MvPolynomial.C (d_seq n_minus_2)
        - MvPolynomial.X (1, ⟨k + 2, Nat.lt_succ_self _⟩)
      = MvPolynomial.C (phi : K)
          * (((MvPolynomial.X (0, n_minus_2.succ)
                : MvPolynomial (VarIndex 2 (k + 2)) K)) ^ 2
              - (MvPolynomial.X (1, n_minus_2.succ)
                  - (phi : K) • MvPolynomial.X (1, n_minus_2.castSucc)
                  - MvPolynomial.C (d_seq n_minus_2)))
        + ((phi : K) • (MvPolynomial.X (1, (⟨k + 1, by omega⟩ : Fin (k + 2)).castSucc)
                          : MvPolynomial (VarIndex 2 (k + 2)) K)
            - MvPolynomial.X (1, (⟨k + 1, by omega⟩ : Fin (k + 2)).succ)
            + MvPolynomial.C (tau ^ 2)
            + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩)) := by
    rw [h_idx1, h_idx2]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_pow]
    ring
  rw [h_eq]
  exact h_sum

set_option maxHeartbeats 8000000 in
/-- **Case D of paper `lem:sq_reduction`** — boundary reduction of `s_n²`
    (= `X(1, n)²` at paper-n = k + 2):

    `s_n² - 2(τ² + d_{n-1})·s_n + (τ² + d_{n-1})²
      - φ²·τ + φ³·t_{n-1} + φ²·c_{n-1} ∈ mamboT2Ideal`.

    Derivation: combine R3-squared (via Ideal.mul_mem with conjugate R3')
    and theta + boundaryEnd at r = n-1, both giving expressions for
    `φ²·s_{n-1}²`. Subtracting yields Case D. Sage-anchored at paper_n
    ∈ {4, 5, 6}. -/
theorem sq_reduction_case_D (k : Nat) (c_seq d_seq : Fin (k + 2) → K) (tau : K) :
    ((MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)))
      : MvPolynomial (VarIndex 2 (k + 2)) K)) ^ 2
      - (2 : K) • ((MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩))
                     * MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3))))
      + (MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩)) ^ 2
      - (phi : K) ^ 2 • MvPolynomial.C tau
      + (phi : K) ^ 3 • MvPolynomial.X (0, (⟨k + 1, by omega⟩ : Fin (k + 3)))
      + (phi : K) ^ 2 • MvPolynomial.C (c_seq ⟨k + 1, by omega⟩)
      ∈ mamboT2Ideal K (k + 2) c_seq d_seq tau := by
  -- R3 at n = k+1 gives ideal membership over Fin (k+2) round indices.
  have h_R3 := R3_eliminate_s_nm1 K (k + 1) c_seq d_seq tau
  -- R3 statement uses r_last : Fin (k+2) at value k+1; .castSucc = ⟨k+1, _⟩, .succ = ⟨k+2, _⟩.
  -- Pin those Fin values to the explicit form used in our goal.
  have h_idx_cast : ((⟨k + 1, by omega⟩ : Fin (k + 2))).castSucc
                      = (⟨k + 1, by omega⟩ : Fin (k + 3)) := by
    apply Fin.ext; simp
  have h_idx_succ : ((⟨k + 1, by omega⟩ : Fin (k + 2))).succ
                      = (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)) := by
    apply Fin.ext; simp
  -- Rewrite h_R3 to use explicit Fin indices.
  simp only [h_idx_cast, h_idx_succ] at h_R3
  -- Conjugate R3' poly. R3' · R3 ∈ I.
  have h_R3_sq := Ideal.mul_mem_left
    (mamboT2Ideal K (k + 2) c_seq d_seq tau)
    ((phi : K) • MvPolynomial.X (1, (⟨k + 1, by omega⟩ : Fin (k + 3)))
      + MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)))
      - MvPolynomial.C (tau ^ 2)
      - MvPolynomial.C (d_seq ⟨k + 1, by omega⟩)) h_R3
  -- theta at r_last : Fin (k+2) at value k+1.
  have h_theta : roundConstraintTheta K (k + 2) ⟨k + 1, by omega⟩
                    (c_seq ⟨k + 1, by omega⟩)
        ∈ mamboT2Ideal K (k + 2) c_seq d_seq tau :=
    Ideal.subset_span (Or.inl (Or.inl ⟨⟨k + 1, by omega⟩, rfl⟩))
  have h_bd : boundaryEnd K (k + 2) tau ∈ mamboT2Ideal K (k + 2) c_seq d_seq tau :=
    Ideal.subset_span (Or.inr (Or.inr rfl))
  -- theta - bd ∈ I.
  have h_theta_minus_bd := Ideal.sub_mem _ h_theta h_bd
  -- φ²·(theta - bd) ∈ I.
  have h_phi2_theta_minus_bd := Ideal.mul_mem_left
    (mamboT2Ideal K (k + 2) c_seq d_seq tau)
    (MvPolynomial.C ((phi : K) ^ 2)) h_theta_minus_bd
  -- Sum, then negate (Case D LHS = -(R3'·R3 + φ²·(theta - bd))).
  have h_sum := Ideal.add_mem _ h_R3_sq h_phi2_theta_minus_bd
  -- Multiply by C(-1) to negate.
  have h_neg_sum := Ideal.mul_mem_left
    (mamboT2Ideal K (k + 2) c_seq d_seq tau) (MvPolynomial.C (-1 : K)) h_sum
  -- Equality: Case D LHS = -(sum-polynomial).
  have h_eq :
      ((MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)))
        : MvPolynomial (VarIndex 2 (k + 2)) K)) ^ 2
        - (2 : K) • ((MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩))
                      * MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3))))
        + (MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩)) ^ 2
        - (phi : K) ^ 2 • MvPolynomial.C tau
        + (phi : K) ^ 3 • MvPolynomial.X (0, (⟨k + 1, by omega⟩ : Fin (k + 3)))
        + (phi : K) ^ 2 • MvPolynomial.C (c_seq ⟨k + 1, by omega⟩)
      = MvPolynomial.C (-1 : K) *
          (((phi : K) • MvPolynomial.X (1, (⟨k + 1, by omega⟩ : Fin (k + 3)))
              + MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)))
              - MvPolynomial.C (tau ^ 2)
              - MvPolynomial.C (d_seq ⟨k + 1, by omega⟩))
            * ((phi : K) • (MvPolynomial.X (1, (⟨k + 1, by omega⟩ : Fin (k + 3)))
                              : MvPolynomial (VarIndex 2 (k + 2)) K)
                - MvPolynomial.X (1, (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)))
                + MvPolynomial.C (tau ^ 2) + MvPolynomial.C (d_seq ⟨k + 1, by omega⟩))
            + MvPolynomial.C ((phi : K) ^ 2)
              * (roundConstraintTheta K (k + 2) ⟨k + 1, by omega⟩
                    (c_seq ⟨k + 1, by omega⟩)
                  - boundaryEnd K (k + 2) tau)) := by
    unfold roundConstraintTheta boundaryEnd sVar
    have h1 : (⟨k + 1, by omega⟩ : Fin (k + 2)).succ
                = (⟨k + 2, Nat.lt_succ_self _⟩ : Fin (k + 3)) := by
      apply Fin.ext; simp
    have h2 : (⟨k + 1, by omega⟩ : Fin (k + 2)).castSucc
                = (⟨k + 1, by omega⟩ : Fin (k + 3)) := by
      apply Fin.ext; simp
    rw [h1, h2]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_pow,
               map_neg, map_one, map_ofNat]
    ring
  rw [h_eq]
  exact h_neg_sum

end Mambo.T2SqReduction
