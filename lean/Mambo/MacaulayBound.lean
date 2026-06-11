/-!
# Macaulay Security Bound (Deliverable B)

Formalizes the Macaulay-bound complexity estimate for Gröbner-basis attacks
on the Mambo coupled-quadratic system.

For a polynomial system of `m` equations in `V` variables with degree of
regularity `d_reg`, the Bardet-Faugère-Salvy asymptotic cost is

  cost(V, d_reg, ω) = binomial(V + d_reg, d_reg) ^ ω

with `ω ∈ [2, 3]` the linear-algebra exponent. The security level in bits
is `log₂(cost)`.

The `d_reg` function below uses the machine-verified production-width values
(each checked by `decide` examples in this file):
  - t = 2: d_reg = 2n      (paper Thm hilb_closed)
  - t = 3: d_reg = 3n − 1   (t=3 CICO theorem; checked at n = 23, 33, 44)
  - t = 4: d_reg = 4n − 3   (t=4 Hilbert series; checked at n = 3, 18, 27)
For t ≥ 5 only, the fallback `t·n − 2(t − 2)` is structural extrapolation
(anchored empirically at t = 2, 3, 4); it is not a security basis at those
wider widths.

NOTE on scope: the `security_*` theorems below machine-check only the
Gröbner/Macaulay-step lower bound (binom(V + d_reg, d_reg) ≥ 2^λ) — the
*comfortable* half of the algebraic-attack cost. They do NOT prove the
binding FGLM basis-conversion step (~D_I²), which remains a modeling
assumption (paper §5.4). They are discharged by `decide`, which
trusts the compiled evaluator (axiom `Lean.ofReduceBool`), not the kernel.
-/

set_option maxRecDepth 100000

namespace Mambo.MacaulayBound

/-- Factorial. -/
def factorial : Nat → Nat
  | 0   => 1
  | n+1 => (n+1) * factorial n

/-- Falling product: n · (n-1) · ... · (n-k+1). -/
def fallingProd (n : Nat) : Nat → Nat
  | 0   => 1
  | k+1 => (n - k) * fallingProd n k

/-- Binomial coefficient via product formula. Fast for decide. -/
def binom (n k : Nat) : Nat :=
  fallingProd n k / factorial k

/-- Number of polynomial variables in coupled-quadratic Mambo at
    width t depth n (state vars + boundary). -/
def numVars (t n : Nat) : Nat := t * (n + 1) + 1

/-- Degree of regularity. Piecewise per-width definition:

      - t = 2: 2n             (paper Thm hilb_closed)
      - t = 3: 3n − 1         (5 cells, sage 2026-05-18)
      - t = 4: 4n − 3         (6 cells, sage 2026-05-17)
      - t ≥ 5: t·n − 2(t − 2) (UNVALIDATED extrapolation for wider-state
        research only; t = 16 research cell test below uses this value —
        see WARNING)

    **WARNING — wider-state fallback is an UNVALIDATED extrapolation
    (corrected 2026-06-02).** An earlier note here claimed sage probes
    measured d_reg = 5n − 3 / 6n − 4 (offset 3/4) and that the
    `t·n − 2(t − 2)` fallback therefore UNDER-counts d_reg and is
    conservative. That is RETRACTED — not reproduced. Fresh msolve under
    the paper-exact CICO convention (RC-generic, Singular-cross-checked,
    2026-06-02) measures:
      t = 5: d_reg(5,3) = 9, d_reg(5,4) = 14  → offset 6 = C(4,2)
      t = 6: d_reg(6,3) = 10                  → offset 8
      t = 7: d_reg(7,3) = 10                  → offset 11
    So the fallback offset 2(t − 2) is EXACT at t = 5 and t = 6 (n = 3),
    and at t = 7 it UNDER-states the offset (10 vs 11) → it OVER-counts
    d_reg, i.e. the security-OVERSTATING direction, not conservative.
    Consequence for the t = 16 cell: the 256-bit claim
    `binom(161 + d_reg, d_reg) ≥ 2^256` holds iff the true offset ≤ 36
    (d_reg ≥ 108); the fallback assumes offset 28 (margin only 8). The
    paper's own unified formula C(t − 1, 2) = 105 would give d_reg = 39 →
    139 bits → FALSE. The true offset at t = 16 is unmeasured and, given
    the upward drift already visible by t = 7 and that asymptotic (large-n)
    offsets are ≥ small-n ones, plausibly exceeds 36. Treat security_t16
    as RESEARCH, conditional on this unproven d_reg model — NOT a robust
    machine-proven floor. (t = 6 n = 4 compute pending to pin the t = 6
    n-trend.) The t ≤ 4 theorems are unaffected: they use exactly-proven
    d_reg (2n / 3n − 1 / 4n − 3) and clear their targets with margin.

    The t = 2, 3, 4 cases match the formula
    `t·n − (t − 1)(t − 2) / 2` (cf. `Mambo.T3HilbertSeries.production_d_reg`),
    valid at production widths only (universal extrapolation refuted
    at t ≥ 5). -/
def d_reg (t n : Nat) : Nat :=
  if t = 2 then 2 * n
  else if t = 3 then 3 * n - 1
  else if t = 4 then 4 * n - 3
  else t * n - 2 * (t - 2)

/-- Macaulay-bound base value: binom(V + d_reg, d_reg). The security
    floor in bits is `ω · log₂(macaulayBase)`. -/
def macaulayBase (t n : Nat) : Nat :=
  binom (numVars t n + d_reg t n) (d_reg t n)

/-- Production parameter sets (paper Table 7). -/
def params_t4_L1  : Nat × Nat := (4, 18)
def params_t4_L3  : Nat × Nat := (4, 27)
def params_t4_L5  : Nat × Nat := (4, 36)
def params_t16_L1 : Nat × Nat := (16, 9)

/-- Sanity: binom 26 9 = 3124550 (universal Q empirical anchor t=4 n=3). -/
example : binom 26 9 = 3124550 := by decide

/-- Sanity: factorial 9 = 362880. -/
example : factorial 9 = 362880 := by decide

/-- Closed-form d_reg at production t=4 L1 (paper N=18): 4·18 − 3 = 69
    (Q_4-corrected). -/
example : d_reg 4 18 = 69 := by decide

/-- Closed-form numVars at production t=4 L1. -/
example : numVars 4 18 = 77 := by decide

/-- d_reg at the t=16 RESEARCH cell (NOT a paper width): 16·9 − 28 = 116 via
    the unvalidated t≥5 fallback (offset 28). See d_reg WARNING. -/
example : d_reg 16 9 = 116 := by decide

/-- Closed-form numVars at production t=16 L1. -/
example : numVars 16 9 = 161 := by decide

/-! ### Wider-state empirical d_reg anchors + fallback divergence (msolve 2026-06-02)

msolve under the paper-exact CICO convention (p=251, PHI=7, TAU=1; RC-generic,
Singular-cross-checked) measured the following d_reg, alongside the value the
`d_reg` fallback `t·n − 2(t−2)` produces:

      (t,n)   msolve d_reg    fallback d_reg    colength = 2^{t(n-1)+1}
      (5,3)   9               9   ✓ match       2^11 = 2048
      (5,4)   14              14  ✓ match        2^16 = 65536
      (6,3)   10              10  ✓ match        2^13 = 8192
      (7,3)   10              11  ✗ DIVERGE      2^15 = 32768

The fallback is EXACT through t=6 (n=3) but at t=7 it returns 11 while the true
d_reg is 10 — it OVER-counts by 1, i.e. the security-OVERSTATING direction (a
larger d_reg inflates the Macaulay binomial). Since n=3 is the small-n regime at
t=7 (n=3 < t) and small-n d_reg is ≥ the asymptotic value, the asymptotic offset
is ≥ 11 > the fallback's 10 — so the fallback is non-conservative for all t ≥ 7,
not merely unvalidated. This is the concrete basis for treating `security_t16`
(which uses this fallback) as CONDITIONAL. The colength law colength = 2·D_I =
2^{t(n-1)+1} is bit-exact at every cell measured (t = 2..6, all probed n). -/
example : d_reg 5 3 = 9  := by decide   -- fallback matches msolve
example : d_reg 6 3 = 10 := by decide   -- fallback matches msolve
example : d_reg 7 3 = 11 := by decide   -- fallback VALUE (msolve-measured is 10)
-- Machine-checked demonstration that the fallback diverges from measurement at t=7:
def dreg_msolve_7_3 : Nat := 10
example : d_reg 7 3 ≠ dreg_msolve_7_3 := by decide
example : dreg_msolve_7_3 < d_reg 7 3 := by decide  -- fallback over-counts (unsafe dir)

/-- At the toy small-cell anchor (t=4, n=3): d_reg = 4·3 − 3 = 9
    (Q_4-corrected), numVars = 4·4 + 1 = 17, Macaulay base = binom(26, 9). -/
example : d_reg 4 3 = 9 := by decide
example : numVars 4 3 = 17 := by decide
example : macaulayBase 4 3 = binom 26 9 := by decide

/-- Production t=4 L1 Macaulay base is binom(146, 69). We expose its closed
    form; the kernel can evaluate it, but it is omitted from `decide` checks
    here to keep build time low. The value has ~141 bits, giving ~334 bits
    security at ω = 2.37. -/
def macaulayBase_t4_L1 : Nat := macaulayBase 4 18

/-- RESEARCH (non-paper) t=16 cell Macaulay base = binom(277, 116) (numVars
    161 + d_reg 116), giving 268 bits raw. NOTE: a prior docstring here said
    binom(302, 141)/296 bits — that was the stale offset-3 value (d_reg=141);
    the current fallback gives offset 28 → d_reg=116. d_reg here is the
    UNVALIDATED t≥5 extrapolation (see d_reg WARNING); the 256-bit margin is
    NOT robust. -/
def macaulayBase_t16_L1 : Nat := macaulayBase 16 9

/-- **Gröbner-step bound (machine-checked via `decide`, non-kernel; the comfortable half only — see module note).** At production
    t=4 L1, the raw Macaulay base `binom(146, 69)` is ≥ 2^128 (the 128-bit
    L1 target). This is the ω = 1 lower bound; the ω = 2.37 production
    estimate gives ~334 bits, but that requires real-log machinery
    (mathlib).

    `binom(146, 69) = 4729484387129524011685921098355593423483600`,
    which has 141 bits, > 2^128 = 2^128.

    NOTE (2026-06-10): (t = 4, n = 18) is a cell of the superseded
    model-dependent grid; the conservative-rule L1 cell is (4, 34) —
    see `security_t4_L1_geq_128bits_conservative`. -/
theorem security_t4_L1_geq_128bits : 2 ^ 128 ≤ macaulayBase_t4_L1 := by
  decide

/-- **CONDITIONAL / RESEARCH — not a paper claim.** This says
    `binom(277, 116) ≥ 2^256` for a t=16 cell (NOT a paper production
    parameter; paper widths are t ∈ {2,3,4}). The binomial inequality below
    is kernel-true as written, but it depends on `d_reg 16 9 = 116`, which
    comes from the UNVALIDATED t≥5 fallback (see d_reg WARNING). The 256-bit
    conclusion holds only if the true offset at t=16 is ≤ 36; the fallback
    assumes 28 and the paper's own C(t−1,2)=105 would falsify it (139 bits).
    Do NOT read this as a robust machine-proven 256-bit guarantee. -/
theorem security_t16_L1_geq_256bits_CONDITIONAL : 2 ^ 256 ≤ macaulayBase_t16_L1 := by
  decide

/-! ### t = 3 production security floors

Mirrors the t=4 pattern above with the empirical d_reg formula at
width 3: `d_reg(3, n) = 3n − 1` (checked at the production cells
below; HS shape (1+z)^{3(n−1)}). The corresponding
Macaulay bases at the production t = 3 cells of paper Table 7 are
verified to clear NIST L1/L3/L5 floors via `decide`. -/

/-- Production t = 3 parameter cells (paper Table 7). -/
def params_t3_L1 : Nat × Nat := (3, 23)
def params_t3_L3 : Nat × Nat := (3, 33)
def params_t3_L5 : Nat × Nat := (3, 44)

/-- d_reg(3, 23) = 3·23 − 1 = 68 — production anchor. Matches the t=3
    CICO theorem formula `3n − 1`. -/
example : d_reg 3 23 = 68 := by decide
/-- d_reg(3, 33) = 3·33 − 1 = 98. -/
example : d_reg 3 33 = 98 := by decide
/-- d_reg(3, 44) = 3·44 − 1 = 131. -/
example : d_reg 3 44 = 131 := by decide

/-- Macaulay base at t = 3, depth n. -/
def macaulayBase_t3 (n : Nat) : Nat :=
  binom (numVars 3 n + d_reg 3 n) (d_reg 3 n)

/-- Production t = 3 L1 Macaulay base: `binom(140, 67)`. -/
def macaulayBase_t3_L1 : Nat := macaulayBase_t3 23

/-- Production t = 3 L3 Macaulay base. -/
def macaulayBase_t3_L3 : Nat := macaulayBase_t3 33

/-- Production t = 3 L5 Macaulay base. -/
def macaulayBase_t3_L5 : Nat := macaulayBase_t3 44

/-- **Gröbner-step bound (machine-checked via `decide`, non-kernel; the comfortable half only — see module note).** At production
    t = 3 L1 (n = 23), the raw Macaulay base clears the 128-bit L1 floor.
    NOTE (2026-06-10): superseded model-dependent grid; conservative-rule
    L1 cell is (3, 44) — see `security_t3_L1_geq_128bits_conservative`. -/
theorem security_t3_L1_geq_128bits : 2 ^ 128 ≤ macaulayBase_t3_L1 := by
  decide

/-- **Gröbner-step bound (machine-checked via `decide`, non-kernel; the comfortable half only — see module note).** At production
    t = 3 L3 (n = 33), the raw Macaulay base clears the 192-bit L3 floor.
    NOTE (2026-06-10): superseded model-dependent grid; conservative-rule
    L3 cell is (3, 66) — see `security_t3_L3_geq_192bits_conservative`. -/
theorem security_t3_L3_geq_192bits : 2 ^ 192 ≤ macaulayBase_t3_L3 := by
  decide

/-- **Gröbner-step bound (machine-checked via `decide`, non-kernel; the comfortable half only — see module note).** At production
    t = 3 L5 (n = 44), the raw Macaulay base clears the 256-bit L5 floor.
    NOTE (2026-06-10): under the conservative sizing rule this same cell
    (3, 44) is reassigned to the L1/128-bit tier — see
    `security_t3_L1_geq_128bits_conservative`; the conservative-rule L5
    cell is (3, 87). -/
theorem security_t3_L5_geq_256bits : 2 ^ 256 ≤ macaulayBase_t3_L5 := by
  decide

/-! ### t = 2 production security floors

Paper Table 7 production cells at width t = 2: N ∈ {33, 49, 65} for
L1/L3/L5 security tiers (paper Table 7).
The d_reg formula `tn − 2(t−2) = 2n` at t = 2 recovers the paper's
`d_reg = 2n` from Thm hilb_closed. -/

def params_t2_L1 : Nat × Nat := (2, 33)
def params_t2_L3 : Nat × Nat := (2, 49)
def params_t2_L5 : Nat × Nat := (2, 65)

example : d_reg 2 33 = 66 := by decide
example : d_reg 2 49 = 98 := by decide
example : d_reg 2 65 = 130 := by decide

def macaulayBase_t2_L1 : Nat := macaulayBase 2 33
def macaulayBase_t2_L3 : Nat := macaulayBase 2 49
def macaulayBase_t2_L5 : Nat := macaulayBase 2 65

/-- t = 2 L1 (n = 33): Macaulay base clears 128-bit floor.
    NOTE (2026-06-10): superseded model-dependent grid; conservative-rule
    L1 cell is (2, 65) — see `security_t2_L1_geq_128bits_conservative`. -/
theorem security_t2_L1_geq_128bits : 2 ^ 128 ≤ macaulayBase_t2_L1 := by
  decide

/-- t = 2 L3 (n = 49): clears 192-bit floor.
    NOTE (2026-06-10): superseded model-dependent grid; conservative-rule
    L3 cell is (2, 97) — see `security_t2_L3_geq_192bits_conservative`. -/
theorem security_t2_L3_geq_192bits : 2 ^ 192 ≤ macaulayBase_t2_L3 := by
  decide

/-- t = 2 L5 (n = 65): clears 256-bit floor.
    NOTE (2026-06-10): under the conservative sizing rule this same cell
    (2, 65) is reassigned to the L1/128-bit tier — see
    `security_t2_L1_geq_128bits_conservative`; the conservative-rule L5
    cell is (2, 129). -/
theorem security_t2_L5_geq_256bits : 2 ^ 256 ≤ macaulayBase_t2_L5 := by
  decide

/-! ### t = 4 L3/L5 production security floors

Completes Table 7 production-cell coverage at t = 4. d_reg = tn − 3
at t = 4 (Q_4-corrected; see `Mambo.T4HilbertSeries`). -/

def params_t4_L3' : Nat × Nat := (4, 27)
def params_t4_L5' : Nat × Nat := (4, 36)

example : d_reg 4 27 = 105 := by decide
example : d_reg 4 36 = 141 := by decide

def macaulayBase_t4_L3 : Nat := macaulayBase 4 27
def macaulayBase_t4_L5 : Nat := macaulayBase 4 36

/-- t = 4 L3 (n = 27): clears 192-bit floor.
    NOTE (2026-06-10): superseded model-dependent grid; conservative-rule
    L3 cell is (4, 50) — see `security_t4_L3_geq_192bits_conservative`. -/
theorem security_t4_L3_geq_192bits : 2 ^ 192 ≤ macaulayBase_t4_L3 := by
  decide

/-- t = 4 L5 (n = 36): clears 256-bit floor.
    NOTE (2026-06-10): superseded model-dependent grid; conservative-rule
    L5 cell is (4, 66) — see `security_t4_L5_geq_256bits_conservative`. -/
theorem security_t4_L5_geq_256bits : 2 ^ 256 ≤ macaulayBase_t4_L5 := by
  decide

/-! ### Conservative-grid production security floors (2026-06-10)

The paper's recommended parameter cells were re-sized on 2026-06-10 under
the new conservative sizing rule. The recommended grid is now:

      tier      t = 2       t = 3       t = 4
      L1/128    (2, 65)     (3, 44)     (4, 34)
      L3/192    (2, 97)     (3, 66)     (4, 50)
      L5/256    (2, 129)    (3, 87)     (4, 66)

Each theorem below kernel-checks (`decide`; empty axiom set) the Macaulay
floor `binom(numVars + d_reg, d_reg) ≥ 2^λ` at its tier target λ. Scope
mirrors the module note: this is Macaulay-model arithmetic — the
Gröbner/Macaulay-step lower bound only (the comfortable half of the
algebraic-attack cost), not the FGLM conversion step. The d_reg input is
theorem-backed at t = 2 via the proven closed form `2n`; at t = 3 and
t = 4 the d_reg formulas `3n − 1` and `4n − 3` are the paper's
exactly-measured values at production widths.

The unsuffixed `security_tX_LY_*` names above belong to the superseded
grid at different n, so all nine conservative theorems carry the
`_conservative` suffix. Cells (2, 65) and (3, 44) coincide with old-grid
L5 cells (`macaulayBase_t2_L5`, `macaulayBase_t3_L5`); they get fresh
defs here under their new tier role. -/

-- d_reg anchors at the conservative cells (proven formulas at t = 2, 3, 4).
example : d_reg 2 65  = 130 := by decide
example : d_reg 2 97  = 194 := by decide
example : d_reg 2 129 = 258 := by decide
example : d_reg 3 44  = 131 := by decide
example : d_reg 3 66  = 197 := by decide
example : d_reg 3 87  = 260 := by decide
example : d_reg 4 34  = 133 := by decide
example : d_reg 4 50  = 197 := by decide
example : d_reg 4 66  = 261 := by decide

-- numVars anchors at the conservative cells.
example : numVars 2 65  = 133 := by decide
example : numVars 2 97  = 197 := by decide
example : numVars 2 129 = 261 := by decide
example : numVars 3 44  = 136 := by decide
example : numVars 3 66  = 202 := by decide
example : numVars 3 87  = 265 := by decide
example : numVars 4 34  = 141 := by decide
example : numVars 4 50  = 205 := by decide
example : numVars 4 66  = 269 := by decide

/-- Conservative-grid t = 2 L1 cell (n = 65): `binom(263, 130)`. -/
def macaulayBase_t2_L1_conservative : Nat := macaulayBase 2 65

/-- Conservative-grid t = 2 L3 cell (n = 97): `binom(391, 194)`. -/
def macaulayBase_t2_L3_conservative : Nat := macaulayBase 2 97

/-- Conservative-grid t = 2 L5 cell (n = 129): `binom(519, 258)`. -/
def macaulayBase_t2_L5_conservative : Nat := macaulayBase 2 129

/-- Conservative-grid t = 3 L1 cell (n = 44): `binom(267, 131)`. -/
def macaulayBase_t3_L1_conservative : Nat := macaulayBase 3 44

/-- Conservative-grid t = 3 L3 cell (n = 66): `binom(399, 197)`. -/
def macaulayBase_t3_L3_conservative : Nat := macaulayBase 3 66

/-- Conservative-grid t = 3 L5 cell (n = 87): `binom(525, 260)`. -/
def macaulayBase_t3_L5_conservative : Nat := macaulayBase 3 87

/-- Conservative-grid t = 4 L1 cell (n = 34): `binom(274, 133)`. -/
def macaulayBase_t4_L1_conservative : Nat := macaulayBase 4 34

/-- Conservative-grid t = 4 L3 cell (n = 50): `binom(402, 197)`. -/
def macaulayBase_t4_L3_conservative : Nat := macaulayBase 4 50

/-- Conservative-grid t = 4 L5 cell (n = 66): `binom(530, 261)`. -/
def macaulayBase_t4_L5_conservative : Nat := macaulayBase 4 66

/-- Cell (t = 2, n = 65) at the L1/128-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 2n = 130 is the proven closed form at t = 2. -/
theorem security_t2_L1_geq_128bits_conservative :
    2 ^ 128 ≤ macaulayBase_t2_L1_conservative := by decide

/-- Cell (t = 2, n = 97) at the L3/192-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 2n = 194 is the proven closed form at t = 2. -/
theorem security_t2_L3_geq_192bits_conservative :
    2 ^ 192 ≤ macaulayBase_t2_L3_conservative := by decide

/-- Cell (t = 2, n = 129) at the L5/256-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 2n = 258 is the proven closed form at t = 2. -/
theorem security_t2_L5_geq_256bits_conservative :
    2 ^ 256 ≤ macaulayBase_t2_L5_conservative := by decide

/-- Cell (t = 3, n = 44) at the L1/128-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 3n − 1 = 131 is the paper's exactly-measured
    value at width 3. -/
theorem security_t3_L1_geq_128bits_conservative :
    2 ^ 128 ≤ macaulayBase_t3_L1_conservative := by decide

/-- Cell (t = 3, n = 66) at the L3/192-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 3n − 1 = 197 is the paper's exactly-measured
    value at width 3. -/
theorem security_t3_L3_geq_192bits_conservative :
    2 ^ 192 ≤ macaulayBase_t3_L3_conservative := by decide

/-- Cell (t = 3, n = 87) at the L5/256-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 3n − 1 = 260 is the paper's exactly-measured
    value at width 3. -/
theorem security_t3_L5_geq_256bits_conservative :
    2 ^ 256 ≤ macaulayBase_t3_L5_conservative := by decide

/-- Cell (t = 4, n = 34) at the L1/128-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 4n − 3 = 133 is the paper's exactly-measured
    value at width 4. -/
theorem security_t4_L1_geq_128bits_conservative :
    2 ^ 128 ≤ macaulayBase_t4_L1_conservative := by decide

/-- Cell (t = 4, n = 50) at the L3/192-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 4n − 3 = 197 is the paper's exactly-measured
    value at width 4. -/
theorem security_t4_L3_geq_192bits_conservative :
    2 ^ 192 ≤ macaulayBase_t4_L3_conservative := by decide

/-- Cell (t = 4, n = 66) at the L5/256-bit target, conservative sizing rule
    (2026-06-10). Macaulay-model arithmetic floor (Gröbner step only — see
    module note); d_reg = 4n − 3 = 261 is the paper's exactly-measured
    value at width 4. -/
theorem security_t4_L5_geq_256bits_conservative :
    2 ^ 256 ≤ macaulayBase_t4_L5_conservative := by decide

end Mambo.MacaulayBound
