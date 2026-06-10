import Mambo.RoundFunction
import Mambo.MacaulayBound
import Mambo.UniversalQ
import Mambo.BooleanReduction
import Mambo.RegimePicture
import Mambo.MathlibBridge
import Mambo.MathlibBridgeMulti
import Mambo.B2Enumeration
import Mambo.MathlibBridgeDim
import Mambo.MamboIdeal
import Mambo.MathlibBridgeMultiDim
import Mambo.T3HilbertSeries
import Mambo.T4HilbertSeries
import Mambo.DegreeGrowth
import Mambo.R1CSCost
import Mambo.T2CicoIdeal
import Mambo.T2GeneralN
import Mambo.T2SqReduction
import Mambo.T3CicoIdeal
import Mambo.T3GeneralN
import Mambo.T3FirstCellCyclic
import Mambo.T3UniversalN
import Mambo.T4CicoIdeal
import Mambo.LiWangNonApplicable
import Mambo.NoFlystelPair

/-!
# Mambo — Lean 4 Formalization

All listed theorems build with zero `sorry` tactics. Headline axioms
across the directory: `[propext, Classical.choice, Quot.sound]`
(standard) and `Lean.ofReduceBool` (native arithmetic).

Modules:

- **`Mambo.RoundFunction`** — t=4 coupled-quadratic permutation round
  (matches the production t = 4 round function)

- **`Mambo.MacaulayBound`** — Gröbner-basis cost estimate. Production
  security floors fully proven via `native_decide`:
    - t=2  L1/L3/L5 ≥ 2^128/2^192/2^256
    - t=3  L1/L3/L5 ≥ 2^128/2^192/2^256 (empirical d_reg = 3n−1)
    - t=4  L1/L3/L5 ≥ 2^128/2^192/2^256
    - t=16 L1 ≥ 2^256

- **`Mambo.UniversalQ`** — Hilbert-series stabilization at **t = 4
  universal-in-n** (post-retraction scope). Dimension corollary
  `dim_K(R/I) = 2^(4n − 3)` fully proven

- **`Mambo.BooleanReduction`** — Step B.1 Boolean-reduction dimension
  contribution fully proven; explicit kbase decomposition recorded at
  t=4 n=3 (9 Boolean + 1 Q-residual + 6 eliminated)

- **`Mambo.RegimePicture`** — three-regime classification: t=2 (paper),
  t=4 (universal-in-n Q_4), t ≥ 6 n=4. Dim formula at t ≥ 6 n=4 regime
  fully proven: `2^(t·4 − 4)` at z=1

- **`Mambo.MathlibBridgeDim`** — single-variable Boolean quotient
  `K[X]/(X² − X)` has K-finrank 2 (via `AdjoinRoot.powerBasis`)

- **`Mambo.MathlibBridgeMultiDim`** — **MAIN MATHLIB BRIDGE.**
  `boolQuot_finrank` proves `finrank K (MvPolynomial (Fin n) K / boolIdeal n) = 2^n`
  for all n by induction. Concrete corollaries at n = 1, 2, 3, 4, 5, 10.

- **`Mambo.T3HilbertSeries`** — t=3 HS-factor dimensional corollaries
  (Boolean count `3n − 2`, dim = `2^{3n − 2}`, d_reg = `3n − 1`).
  Anchor cells n = 2..5 via `decide`.

- **`Mambo.T4HilbertSeries`** — t=4 HS factorisation
  `(1+z)^{4n − 9} · Q_4(z)` with d_reg = `4n − 3`. Anchor cells n = 3..8.

- **`Mambo.MamboIdeal`** — typed Mambo CICO ideal in `MvPolynomial
  (VarIndex t n) K`. Round constraints + boundary generators + the
  full `mamboIdeal`. Non-triviality proven via eval-at-origin.

- **`Mambo.DegreeGrowth`** — paper Thm `thm:degree`, Lem `lem:recurrence`,
  Cor `cor:alfom`. Closed-form `dPsi(n) = 4^n` + `dTheta(n) = 2·4^{n-1}`
  + ALFOM = 1.0 numerical core fully proven.

- **`Mambo.R1CSCost`** — paper Prop `prop:cost`, Cor `cor:mpc_cost`,
  Prop `prop:wider_alfom`. R1CS cost = 2n at t = 2 (general: tn);
  ALFOM = 1.0 at any width t ≥ 1.

- **`Mambo.T2CicoIdeal`** — paper coupled-sequential round (canonical
  t = 2 instance). n=1 base-case dim theorem
  `t2_n1_dim : dim_K (MvPoly(VarIndex 2 1) K ⧸ mamboT2Ideal_n=1) = 2`
  via AlgEquiv to `AdjoinRoot(X² − C(τ − c_0))`. Proves paper
  Thm `thm:hilb_closed` at n = 1 (`2 = 2^{2·1-1}`).

- **`Mambo.T2GeneralN`** — **PAPER `thm:hilb_closed` AT GENERAL n.**
  `t2_general_dim : ∀ n ≥ 1, dim_K (MvPoly(VarIndex 2 n) K ⧸ mamboT2Ideal_n)
  = 2·4^{n-1}`. Fully proven via symbolic iterators + AdjoinRoot bridge.

- **`Mambo.T2SqReduction`** — paper `lem:sq_reduction` formalisation.
  Cases A and B (interior) and R3 (last-cell elimination, inversion-free)
  fully proven. Cases C and D (boundary `t_{n-1}²` and `s_n²` reductions)
  closed via `linear_combination` after Fin-index alignment.

- **`Mambo.T3CicoIdeal`** — t=3 Mambo CICO ideal (analog of t=2). Three
  chain-coupled round-constraint families + boundary pins.

- **`Mambo.T3GeneralN`** — symbolic iterator scaffold for t=3 (three
  mutually recursive iterators in `Polynomial K`). General-n
  AdjoinRoot bridge deferred pending FGLM-cyclic-module machinery.

- **`Mambo.T4CicoIdeal`** — t=4 Mambo CICO ideal (analog of t=2/t=3).
  Four chain-coupled round-constraint families + boundary pins.

- **`Mambo.LiWangNonApplicable`** — lane #14 (Li-Wang subspace trails).
  Formal proof at t=2 that the only solution to
  `b² = 0 ∧ 49a² + 2b²·rc[0] = 0` is `a = b = 0`.

- **`Mambo.NoFlystelPair`** — lane #12 (Anemoi-Flystel adaptation).
  Witnesses the `ψ²` monomial in `mambo_s0.support` with coefficient 1,
  demonstrating degree-2 incompatibility with α≥3 Flystel pair.

Toolchain: Lean 4 v4.18.0, Mathlib.
-/
