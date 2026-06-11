# Mambo — Reproducibility Artifact

This repository is the supplementary-materials artifact for the paper

> **Mambo: Degree-Two Hashing for Zero-Knowledge Proof Systems**

It contains everything needed to independently reproduce the paper's
structural and security claims: the machine-checked Lean 4 development, a
self-contained reference implementation with known-answer test vectors, and
the algebraic reproducer scripts behind the degree, regularity-degree,
Hilbert-series, colength, effective-degree, monodromy, and round-reduced
attack results.

It deliberately does **not** include the production backend integrations,
the signature layer, or any benchmarking/engineering material. Those are not
needed to verify the paper and are not part of this artifact.

---

## License and intellectual-property notice

The Mambo construction is **patent pending** (USPTO provisional, March 2026).

All material in this artifact is licensed under the **Business Source License
1.1 (BUSL-1.1)** — see [`LICENSE`](LICENSE). The Additional Use Grant
explicitly permits **non-commercial academic research (including
cryptanalysis and benchmarking), academic verification, audit use, peer
review, and personal evaluation/testing**. Integrating the construction into
any system that processes live transactions or serves end users in production
requires a separate commercial license from the licensor.

No rights to the construction transfer by virtue of this artifact or the
associated publication.

---

## Layout

```
lean/        Lean 4 formalization (sorry-free machine-checked proofs)
reference/   Reference implementation + known-answer test vectors (KATs)
analysis/    Algebraic reproducer scripts (Sage / Singular / Python)
LICENSE      BUSL-1.1 with the research/verification/audit Additional Use Grant
```

---

## Claim → file → command map

Each row lists where a paper claim is reproduced and how to run it. `n` is the
round count and `t` the state width.

### Round-function degree growth (degree theorem)

| Backing | File |
|---|---|
| Round map definition (t=4 coupled-quadratic) | `lean/Mambo/RoundFunction.lean` |
| Degree-doubling per round | `lean/Mambo/DegreeGrowth.lean`, `lean/Mambo/T3DegreeTracking.lean`, `lean/Mambo/TGeneralDegreeTracking.lean` |
| Universal elimination degree `D_I = 2^{t(n-1)}` (finrank bridge) | `lean/Mambo/TFinrankBridge.lean`, `lean/Mambo/TGeneralDegreeTracking.lean` |

### Regularity degree `d_reg` (= 2n, 3n−1, 4n−3 at t = 2, 3, 4)

| Backing | File / command |
|---|---|
| `d_reg = 2n` at t=2 (`boolQuot_finrank`) | `lean/Mambo/T2SqReduction.lean`, `lean/Mambo/T2GeneralN.lean` |
| t=3 and t=4 production `d_reg` cells | `lean/Mambo/T3HilbertSeries.lean`, `lean/Mambo/T4HilbertSeries.lean` |
| Macaulay/Bardet-Faugère-Salvy cost floors | `lean/Mambo/MacaulayBound.lean`, `lean/Mambo/R1CSCost.lean` |
| Empirical `d_reg` sweep over t=2,4 | `sage analysis/syzygy_hunt_sage/mambo_d_reg_paper.sage`; `python3 analysis/mambo_dreg_t24_subprocess.py` (results in `analysis/dreg_t24_linux_results.json`, `analysis/dreg_t24_wider_results.json`) |

### Hilbert series and the residue staircase

| Backing | File / command |
|---|---|
| Closed-form Hilbert series, t=4 universal-in-n corollary | `lean/Mambo/UniversalQ.lean`, `lean/Mambo/T3HilbertSeries.lean`, `lean/Mambo/T4HilbertSeries.lean` |
| Hilbert-series computation | `python3 analysis/mambo_hilbert_series.py`, `python3 analysis/mambo_hilbert_t32.py` |
| Staircase classification + numerator-residue reconstruction | `sage analysis/hilbert_residue_staircase.sage` |
| Large-n Hilbert series | `sage analysis/syzygy_hunt_sage/mambo_hs_large_n.sage` |
| Universal-Q window membership | `sage analysis/q4_window_membership.sage` |
| Universal-Q residue with generic window initialization (Q_4 theorem) | `sage analysis/q4_window_generic_init.sage` |
| Non-telescoping verification | `sage analysis/nontelescoping_verify.sage` |

### Colength (= 2·D_I = 2^{tn−(t−1)})

| Backing | File / command |
|---|---|
| Structural proof of the wider-state colength closed form | `analysis/widerstate_dreg_proof.md` |
| Cyclic-reduction finrank (t=3) | `lean/Mambo/T3FirstCellCyclic.lean`, `lean/Mambo/T3UniversalN.lean` |

### Effective degree `D_eff` (c = 1 specialization)

| Backing | File / command |
|---|---|
| `D_eff` specialization analysis | `sage analysis/widet_specialization.sage`, `sage analysis/widet_specialization_adversarial.sage` |
| `D_eff` proof verification | `sage analysis/widet_deff_proof_verify.sage` |
| Multi-block chaining-value specialization (Section 5.12) | `sage analysis/multiblock_chaining.sage` |

### Monodromy / squarefreeness certificates ("no exploitable structure")

| Backing | File / command |
|---|---|
| Galois-group / irreducibility certificates over BN254 | `sage analysis/monodromy_certificates/cert_bn254.sage` |
| Generic-constants formulation over Mersenne-31 | `sage analysis/monodromy_certificates/cert_m31_generic.sage` |
| Indecomposability / Morse argument | `sage analysis/monodromy_certificates/indec_morse_bn254.sage` |
| n=6 and n=5 irreducibility | `sage analysis/monodromy_certificates/n6_and_n5irr.sage` |
| Independent re-check of every certificate row | `sage analysis/monodromy_certificates/verify_certs.sage` |

### Round-reduced practical attacks

| Backing | File / command |
|---|---|
| Round-reduced attack engine (univariate-eliminant and full Gröbner) | `sage analysis/round_reduced_attacks.sage <uni\|gb> <t> <n> <kb\|bn254\|pm> [seed]` |
| Sweep driver | `analysis/run_sweep.sh OUTLOG "uni 2 3 kb 600" ...` |
| Writeup + raw results | `analysis/round_reduced_attacks.md`, `analysis/round_reduced_results.csv`, `analysis/sweep_results.log` |

### Gröbner-basis / CICO ideal structure

| Backing | File / command |
|---|---|
| CICO Gröbner-basis computation (generic field) | `python3 analysis/mambo_groebner_singular.py` |
| CICO Gröbner-basis over BN254 | `python3 analysis/mambo_gb_bn254_singular.py` |
| Summary | `analysis/mambo_groebner_results.md` |
| Char-eq, graded-hom, syzygy reproducers | `analysis/syzygy_hunt_sage/` |

### Algebraic immunity (AI(R) = 2)

| Backing | File |
|---|---|
| AI(R) = 2 at t=2 and universal t | `lean/Mambo/T114AlgebraicImmunity.lean`, `lean/Mambo/T114UniversalT.lean` |
| No affine-equivalent Flystel pair | `lean/Mambo/NoFlystelPair.lean` |

### Known-answer test vectors (KATs) / cross-implementation parity

| Backing | File / command |
|---|---|
| Reference implementation + KAT self-check | `python3 reference/independent_reference.py` |
| Test-vector generator | `python3 reference/test_vectors.py` |
| Test-vector data | `reference/test_vectors.json`, `reference/test/test_vectors.json`, `reference/test/parity_vectors_bn254.json` |
| Round-constant specification | `reference/round_constants.md` |
| Round-constant generator (canonical derive-fresh t=2 scheme) | `python3 reference/gen_rc_derivefresh.py [field] [n]` |

---

## Build and run

### Lean development

The Lean toolchain version is pinned by `lean/lean-toolchain`
(`leanprover/lean4:v4.18.0`). With [`elan`](https://github.com/leanprover/elan)
installed:

```sh
elan default leanprover/lean4:v4.18.0   # optional; the toolchain file pins it
cd lean
lake exe cache get                      # fetch the prebuilt mathlib cache
lake build Mambo                        # build all modules (sorry-free)
```

The only network access required is the mathlib cache fetch. The proofs build
with zero `sorry`; the headline axioms across the directory are the three
standard ones (`propext`, `Classical.choice`, `Quot.sound`) plus
`Lean.ofReduceBool` for the native-arithmetic `decide` checks.

### Reference implementation and KATs

```sh
python3 reference/independent_reference.py   # runs all KAT comparisons, prints PASS/FAIL
python3 reference/test_vectors.py
```

Pure Python 3, no third-party dependencies.

### Algebraic reproducers

- `*.sage` files run under [SageMath](https://www.sagemath.org/): `sage analysis/<script>.sage`
- `*.sing` files run under [Singular](https://www.singular.uni-kl.de/): `Singular analysis/<script>.sing`
- `*.py` files run under Python 3 (some shell out to Singular for the heavy
  computations).

Several scripts write transient working files to the system temp directory and
require Sage/Singular (and, for some larger cells, `msolve`) on the `PATH`.

---

## Known gaps and reproduction caveats

- **Canonical t=2 round-constant scheme is derive-fresh.** A permutation of N
  rounds derives 2N fresh constants with the d-series offset equal to N, so the
  constant set is N-dependent (the constants for N=82 are not an extension of
  the N=65 set). This is the single canonical scheme across the reference
  implementation, the generator (`reference/gen_rc_derivefresh.py`), and the
  round-constant specification; the earlier modular-cycling 65-entry table
  coincided with derive-fresh only at exactly N=65. KATs are included at the
  analysis-minimum cell (n=65) and the recommended deployment cell (n=82). The
  Goldilocks test vectors use the conforming multiplier phi=7, matching the
  other supported fields.

- **Recommended deployment cells carry a +25% margin over the analysis
  minimum.** Throughout, the *minimum* cells (t=2 n=65, t=3 n=44, t=4 n=34) are
  the falsification targets — the smallest round counts at which the effective
  degree reaches the security floor — and the *recommended* cells (e.g. t=2
  n=82, t=3 n=55, t=4 n=44) add the +25% engineering margin. Reproductions that
  target the security claim should run against the minimum cells.

- **Some wider-width (t ≥ 5) checks are compute-bound.** The colength closed
  form `2^{tn−(t−1)}` is verified bit-exact across the full grid t = 2..7. The
  `d_reg` constant offset is confirmed for t ≤ 5; for t ≥ 6 it is an open
  question pending a single large compute cell, as documented honestly in
  `analysis/widerstate_dreg_proof.md`.
