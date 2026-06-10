# Round-reduced practical attacks on Mambo sponge-CICO

Engine: `round_reduced_attacks.sage`. Raw, crash-safe results:
`round_reduced_results.csv` (one fsync'd line per completed cell;
externally-killed cells get a DNF line appended by the driver).

Convention: sponge CICO on the capacity-1 hash surface — capacity cells = 0
at input, rate cell x_1(n) = tau at output, single unknown x_1(0). This is
the convention under which the paper's univariate-eliminant cost model
(D_eff = 2^{t(n-1)-max(t-2,0)}) is stated. Eliminant degree D_I = 2^{t(n-1)}. phi = 7, random round constants,
seed 20260610.

Two attacks:
- `uni` — build the dense univariate eliminant f_n(x_1(0)) by iterated
  composition, then F_p root-find with sage's generic `.roots()`
  (NTL/flint dense root-finding, NOT the theoretical Otilde(D_I) optimum).
- `gb` — the multivariate iterated quadratic system (one new variable per
  state component per round), Groebner basis via msolve (F4), colength via
  `vector_space_dimension`. Over a small prime (`pm`, p=1048573 < 2^28) the
  full variety is extracted and every root forward-verified; over KoalaBear
  / BN254 only GB + colength are computed (msolve variety/parametrization is
  not run there — for BN254 msolve rejects the base field entirely).

All cells run nice -n 19, strictly sequential, gtimeout-capped, on an
M-series MacBook Air. peak_mem_mb is in-process RUSAGE_SELF maxrss (sage
baseline ~240 MB; only the large dense uni cells move it).

## Results

Fields: kb = KoalaBear (p = 2^31-2^24+1, 31-bit), pm = 20-bit verification
prime, bn254 = BN254 scalar field (254-bit).

### univariate eliminant (uni)

| t | n | field | D_I | solve_s | total_s | peakMB | outcome |
|---|---|-------|-----|---------|---------|--------|---------|
| 2 | 2 | kb | 4 | 0.0013 | 0.0019 | 240 | verified |
| 2 | 3 | kb | 16 | 0.0016 | 0.0022 | 240 | verified |
| 2 | 4 | kb | 64 | 0.0035 | 0.0043 | 240 | verified |
| 2 | 5 | kb | 256 | 0.0173 | 0.0181 | 240 | verified |
| 2 | 6 | kb | 1024 | 0.2915 | 0.2925 | 239 | verified |
| 2 | 7 | kb | 4096 | 7.1476 | 7.1495 | 249 | verified |
| 2 | 8 | kb | 16384 | 88.272 | 88.275 | 319 | verified |
| 2 | 9 | kb | 65536 | — | >480 | — | DNF (8-min cap) |
| 3 | 2 | kb | 8 | 0.0006 | 0.0008 | 240 | verified |
| 3 | 3 | kb | 64 | 0.0010 | 0.0012 | 240 | verified |
| 3 | 4 | kb | 512 | 0.0509 | 0.0517 | 240 | verified |
| 3 | 5 | kb | 4096 | 2.1322 | 2.1334 | 248 | verified |
| 2 | 4 | bn254 | 64 | 0.4420 | 0.4467 | 241 | verified |
| 2 | 6 | bn254 | 1024 | 20.710 | 20.721 | 459 | verified |

### Groebner / msolve (gb)

| t | n | field | D_I | solve_s | total_s | outcome |
|---|---|-------|-----|---------|---------|---------|
| 2 | 2..10 | kb | 4..262144 | 0.009–0.05 | 0.02–0.06 | dim=D_I (GB+colength ONLY, no root) |
| 3 | 2..6 | kb | 8..32768 | 0.016–0.28 | 0.03–0.35 | dim=D_I (GB+colength ONLY, no root) |
| 2 | 4 | bn254 | 64 | — | 0.22 | ERR: msolve base field unsupported |

Full GB solve (F4 + FGLM variety + forward-verify) over the small prime pm,
solve_s NOW includes the variety/root-extraction step (engine corrected — see
caveat 2):

| t | n | field | D_I | GB(F4)_s | full solve_s | outcome |
|---|---|-------|-----|----------|--------------|---------|
| 2 | 4 | pm | 64 | 0.006 | 0.024 | dim=D_I / verified |
| 2 | 5 | pm | 256 | 0.006 | 0.034 | dim=D_I / verified |
| 2 | 6 | pm | 1024 | 0.006 | 0.356 | dim=D_I / verified |
| 2 | 7 | pm | 4096 | 0.006 | 20.535 | dim=D_I / verified |

Every gb colength equals D_I = 2^{t(n-1)} exactly (n=2..10 at t=2, n=2..6 at
t=3): the eliminant-degree model is confirmed bit-exact at every cell. Every
small-prime (pm) variety root forward-evaluates to tau. Every uni root
forward-evaluates to tau.

## Fitted scaling (fit range stated; no extrapolation)

uni, KoalaBear, t=2, solve_s as a power of D_I, fit over D_I in [256, 16384]
(n = 5..8): log-log slope per consecutive 4x in D_I is
{2.03, 2.31, 1.81}, mean ~2.05. So as MEASURED with sage's generic dense
root-finder,

    uni solve_s ~ D_I^2.0   over n=5..8 at t=2 on KoalaBear.

That is ~16x per added round (each +1 in n is x4 in D_I). This is the cost of
sage's default dense `.roots()`, NOT the theoretical Otilde(D_I) attack of
the simpler-argument note — the practical sage path is roughly quasi-quadratic
in D_I. uni at t=3 over n=4..5 (D_I 512->4096) gives slope ~1.80, consistent
with the t=2 exponent (the cost tracks D_I, not (t,n) separately).

gb (msolve), two costs to keep separate:
- F4 GB-construction of the iterated triangular system: ~linear in round count
  (~0.01–0.05s from D_I=4 to D_I=262144). This is cheap and is NOT a solve.
- FGLM variety root-extraction (the real solve cost, small prime pm): full
  solve_s = {0.024, 0.034, 0.356, 20.5}s at D_I = {64, 256, 1024, 4096}.
  Fit over D_I in [1024, 4096]: slope log(20.5/0.356)/log(4) ~ 2.9, i.e.
  FGLM root-extraction scales ~D_I^2.5–3 — STEEPER than the uni eliminant.

Head-to-head, same prime pm at D_I=4096: uni 2.20s vs full GB 20.5s — the
univariate eliminant is ~9x FASTER (and ~3x faster at D_I=1024). The GB/FGLM
path does NOT beat the direct univariate path. This matches the simpler-
argument note: univariate root-finding is the binding attack for sponge CICO,
not Groebner/FGLM.

Field-size off-model factor (BN254 vs KoalaBear, same D_I): uni at D_I=64 is
126x slower on BN254 (0.44s vs 0.0035s); at D_I=1024, 71x slower
(20.7s vs 0.29s). The cost carries a substantial poly(log p) factor on top of
the D_I model — the curve is genuinely OFF a pure-D_I prediction by ~10^2 at
254-bit. Root-finding cost is Otilde(D_I^~2 · poly(log p)) as measured.

## Largest n broken per attack (full root recovery, forward-verified)

- uni, t=2, KoalaBear: n=8 (D_I=2^14, 88s). DNF at n=9 (>480s).
- uni, t=3, KoalaBear: n=5 (D_I=2^12, 2.1s). (n=6 not attempted; budget.)
- uni, t=2, BN254: n=6 (D_I=2^10, 20.7s).
- gb full solve (F4+FGLM root extracted+verified), t=2, small prime pm: n=7
  (D_I=2^12, 20.5s) — slower than uni at the same D_I.
- gb GB+colength only (no root extraction), t=2 KoalaBear: n=10 (D_I=2^18);
  t=3 KoalaBear: n=6 (D_I=2^15) — cheap but NOT a solve.

## Rounds broken vs rounds recommended

Recommended at 128-bit (D_I >= 2^128): t=2 n=65, t=3 n=44, t=4 n=33–34.

Largest practical FULL break (root recovered + verified):
- t=2: n=8, D_I = 2^14.
- t=3: n=5, D_I = 2^12.

The frontier sits ~57 rounds below the t=2 recommendation and ~39 below t=3.
In D_I terms the gap is enormous: 2^14 broken vs 2^128 recommended is a factor
of 2^114 in solution-space size. Even on the most favourable measured cost
(msolve, which stayed sub-second to D_I=2^18 but only computes the GB /
colength over KoalaBear and only root-extracts on a 20-bit prime), nothing
approaches the recommended widths. The eliminant-degree security model
D_I = 2^{t(n-1)} is confirmed exactly (every colength = D_I), and the
practical solve cost grows steeply (~D_I^2 with the naive uni path; field-size
penalty ~10^2 at BN254). No round-reduced shortcut below the D_I barrier was
found.

## Honesty caveats

1. uni solve_s exponent ~2.0 is sage's generic dense root-finder, not the
   Otilde(D_I) optimum; the asymptotic attack would be faster but we measure
   what sage actually runs.
2. MEASUREMENT TRAP (fixed in the engine this session): the gb `solve_s`
   originally timed only the F4 GB step, which is cheap (~0.02s) because the
   iterated system is triangular — but that step does NOT recover a root.
   The dominant cost is the FGLM variety extraction, which the engine now
   folds into solve_s. With that corrected, full GB solve at D_I=4096 is
   20.5s, ~9x SLOWER than the uni eliminant (2.2s same prime). So GB does
   NOT beat the eliminant. gb KoalaBear/BN254 cells still report GB+colength
   only (msolve does not run variety at those prime sizes; BN254 raises
   NotImplementedError on the base field), so those rows are not solves and
   must not be read as attack costs.
3. Fit ranges are stated; no value is extrapolated past the largest measured
   cell. The duplicate gb,2,7,pm row in the CSV is an expected artefact of the
   append-on-completion design (a cell was re-run); both rows agree.
