# Window-local membership certificate for the t = 4 staircase LM classification.
#
# Closes the membership half of the LM-classification theorem (Section 5 of
# the 2026-06-10 Hilbert-coefficients note): every non-Boolean leading
# monomial of the t = 4 full-cap CICO ideal -- the 57 mixed monomials, the
# tower w^6 (w = x_{n,3}), and the two anti-diagonal linears x_{n-1,1},
# x_{n-2,2} -- is the leading monomial of an element of the WINDOW SUBIDEAL
#
#     J_n := < round-map generators for rounds n-3 -> n-2 -> n-1 -> n,
#              output pin x_{n,0} - tau >                (13 polynomials)
#
# which involves only the 16 state variables of rounds n-3..n.  All Boolean
# squares are leading monomials of original generators directly, so the whole
# certificate reduces to J_n.  J_n's generators are the SAME polynomials for
# every n >= 4 (window rounds n-3 >= 1 never touch the round-0 input pins),
# up to the values of the round constants and tau.  Since degrevlex restricts
# to degrevlex on any subset of variables with the relative order preserved,
# an element of J_n with leading monomial mu maps, under the round-index
# shift, to an element of J_{n'} with the shifted leading monomial, for every
# n' >= 4 -- PROVIDED the membership does not depend on the constants.
#
# That is what the symbolic mode establishes: adjoin the 12 round constants
# and tau as indeterminates in a LOWER BLOCK of the term order
# (degrevlex(16 state vars) >> degrevlex(13 constants)) and compute the GB of
# the lifted ideal J^sym over GF(p)[y, c, tau].  A GB element g whose leading
# monomial is PURE in the state variables (trivial constant-block part)
# necessarily has a unit leading coefficient in GF(p): any term with the same
# y-part and a nontrivial c-part would beat it in the block order.  Writing
# g = sum q_i f_i over the lifted generators and specializing the constants
# to ANY values (any prime-field elements, any n's round-constant schedule)
# therefore yields an element of the specialized ideal with the SAME leading
# monomial.  No genericity caveat, no denominators (everything stays in the
# polynomial ring).  Pure-y leading monomials of GB(J^sym) covering the
# certificate ==> membership for all constants, hence for all n >= 4.
#
# Modes:
#   sage q4_window_membership.sage numeric  [n] [p] [seed]
#       certificate from the full-ideal GB at this n; window GB with the
#       actual constants of this (n, p, seed); divisibility check.
#   sage q4_window_membership.sage symbolic [n] [p] [seed]
#       certificate from the full-ideal GB at n (numeric, cheap); then the
#       block-order GB of J^sym over GF(p)[y(16), c(12), tau]; coverage check
#       restricted to UNIT-CERTIFIED (pure-y) leading monomials.
#
# Conventions identical to analysis/hilbert_residue_staircase.sage:
# x_{r+1,0} = phi x_{r,0} + x_{r,3}^2 + c_{r,0};
# x_{r+1,i} = phi x_{r,i} + x_{r+1,i-1}^2 + c_{r,i}, i = 1..3;
# x_{0,0} = x_{0,1} = x_{0,2} = 0, x_{n,0} = tau; degrevlex, round-major.

import sys, hashlib, time

args = sys.argv[1:]
mode = args[0] if len(args) > 0 else "numeric"
n = int(args[1]) if len(args) > 1 else 5
p = int(args[2]) if len(args) > 2 else 251
seed = args[3] if len(args) > 3 else "mambo_residue"
WB = int(args[4]) if len(args) > 4 else 4  # map-generator rounds in the window
t = 4
PHI = 7
assert n >= WB, "window rounds n-WB..n-1 must exist"

K = GF(p)

def rc(r, i):
    h = hashlib.sha256(("%s_%d_%d" % (seed, r, i)).encode()).digest()
    return K(int.from_bytes(h, "big") % p)

# ---------------------------------------------------------------- full ideal
names = ["x%d_%d" % (r, i) for r in range(n + 1) for i in range(t)]
P = PolynomialRing(K, names, order="degrevlex")
V = {(r, i): P.gens()[r * t + i] for r in range(n + 1) for i in range(t)}

state = [K(0)] * (t - 1) + [K(1)]
for r in range(n):
    new = [K(0)] * t
    new[0] = PHI * state[0] + state[t - 1] ** 2 + rc(r, 0)
    for i in range(1, t):
        new[i] = PHI * state[i] + new[i - 1] ** 2 + rc(r, i)
    state = new
tau = state[0]

gens = []
for r in range(n):
    gens.append(V[(r + 1, 0)] - PHI * V[(r, 0)] - V[(r, t - 1)] ** 2 - rc(r, 0))
    for i in range(1, t):
        gens.append(V[(r + 1, i)] - PHI * V[(r, i)] - V[(r + 1, i - 1)] ** 2 - rc(r, i))
for i in range(t - 1):
    gens.append(V[(0, i)])
gens.append(V[(n, 0)] - tau)
I = P.ideal(gens)

# Boolean squares are generator LMs directly (valid for every n >= 2):
# gen for x_{r+1,0} has LM x_{r,3}^2; gen for x_{r+1,i} (i>=1) has LM
# x_{r+1,i-1}^2.  Verify, and record which squares are covered.
sq_lms = set()
for g in gens[: t * n]:
    m = g.lm()
    e = m.exponents()[0]
    supp = [j for j in range(len(e)) if e[j] > 0]
    assert len(supp) == 1 and e[supp[0]] == 2, "round-map generator LM not a square: %s" % g
    sq_lms.add(P.gens()[supp[0]])
expected_sq = set(P.gens()) - {V[(0, i)] for i in range(t - 1)} - {V[(n, t - 1)]}
assert sq_lms == expected_sq, "square coverage mismatch"
print("[squares] every Boolean variable's square is an original generator's LM "
      "(all vars except the %d input pins and w): OK, %d squares" % (t - 1, len(sq_lms)))

# ----------------------------------------------- certificate from full GB
t0 = time.time()
G = I.groebner_basis()
print("[full GB] t=%d n=%d p=%d seed=%s: %.1fs, |G| = %d" % (t, n, p, seed, time.time() - t0, len(G)))

lin_lms, nonbool = [], []
for g in G:
    m = g.lm()
    e = m.exponents()[0]
    supp = [j for j in range(len(e)) if e[j] > 0]
    if len(supp) == 1 and e[supp[0]] == 1:
        lin_lms.append(m)
    elif len(supp) == 1 and e[supp[0]] == 2:
        pass  # Boolean square
    else:
        nonbool.append((m, g))

w = V[(n, t - 1)]
expect_lin = {V[(0, 0)], V[(0, 1)], V[(0, 2)], V[(n, 0)], V[(n - 1, 1)], V[(n - 2, 2)]}
assert set(P(m) for m in lin_lms) == expect_lin, "linear LM set unexpected: %s" % lin_lms
print("[linears] 3 input pins + anti-diagonal {x_{n,0}, x_{n-1,1}, x_{n-2,2}}: OK")
print("[mixed] %d non-Boolean LMs (expect 58 = 57 mixed + w^6)" % len(nonbool))

# LM window = rounds n-3..n; check every non-Boolean LM is supported there
lm_win = set(V[(r, i)] for r in range(n - 3, n + 1) for i in range(t))
for m, g in nonbool:
    assert set(m.variables()) <= lm_win, "LM outside round n-3..n window: %s" % m
print("[LM window] all non-Boolean LMs supported on rounds %d..%d: OK" % (n - 3, n))

# generator window = rounds n-WB..n (variables), maps n-WB -> ... -> n + pin
win_set = set(V[(r, i)] for r in range(n - WB, n + 1) for i in range(t))

# Are the REDUCED GB elements themselves window-supported (tails included)?
full_local = all(set(g.variables()) <= win_set for m, g in nonbool)
print("[locality] all %d reduced GB elements (LM + tail) supported on "
      "rounds %d..%d: %s" % (len(nonbool), n - WB, n, full_local))

# ------------------------------------------------------- window subideal J_n
# numeric J in the big ring (degrevlex restricts; GB of J equals its GB in
# the subring on the window variables)
Jgens = []
for r in range(n - WB, n):
    Jgens.append(V[(r + 1, 0)] - PHI * V[(r, 0)] - V[(r, t - 1)] ** 2 - rc(r, 0))
    for i in range(1, t):
        Jgens.append(V[(r + 1, i)] - PHI * V[(r, i)] - V[(r + 1, i - 1)] ** 2 - rc(r, i))
Jgens.append(V[(n, 0)] - tau)
J = P.ideal(Jgens)

targets = [m for m, g in nonbool] + [P(V[(n - 1, 1)]), P(V[(n - 2, 2)])]

if mode == "numeric":
    t0 = time.time()
    GJ = J.groebner_basis()
    print("[window GB numeric] %.1fs, |GJ| = %d" % (time.time() - t0, len(GJ)))
    for g in GJ:
        assert set(g.variables()) <= win_set
    jlms = [g.lm() for g in GJ]
    misses = []
    for mu in targets:
        if not any(P.monomial_divides(nu, mu) for nu in jlms):
            misses.append(mu)
    print("[membership numeric] %d/%d certificate LMs (57 mixed + w^6 + 2 linears) "
          "are multiples of LM(GB(J_n)): %s"
          % (len(targets) - len(misses), len(targets),
             "ALL COVERED" if not misses else "MISSING %s" % misses))
    # strongest numeric statement: the actual reduced-GB elements lie in J_n
    inJ = all(g.reduce(GJ) == 0 for m, g in nonbool)
    print("[membership numeric] all %d non-Boolean reduced-GB elements of the FULL "
          "ideal reduce to 0 modulo GB(J_n): %s" % (len(nonbool), inJ))
    sys.exit(0)

# ------------------------------------------------- symbolic-constants window
# ring GF(p)[y_{0..WB,0..3} | c_{0..WB-1,0..3}, tau], block order
# dp(4*(WB+1)) >> dp(4*WB + 1); y_{j,i} stands for x_{n-WB+j,i}
assert mode == "symbolic"
ny = t * (WB + 1)
nc = t * WB + 1
ynames = ["y%d_%d" % (j, i) for j in range(WB + 1) for i in range(t)]
cnames = ["c%d_%d" % (j, i) for j in range(WB) for i in range(t)] + ["tu"]
T = TermOrder("degrevlex", ny) + TermOrder("degrevlex", nc)
S = PolynomialRing(K, ynames + cnames, order=T)
Y = {(j, i): S.gens()[j * t + i] for j in range(WB + 1) for i in range(t)}
C = {(j, i): S.gens()[ny + j * t + i] for j in range(WB) for i in range(t)}
TU = S.gens()[ny + t * WB]

Jsym = []
for j in range(WB):
    Jsym.append(Y[(j + 1, 0)] - PHI * Y[(j, 0)] - Y[(j, t - 1)] ** 2 - C[(j, 0)])
    for i in range(1, t):
        Jsym.append(Y[(j + 1, i)] - PHI * Y[(j, i)] - Y[(j + 1, i - 1)] ** 2 - C[(j, i)])
Jsym.append(Y[(WB, 0)] - TU)

t0 = time.time()
GS = S.ideal(Jsym).groebner_basis()
print("[window GB symbolic] GF(%d)[y(%d) | c(%d)], block degrevlex: "
      "%.1fs, |GS| = %d" % (p, ny, nc, time.time() - t0, len(GS)))

# unit-certified leading monomials: block-LM has trivial c-part, hence the
# coefficient of the y-part is a nonzero CONSTANT and survives every
# specialization of (c, tau).
unit_lms, nonunit = [], []
for g in GS:
    e = g.lm().exponents()[0]
    if any(e[j] > 0 for j in range(ny, ny + nc)):
        nonunit.append(g.lm())
    else:
        unit_lms.append(g.lm())
print("[symbolic] %d unit-certified (pure-y) LMs, %d GB elements with "
      "constant-block content in their LM" % (len(unit_lms), len(nonunit)))

# map certificate targets x_{r,i} -> y_{r-(n-WB),i} and check coverage
def to_window(m):
    e = m.exponents()[0]
    out = S(1)
    for j in range(len(e)):
        if e[j]:
            r, i = divmod(j, t)
            assert n - WB <= r <= n
            out *= Y[(r - (n - WB), i)] ** e[j]
    return out

misses = []
for mu in targets:
    muw = to_window(mu)
    if not any(S.monomial_divides(nu, muw) for nu in unit_lms):
        misses.append((mu, muw))
print("[membership symbolic] %d/%d certificate LMs are multiples of "
      "unit-certified LMs of GB(J^sym): %s"
      % (len(targets) - len(misses), len(targets),
       "ALL COVERED -- membership holds for ALL round constants and tau, "
       "hence for all n >= 4 by the round-index shift"
       if not misses else "MISSING %s" % misses))
if misses:
    print("  (non-unit LMs that might cover generically: %s)" % nonunit)
