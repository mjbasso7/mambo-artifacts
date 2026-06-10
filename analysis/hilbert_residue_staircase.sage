# Staircase classification of the wider-t CICO Groebner basis and
# combinatorial reconstruction of the Hilbert numerator residue.
#
# System (the d_reg convention that reproduces the paper formulas
# 2n / 3n-1 / 4n-3 at t = 2, 3, 4):
#   variables x_{r,i}, r = 0..n, i = 0..t-1, degrevlex, round-major order;
#   round map (coupled-sequential chain, matches mambo_hilbert_t32.py and
#   the production t = 4 round function):
#     x_{r+1,0} = phi*x_{r,0} + x_{r,t-1}^2 + c_{r,0}
#     x_{r+1,i} = phi*x_{r,i} + x_{r+1,i-1}^2 + c_{r,i}     (i = 1..t-1)
#   boundary (full-cap CICO, 0-dimensional):
#     x_{0,i} = 0 for i = 0..t-2,  x_{n,0} = tau  (tau consistent by
#     forward simulation so the variety is nonempty).
#
# Pipeline:
#   1. degrevlex GB; classify leading monomials as
#        LIN     (single variable, degree 1  -> eliminated variable)
#        BOOL    (v^2 for a single variable  -> Boolean variable)
#        NONBOOL (everything else)
#   2. verify the single-distinguished-variable claim: every NONBOOL LM is
#      w^a * m with w = x_{n,t-1} and m squarefree in the Boolean variables
#   3. reconstruct the Hilbert numerator combinatorially from the LM data
#      alone, by levels of the w-exponent with inclusion-exclusion over the
#      Boolean blocking sets, and compare with the directly computed
#      numerator; extract the (1+z)^k cofactor and the residue.
#
# Usage: sage hilbert_residue_staircase.sage t n [p] [seed]

import sys, hashlib
from itertools import combinations

args = sys.argv[1:]
t = int(args[0]) if len(args) > 0 else 4
n = int(args[1]) if len(args) > 1 else 3
p = int(args[2]) if len(args) > 2 else 251
seed = args[3] if len(args) > 3 else "mambo_residue"
PHI = 7

K = GF(p)
names = ["x%d_%d" % (r, i) for r in range(n + 1) for i in range(t)]
P = PolynomialRing(K, names, order="degrevlex")
V = {(r, i): P.gens()[r * t + i] for r in range(n + 1) for i in range(t)}

def rc(r, i):
    h = hashlib.sha256(("%s_%d_%d" % (seed, r, i)).encode()).digest()
    return K(int.from_bytes(h, "big") % p)

# consistent tau by forward simulation from x_{0,t-1} = 1, capacity 0
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
import time, os, subprocess
t0 = time.time()
if os.environ.get("USE_MSOLVE"):
    # msolve backend: only the leading monomials are needed downstream
    msf = "/tmp/stair_t%d_n%d.ms" % (t, n)
    with open(msf, "w") as f:
        f.write(",".join(names) + "\n%d\n" % p)
        f.write(",\n".join(str(g).replace(" ", "") for g in gens) + "\n")
    outf = msf + ".gb"
    if not (os.environ.get("REUSE_GB") and os.path.exists(outf)):
        subprocess.run(["msolve", "-g", "2", "-f", msf, "-o", outf], check=True)
    # output: one polynomial per line (terminated by ','), leading term first,
    # terms joined by '+', coefficients reduced mod p (so no '-' inside terms)
    LMs = []
    with open(outf) as f:
        for line in f:
            line = line.strip()
            if not line or line[0] in "#[]":
                line = line.lstrip("[")
                if not line or line[0] == "#" or not line[0].isdigit():
                    continue
            lt = line.split("+", 1)[0].rstrip(",]").strip()
            if "*" in lt:
                lt = lt.split("*", 1)[1] if lt.split("*", 1)[0].isdigit() else lt
            elif lt.isdigit():
                continue  # constant poly (inconsistent ideal); shouldn't happen
            LMs.append(P(lt).lm())
    print("msolve GB done in %.1fs, |G| = %d" % (time.time() - t0, len(LMs)))
else:
    G = I.groebner_basis()
    print("GB done in %.1fs, |G| = %d" % (time.time() - t0, len(G)))
    LMs = [g.lm() for g in G]

lin_vars, bool_vars, nonbool_lms = [], [], []
for m in LMs:
    e = m.exponents()[0]
    supp = [j for j in range(len(e)) if e[j] > 0]
    if len(supp) == 1 and e[supp[0]] == 1:
        lin_vars.append(P.gens()[supp[0]])
    elif len(supp) == 1 and e[supp[0]] == 2:
        bool_vars.append(P.gens()[supp[0]])
    else:
        nonbool_lms.append(m)

all_vars = list(P.gens())
free_vars = [v for v in all_vars if v not in lin_vars]
w = V[(n, t - 1)]  # distinguished variable candidate
B = [v for v in free_vars if v in bool_vars]
other_free = [v for v in free_vars if v not in bool_vars]

print("t=%d n=%d p=%d  vars=%d" % (t, n, p, len(all_vars)))
print("eliminated (linear LM): %d  %s" % (len(lin_vars), sorted(map(str, lin_vars))))
print("Boolean (v^2 LM): %d" % len(bool_vars))
print("free non-Boolean vars: %s" % sorted(map(str, other_free)))
print("non-Boolean LMs: %d" % len(nonbool_lms))
for m in sorted(nonbool_lms):
    print("   deg %d : %s" % (m.degree(), m))

# --- check single-distinguished-variable form: every nonbool LM = w^a * squarefree(B)
widx = all_vars.index(w)
ok_form = True
levels = {}  # a -> list of frozenset of Boolean-var indices (blocking sets)
pure_power = None
for m in nonbool_lms:
    e = m.exponents()[0]
    a = e[widx]
    rest = [(j, e[j]) for j in range(len(e)) if e[j] > 0 and j != widx]
    if any(ex > 1 for j, ex in rest):
        ok_form = False
        print("   !! non-squarefree Boolean part: %s" % m)
    if any(all_vars[j] not in B for j, ex in rest):
        ok_form = False
        print("   !! support outside Boolean set: %s" % m)
    if not rest:
        pure_power = a
    levels.setdefault(a, []).append(frozenset(j for j, ex in rest))
print("single-distinguished-variable form (w = %s): %s" % (w, ok_form))
if pure_power is not None:
    print("pure power: w^%d" % pure_power)

if os.environ.get("BLOCKS_ONLY"):
    # print the per-level minimal blocking sets only (cheap shift-stability check)
    for a in sorted(levels):
        blocks = []
        for ap in levels:
            if ap <= a:
                blocks += [s for s in levels[ap] if s]
        blocks = [s for s in blocks if not any(s2 < s for s2 in blocks)]
        blocks = list(set(blocks))
        print("  level a=%d: %d minimal blocks %s" % (a, len(blocks),
              sorted([tuple(sorted(str(all_vars[j]) for j in s)) for s in blocks])))
    sys.exit(0)

# --- direct Hilbert numerator from standard monomials (0-dim: numerator = h-vector)
# count standard monomials of the LM ideal degree by degree (Macaulay: same as R/I)
t0 = time.time()
std_mons = P.ideal(LMs).normal_basis()
print("normal_basis: %d monomials (%.1fs)" % (len(std_mons), time.time() - t0))
maxdeg = max(m.degree() for m in std_mons)
hv = [0] * (maxdeg + 1)
for m in std_mons:
    hv[m.degree()] += 1
print("h-vector (direct): %s   colength=%d  d_reg=%d" % (hv, sum(hv), maxdeg + 1))

Rz.<z> = PolynomialRing(QQ)
H = Rz(hv)
# extract (1+z)^k cofactor
k = 0
Q = H
while Q % (1 + z) == 0:
    Q = Q // (1 + z)
    k += 1
print("H = (1+z)^%d * residue,  residue = %s" % (k, Q.list()))

# --- combinatorial reconstruction from LM data alone -------------------------
# standard monomials = { w^a * sigma : sigma squarefree in B, 0 <= a,
#                        no nonbool LM w^{a'} * m  with a' <= a and supp(m) <= sigma,
#                        a < pure_power }
# (other_free should be exactly [w]; if not, reconstruction below is invalid)
if ok_form and other_free == [w]:
    Amax = (pure_power - 1) if pure_power is not None else max(levels)
    nB = len(B)
    recon = Rz(0)
    print("\nlevel-by-level reconstruction (|B| = %d):" % nB)
    for a in range(Amax + 1):
        # blocking sets active at level a: minimal sets among union of levels a' <= a
        blocks = []
        for ap in levels:
            if ap <= a:
                blocks += [s for s in levels[ap] if s]
        # minimalize
        blocks = [s for s in blocks if not any(s2 < s for s2 in blocks)]
        blocks = list(set(blocks))
        # H_a(z) = h-vector of K[B]/(squares + blocks); equals the
        # inclusion-exclusion sum_{S subset blocks} (-1)^|S| z^{|union S|} (1+z)^{nB-|union S|}
        # but computed via the (free, monomial) normal basis instead.
        PB = PolynomialRing(K, [str(v) for v in B], order="degrevlex")
        gB = list(PB.gens())
        mon_gens = [g ** 2 for g in gB]
        for s in blocks:
            mon_gens.append(prod(PB(str(all_vars[j])) for j in s))
        nb = PB.ideal(mon_gens).normal_basis()
        Ha = Rz(0)
        for m in nb:
            Ha += z ** m.degree()
        # factor Ha
        Qa = Ha; ka = 0
        while Qa != 0 and Qa % (1 + z) == 0:
            Qa = Qa // (1 + z); ka += 1
        print("  level a=%d: %d minimal blocks %s" % (a, len(blocks),
              sorted([tuple(sorted(str(all_vars[j]) for j in s)) for s in blocks])))
        print("            H_a = (1+z)^%d * %s" % (ka, Qa.list()))
        # union-lattice invariant: psi_a(u) with H_a(z) = (1+z)^nB psi_a(z/(1+z)),
        # i.e. psi_a(u) = (1-u)^nB H_a(u/(1-u)).  This is the inclusion-exclusion
        # polynomial sum_S (-1)^|S| u^|union S| and the candidate n-stable object.
        Ru.<u> = PolynomialRing(QQ)
        Fu = FractionField(Ru)
        psi = Fu(1 - u) ** nB * Ha(Fu(u) / Fu(1 - u))
        psi = Ru(psi)
        print("            psi_a(u) = %s" % psi.list())
        recon += z ** a * Ha
    match = (recon == H)
    print("\nreconstructed numerator == direct h-vector: %s" % match)
    if not match:
        print("  recon = %s" % recon.list())
else:
    print("reconstruction skipped (form violated or extra non-Boolean vars)")
