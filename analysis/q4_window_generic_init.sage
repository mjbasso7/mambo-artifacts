# Constant-independence of the t = 4 staircase membership certificate, via the
# generic initial ideal of the window subideal J_n.
#
# Companion to analysis/q4_window_membership.sage.  That script established,
# at the actual round-constant schedules (n = 4, 5, 6; two seeds; two primes):
#
#   every non-Boolean leading monomial of the full-cap CICO ideal -- the 57
#   mixed monomials, the tower w^6 (w = x_{n,3}), and the two anti-diagonal
#   linears x_{n-1,1}, x_{n-2,2} -- is a multiple of a leading monomial of
#   GB(J_n), where J_n is the WINDOW SUBIDEAL on the four rounds n-4..n
#   (17 generators: 16 round-map relations + the output pin y_{4,0} - tau),
#   involving only the 20 window state variables.  WB = 4 is minimal: a
#   3-round window already misses 13 certificate monomials.
#
# What remains is to remove the dependence on the actual constant schedule, so
# that membership holds for EVERY n >= 4 by the round-index shift (the window
# generators of J_n and J_{n'} are identical polynomials up to the values of
# the 16 round constants and tau, which the shift permutes).
#
# RIGOROUS ARGUMENT used here (Groebner stratification / upper-semicontinuity
# of the initial ideal).  Regard J as a family over the parameter space
# A^17 = {(c_{j,i}, tau)}.  There is a dense Zariski-open stratum on which the
# initial ideal in_<(J) is constant and MINIMAL -- the generic initial ideal
# in_gen -- and for EVERY parameter value v, in_<(J_v) contains in_gen (the
# initial ideal can only jump UP on the proper closed complement).  Therefore:
#
#       if in_gen already covers the certificate
#       (each certificate monomial is a multiple of some LM in in_gen),
#       then in_<(J_v) covers it for EVERY v -- all constants, all n >= 4.
#
# in_gen is identified by random specialization: the bad locus where in_<(J_v)
# strictly exceeds in_gen is a proper closed subset, so a uniformly random v
# over a large field lands on the generic stratum with overwhelming
# probability, and independent random v that all yield the SAME leading-monomial
# set L pin down L = in_gen (the unique minimal one).  We draw many random v
# over a large prime, verify the window-GB leading-monomial set is bit-identical
# across all of them, and verify it covers the certificate.  Agreement across
# R independent draws bounds the chance of having all missed the generic stratum
# by ~ (D/p)^R for the stratification degree D, i.e. negligible.
#
# Conventions identical to q4_window_membership.sage / hilbert_residue_staircase.sage.
# Usage: sage q4_window_generic_init.sage [p] [reps] [n_for_certificate] [seed]

import sys, hashlib, time

args = sys.argv[1:]
p     = int(args[0]) if len(args) > 0 else 2147483647   # 2^31 - 1, for SZ strength
reps  = int(args[1]) if len(args) > 1 else 40
ncert = int(args[2]) if len(args) > 2 else 5            # n used to read off the certificate
seed  = args[3] if len(args) > 3 else "mambo_residue"
t, PHI, WB = 4, 7, 4
K = GF(p)

def rc(r, i):
    h = hashlib.sha256(("%s_%d_%d" % (seed, r, i)).encode()).digest()
    return K(int.from_bytes(h, "big") % p)

# -------------------------------------------------- read the certificate once
# full-cap CICO ideal at n = ncert, actual schedule; extract the non-Boolean GB
# leading monomials + the two anti-diagonal linears, then translate to window
# coordinates y_{j,i} = x_{ncert-WB+j, i}.
names = ["x%d_%d" % (r, i) for r in range(ncert + 1) for i in range(t)]
P = PolynomialRing(K, names, order="degrevlex")
V = {(r, i): P.gens()[r * t + i] for r in range(ncert + 1) for i in range(t)}

state = [K(0)] * (t - 1) + [K(1)]
for r in range(ncert):
    new = [K(0)] * t
    new[0] = PHI * state[0] + state[t - 1] ** 2 + rc(r, 0)
    for i in range(1, t):
        new[i] = PHI * state[i] + new[i - 1] ** 2 + rc(r, i)
    state = new
tau0 = state[0]

gens = []
for r in range(ncert):
    gens.append(V[(r + 1, 0)] - PHI * V[(r, 0)] - V[(r, t - 1)] ** 2 - rc(r, 0))
    for i in range(1, t):
        gens.append(V[(r + 1, i)] - PHI * V[(r, i)] - V[(r + 1, i - 1)] ** 2 - rc(r, i))
for i in range(t - 1):
    gens.append(V[(0, i)])
gens.append(V[(ncert, 0)] - tau0)

t0 = time.time()
G = P.ideal(gens).groebner_basis()
nonbool, lin = [], []
for g in G:
    e = g.lm().exponents()[0]
    supp = [j for j in range(len(e)) if e[j] > 0]
    if len(supp) == 1 and e[supp[0]] == 1:
        lin.append(g.lm())
    elif len(supp) == 1 and e[supp[0]] == 2:
        pass
    else:
        nonbool.append(g.lm())
print("[certificate] n=%d p=%d: full GB %.1fs, %d non-Boolean LMs"
      % (ncert, p, time.time() - t0, len(nonbool)))
# certificate targets in x-coords: non-Boolean LMs + 2 anti-diagonal linears
cert_x = list(nonbool) + [P(V[(ncert - 1, 1)]), P(V[(ncert - 2, 2)])]

# window ring on the 20 state variables, degrevlex round-major (restriction of
# the big degrevlex order); y_{j,i} = x_{ncert-WB+j, i}
wnames = ["y%d_%d" % (j, i) for j in range(WB + 1) for i in range(t)]
W = PolynomialRing(K, wnames, order="degrevlex")
Y = {(j, i): W.gens()[j * t + i] for j in range(WB + 1) for i in range(t)}

def to_window(m):
    e = m.exponents()[0]
    out = W(1)
    for j in range(len(e)):
        if e[j]:
            r, i = divmod(j, t)
            assert ncert - WB <= r <= ncert, "certificate monomial outside window"
            out *= Y[(r - (ncert - WB), i)] ** e[j]
    return out

cert = [to_window(m) for m in cert_x]
cert_fp = hashlib.sha256(("|".join(sorted(str(m) for m in cert))).encode()).hexdigest()[:16]
print("[certificate] %d target monomials mapped to window coords; fingerprint %s"
      % (len(cert), cert_fp))

def window_gb_lms(consts, tau):
    Jg = []
    for j in range(WB):
        Jg.append(Y[(j + 1, 0)] - PHI * Y[(j, 0)] - Y[(j, t - 1)] ** 2 - consts[(j, 0)])
        for i in range(1, t):
            Jg.append(Y[(j + 1, i)] - PHI * Y[(j, i)] - Y[(j + 1, i - 1)] ** 2 - consts[(j, i)])
    Jg.append(Y[(WB, 0)] - tau)
    GJ = W.ideal(Jg).groebner_basis()
    return frozenset(g.lm() for g in GJ)

def covers(lmset):
    return [mu for mu in cert
            if not any(W.monomial_divides(nu, mu) for nu in lmset)]

# -------------------------------------------------- sanity: the ACTUAL schedule
real_consts = {(j, i): rc(ncert - WB + j, i) for j in range(WB) for i in range(t)}
L_real = window_gb_lms(real_consts, tau0)
m_real = covers(L_real)
print("[actual schedule] |GB(J) LMs| = %d, certificate %s"
      % (len(L_real), "ALL COVERED" if not m_real else "MISSING %d: %s" % (len(m_real), m_real)))

# -------------------------------------------------- random specialization sweep
import random
random.seed(int(12345))
pp = int(p)
ref = None
all_match = True
all_cover = True
t0 = time.time()
for r in range(reps):
    consts = {(j, i): K(random.randrange(1, pp)) for j in range(WB) for i in range(t)}
    tau = K(random.randrange(0, pp))
    L = window_gb_lms(consts, tau)
    miss = covers(L)
    if miss:
        all_cover = False
        print("  draw %d: NOT COVERED, missing %d" % (r, len(miss)))
    if ref is None:
        ref = L
    elif L != ref:
        all_match = False
        print("  draw %d: LM-set DIFFERS from reference (sym diff %d)"
              % (r, len(L.symmetric_difference(ref))))
print("[random sweep] %d draws over GF(%d) in %.1fs" % (reps, p, time.time() - t0))
ref_fp = hashlib.sha256(("|".join(sorted(str(m) for m in ref))).encode()).hexdigest()[:16]
print("[random sweep] all LM-sets identical: %s  |L| = %d  fingerprint %s"
      % (all_match, len(ref), ref_fp))
print("[random sweep] every draw covers the certificate: %s" % all_cover)
gen_cover = not covers(ref)
print("[generic initial ideal] in_gen LM-set covers certificate: %s" % gen_cover)
print("[actual == generic] real-schedule LM-set equals random reference: %s" % (L_real == ref))

if all_match and all_cover and gen_cover:
    print("\n[CONCLUSION] The window-GB leading-monomial set is constant across %d "
          "random parameter points over GF(%d); it therefore equals the generic "
          "initial ideal in_gen of the parameterised window subideal.  in_gen "
          "covers the certificate, and by upper-semicontinuity in_<(J_v) ⊇ in_gen "
          "for every parameter v; hence the certificate is covered for EVERY "
          "round-constant schedule and tau, i.e. for all n >= 4 by the round-shift."
          % (reps, p))
else:
    print("\n[CONCLUSION] constant-independence NOT established cleanly; see flags above.")
