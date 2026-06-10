# Round-reduced practical-attack engine for Mambo sponge-convention CICO.
#
# Two attacks on the sponge CICO instance (rate r=1, capacity c=t-1):
# capacity cells x_2(0)=...=x_t(0)=0 at input, rate cell x_1(n)=tau at output;
# unknown is the input rate cell x_1(0).
#
#   (1) attack=uni : build the dense univariate eliminant f_n(x_1(0)) by
#       iterated composition, then F_p-root-find (sage .roots()).
#   (2) attack=gb  : the multivariate iterated system an attacker who ignores
#       the univariate structure would use (one quadratic per state component
#       per round, all intermediate values as variables), solved with msolve
#       (F4 + FGLM) via sage's variety(algorithm='msolve').
#
# Round map (paper eq:theta/eq:psi and sec:inst:wider), phi=7:
#   x_1' = phi*x_1 + x_t^2          + c_{r,1}
#   x_i' = phi*x_i + (x_{i-1}')^2   + c_{r,i}   for i=2..t
# Eliminant degree D_I = 2^{t(n-1)}.
#
# Usage:  sage round_reduced_attacks.sage <uni|gb> <t> <n> <kb|bn254|pm> [seed]
#
# CRASH-SAFE RESULT PERSISTENCE: every completed cell appends ONE line to
#   round_reduced_results.csv (next to this script)
# in append mode, flushed + fsync'd, with columns:
#   attack,t,n,field,D_I,build_s,solve_s,total_s,peak_mem_mb,outcome
# The line is written the moment the cell finishes (and also echoed to stdout).
# Cells killed by an external timeout never reach record(); the driver is
# responsible for appending a DNF line for those.

import sys, time, os, resource

attack = sys.argv[1]
t      = int(sys.argv[2])
n      = int(sys.argv[3])
fld    = sys.argv[4]
seed   = int(sys.argv[5]) if len(sys.argv) > 5 else 20260610

if fld == 'kb':
    p = 2130706433                                   # KoalaBear, 2^31-2^24+1
elif fld == 'bn254':
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
elif fld == 'pm':
    p = 1048573   # ~20-bit prime (paper's verification field); msolve variety ok
else:
    raise ValueError("field must be kb, pm or bn254")

F   = GF(p)
phi = F(7)
set_random_seed(seed)

D_I = 2**(t*(n-1))

# ---- crash-safe CSV recorder ------------------------------------------------
import os as _os
CSV    = _os.path.join(_os.path.dirname(_os.path.abspath(__file__)) if '__file__' in globals() else '.', 'round_reduced_results.csv')
HEADER = 'attack,t,n,field,D_I,build_s,solve_s,total_s,peak_mem_mb,outcome'

def peak_mem_mb():
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # darwin reports bytes; linux reports kilobytes
    return rss / 1048576.0 if sys.platform == 'darwin' else rss / 1024.0

def record(build_s, solve_s, outcome):
    total = build_s + solve_s
    line = "%s,%d,%d,%s,%d,%.4f,%.4f,%.4f,%.1f,%s" % (
        attack, t, n, fld, D_I, build_s, solve_s, total, peak_mem_mb(), outcome)
    new = not os.path.exists(CSV)
    with open(CSV, 'a') as fh:
        if new:
            fh.write(HEADER + "\n")
        fh.write(line + "\n")
        fh.flush()
        os.fsync(fh.fileno())
    print(line)

# per-round constant vectors c[r][i], i=0..t-1  (i index 0 == component 1)
C = [[F.random_element() for _ in range(t)] for _ in range(n)]

def round_step(state, r):
    # state: list of t field/poly elements (component 1..t)
    new = [None]*t
    new[0] = phi*state[0] + state[t-1]**2 + C[r][0]
    for i in range(1, t):
        new[i] = phi*state[i] + new[i-1]**2 + C[r][i]
    return new

def forward_x1n(x1_0):
    # numeric forward evaluation; capacity zeros at input; returns x_1(n)
    state = [x1_0] + [F(0)]*(t-1)
    for r in range(n):
        state = round_step(state, r)
    return state[0]

# pick a real secret input so a root is guaranteed to exist and be verifiable
secret = F.random_element()
tau = forward_x1n(secret)

def verify(x0):
    return forward_x1n(F(x0)) == tau

if attack == 'uni':
    R = PolynomialRing(F, 'x'); x = R.gen()
    t0 = time.time()
    state = [x] + [R(0)]*(t-1)
    for r in range(n):
        state = round_step(state, r)
    f = state[0] - tau
    build_s = time.time() - t0
    deg = f.degree()
    t1 = time.time()
    rts = f.roots()                                  # list of (root, mult)
    solve_s = time.time() - t1
    sols = [rr for rr, _ in rts]
    ok = any(verify(rr) for rr in sols)
    outcome = ("verified" if ok else "NOVERIFY") + ("" if deg == D_I else "/deg!=D_I")
    record(build_s, solve_s, outcome)

elif attack == 'gb':
    # variables: x0 (= x_1(0)); X[i,r] for r=1..n-1, i=0..t-1 (component i+1).
    # final round contributes only the x_1(n)=tau equation.
    names = ['x0']
    idx = {}
    for r in range(1, n):
        for i in range(t):
            idx[(i, r)] = len(names)
            names.append('y_%d_%d' % (i, r))
    Rg = PolynomialRing(F, names, order='degrevlex')
    g = Rg.gens()
    x0 = g[0]
    def var(i, r):
        if r == 0:
            return x0 if i == 0 else Rg(0)
        return g[idx[(i, r)]]
    eqs = []
    t0 = time.time()
    for r in range(1, n):
        # component-1 update uses x_t of previous round
        e0 = var(0, r) - (phi*var(0, r-1) + var(t-1, r-1)**2 + C[r-1][0])
        eqs.append(e0)
        for i in range(1, t):
            ei = var(i, r) - (phi*var(i, r-1) + var(i-1, r)**2 + C[r-1][i])
            eqs.append(ei)
    # final round r=n: x_1(n) = phi*x_1(n-1) + x_t(n-1)^2 + c == tau
    eqs.append(phi*var(0, n-1) + var(t-1, n-1)**2 + C[n-1][0] - tau)
    I = Rg.ideal(eqs)
    build_s = time.time() - t0
    # Primary cost: the F4 Groebner basis (msolve). This msolve build rejects
    # the full variety/parametrization step for >~31-bit primes, so over
    # KoalaBear we time the GB and read the quotient colength; over a smaller
    # prime we additionally run the variety and forward-verify a recovered root.
    t1 = time.time()
    try:
        G = I.groebner_basis(algorithm='msolve')
        gb_s = time.time() - t1
    except Exception as e:
        gb_s = time.time() - t1
        record(build_s, gb_s, "ERR:" + repr(e)[:40].replace(',', ';'))
        sys.exit(0)
    # quotient colength (number of solutions counted with multiplicity)
    try:
        col = I.vector_space_dimension()
    except Exception:
        col = -1
    outcome = "dim=%d%s" % (col, "(=D_I)" if col == D_I else "(!=D_I)")
    # full solve + verification only attempted on a small prime (variety ok).
    # IMPORTANT: the variety / FGLM root-extraction is the DOMINANT cost of the
    # GB attack and MUST be folded into solve_s, else solve_s reports only the
    # (cheap, triangular) F4 step and understates the attack by 100-1000x.
    solve_s = gb_s
    if p < 2**28:
        try:
            tv = time.time()
            V = I.variety(algorithm='msolve', proof=False)
            solve_s = gb_s + (time.time() - tv)
            sols = [sol[x0] for sol in V]
            vok = any(verify(s) for s in sols)
            outcome += "/verified" if vok else "/NOVERIFY"
        except Exception:
            outcome += "/novariety"
    record(build_s, solve_s, outcome)
else:
    raise ValueError("attack must be uni or gb")
