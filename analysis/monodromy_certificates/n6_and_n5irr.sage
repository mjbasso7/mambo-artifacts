import time, hashlib
p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
F = GF(p); R.<x> = PolynomialRing(F); phi = F(7)
T_START = time.time()
BUDGET = 420  # seconds, hard internal budget

def derive_rc(n, seed=b"Mambo_round_constants"):
    vals = []
    for j in range(2*n):
        h = hashlib.sha256(seed + j.to_bytes(4,"big")).digest()
        v = int.from_bytes(h,"big") % p
        vals.append(v if v != 0 else 1)
    return [(F(vals[i]), F(vals[n+i])) for i in range(n)]

def build_theta(n):
    rc = derive_rc(n); th, ps = x, R(0)
    for r in range(n):
        c, d = rc[r]
        th_new = phi*th + ps^2 + c
        ps = phi*ps + th_new^2 + d
        th = th_new
    return th

def is_decomposable(f):
    D = f.degree(); f = f.monic()
    for s in divisors(D):
        if s == 1 or s == D: continue
        r = D // s
        frev = R(list(reversed(f.list())))
        S.<T> = PowerSeriesRing(F, default_prec=s+1)
        try:
            hrev_ser = S(frev.list()[:s+1]).nth_root(r)
        except (ValueError, ArithmeticError):
            continue
        h = R(list(reversed(hrev_ser.padded_list(s+1))))
        if h.degree() != s: continue
        g, digits = f, []
        while g != 0:
            g, rem = g.quo_rem(h)
            digits.append(rem)
        if all(d.degree() <= 0 for d in digits):
            return True, s
    return False, None

# ---- n=6, D=1024 ----
n = 6; th6 = build_theta(n); D = th6.degree()
dens = sum(1 for c in th6.list() if c != 0) / (D+1)
t0=time.time(); dec, s = is_decomposable(th6); t1=time.time()
print("n=6 D=%d density=%.4f decomposable=%s split=%s (KL test %.1fs)" % (D, float(dens), dec, s, t1-t0))

qs = set(primes(D//2 + 1, D-2))
found_q = None
for tau in range(1, 60):
    if time.time() - T_START > BUDGET*0.55: print("n=6 q-hunt budget out at tau=%d" % tau); break
    f = th6 - F(tau)
    if gcd(f, f.derivative()).degree() != 0:
        print("  tau=%d not squarefree, skip" % tau); continue
    tf0=time.time(); degs = sorted([g.degree() for g,_ in f.factor()]); tf1=time.time()
    hit = sorted(q for q in qs if q in degs)
    r = len(degs); oddperm = (r % 2 == 1)  # D even
    print("  tau=%d pattern=%s (%.1fs) oddperm=%s" % (tau, degs, tf1-tf0, oddperm))
    if hit:
        found_q = (tau, degs, hit[0])
        print("n=6 CERT-Q: tau=%d q=%d pattern=%s" % (tau, hit[0], degs))
        break
if found_q is None: print("n=6: no q-cycle found within budget (record patterns above)")

# ---- n=5 irreducible tau hunt ----
th5 = build_theta(5); D5 = 256
found_irr = None
for tau in range(1, 3000):
    if time.time() - T_START > BUDGET: print("n=5 irr-hunt budget out at tau=%d" % tau); break
    f = th5 - F(tau)
    if not f.is_irreducible(): continue
    found_irr = tau
    print("n=5 CERT-T (irreducible): tau=%d (pattern [256], D-cycle, r=1 odd perm)" % tau)
    break
if found_irr is None: print("n=5: no irreducible tau found in scanned range")
print("total time %.1fs" % (time.time()-T_START))
