# Certificates for Gal(theta_n(x) - tau / F_p(tau)) at production constants, BN254.
# Method: Dedekind specialization tau -> small integers; find squarefree pattern
# containing a prime-length cycle q with D/2 < q <= D-3 (forces primitivity +
# Jordan => >= A_D); transitivity over F_p(tau) is automatic (linear in tau).
# Parity of any certified pattern with odd #factors (D even) => odd perm => = S_D.
import time, hashlib
p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
F = GF(p); R.<x> = PolynomialRing(F)
phi = F(7)

def derive_rc(n, seed=b"Mambo_round_constants"):
    vals = []
    for j in range(2*n):
        h = hashlib.sha256(seed + j.to_bytes(4,"big")).digest()
        v = int.from_bytes(h,"big") % p
        vals.append(v if v != 0 else 1)
    return [(F(vals[i]), F(vals[n+i])) for i in range(n)]

def build_theta(n):
    th, ps = x, R(0)
    for r in range(n):
        c, d = derive_rc(n)[r] if False else None, None
    return None

def build_theta2(n, rc):
    th, ps = x, R(0)
    for r in range(n):
        c, d = rc[r]
        th_new = phi*th + ps^2 + c
        ps = phi*ps + th_new^2 + d
        th = th_new
    return th

for n in [3,4,5]:
    D = 4^(n-1)
    qs = [q for q in primes(D//2 + 1, D-2)]  # primes in (D/2, D-3]
    rc = derive_rc(n)
    th = build_theta2(n, rc)
    assert th.degree() == D
    dens = sum(1 for c in th.list() if c != 0) / (D+1)
    print("== n=%d D=%d density(theta_n)=%.4f  Jordan primes q in (%d,%d]: %s" % (n, D, float(dens), D//2, D-3, qs))
    found_q, found_irr = None, None
    t0 = time.time()
    for tau in range(1, 2000):
        f = th - F(tau)
        if gcd(f, f.derivative()).degree() != 0:
            print("   tau=%d NOT squarefree (skipped)" % tau); continue
        degs = sorted([g.degree() for e in [f.factor()] for g,_ in e])
        sign_odd = (len(degs) % 2 == 1)   # D even: sign = (-1)^r, r=#cycles
        if found_irr is None and degs == [D]:
            found_irr = (tau, degs, sign_odd)
            print("   CERT-T  tau=%d pattern=[%d] (irreducible: D-cycle; r=1 odd perm)" % (tau, D))
        if found_q is None:
            hit = [q for q in qs if q in degs]
            if hit:
                found_q = (tau, degs, hit[0], sign_odd)
                print("   CERT-Q  tau=%d pattern=%s q=%d oddperm=%s" % (tau, degs, hit[0], sign_odd))
        if found_q and (found_irr or n == 5):
            break
    print("   time %.1fs ; scanned tau up to %s" % (time.time()-t0, tau))
