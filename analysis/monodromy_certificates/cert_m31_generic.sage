# Generic-constants formulation over M31 (n=3 methodology extended):
# random specializations of (c,d,tau); record exact tuples certifying
# Gal(f_n / F_p(c_0..c_{n-1}, d_0..d_{n-1}, tau)) >= A_D via Dedekind+Jordan.
import time
p = 2147483647
F = GF(p); R.<x> = PolynomialRing(F); phi = F(7)

def build_f(n, cs, ds, tau):
    th, ps = x, R(0)
    for r in range(n):
        th_new = phi*th + ps^2 + cs[r]
        ps = phi*ps + th_new^2 + ds[r]
        th = th_new
    return th - tau

set_random_seed(20260610)
for n in [4,5]:
    D = 4^(n-1)
    qs = set(primes(D//2 + 1, D-2))
    found_irr, found_q = None, None
    t0=time.time(); trials = 0
    while (found_irr is None or found_q is None) and trials < 5000:
        trials += 1
        cs = [F.random_element() for _ in range(n)]
        ds = [F.random_element() for _ in range(n)]
        tau = F.random_element()
        f = build_f(n, cs, ds, tau)
        if gcd(f, f.derivative()).degree() != 0: continue
        degs = sorted([g.degree() for g,_ in f.factor()])
        if found_irr is None and degs == [D]:
            found_irr = (cs, ds, tau, degs)
            print("n=%d CERT-T (irreducible): cs=%s ds=%s tau=%s" % (n, [int(c) for c in cs], [int(d) for d in ds], int(tau)))
        if found_q is None:
            hit = sorted(q for q in qs if q in degs)
            if hit:
                found_q = (cs, ds, tau, degs, hit[0])
                print("n=%d CERT-Q: q=%d pattern=%s cs=%s ds=%s tau=%s" % (n, hit[0], degs, [int(c) for c in cs], [int(d) for d in ds], int(tau)))
    print("n=%d done: trials=%d time=%.1fs" % (n, trials, time.time()-t0))
