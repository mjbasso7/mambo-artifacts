# Probes on the t=2 sponge elimination polynomial f_n(x) = theta_n(x) - tau
# (psi_0 = 0, capacity convention of the paper's D_I paragraph).
# All cells tiny: degrees 16..1024. Checks: density, squarefreeness,
# decomposability (full Kozen-Landau-style base-h test over all divisor splits),
# g(x^k) substructure, and S_D cycle-type sampling at n=3 (D=16).
import time
p = 2147483647  # M31
F = GF(p)
R.<x> = PolynomialRing(F)
phi = F(7)

def build_f(n, cs, ds, tau):
    th, ps = x, R(0)   # theta_0 = free var, psi_0 = 0
    for r in range(n):
        th_new = phi*th + ps^2 + cs[r]
        ps     = phi*ps + th_new^2 + ds[r]
        th     = th_new
    return th - tau

def is_decomposable(f):
    """check all splits f = g(h(x)), deg h = s, 1 < s < D, s | D.
       h recovered from top coefficients via truncated r-th root; then test
       whether base-h expansion of f has constant coefficients."""
    D = f.degree()
    f = f.monic()
    for s in divisors(D):
        if s == 1 or s == D: continue
        r = D // s
        # h^r matches f in top s+1 coeffs: take r-th root of reversed series
        frev = R(list(reversed(f.list())))
        S.<T> = PowerSeriesRing(F, default_prec=s+1)
        try:
            hrev_ser = S(frev.list()[:s+1]).nth_root(r)
        except (ValueError, ArithmeticError):
            continue
        h = R(list(reversed(hrev_ser.padded_list(s+1))))
        if h.degree() != s: continue
        # base-h expansion of f; decomposable with this h iff all digits constant
        g, ok, rem = f, True, None
        digits = []
        while g != 0:
            g, rem = g.quo_rem(h)
            digits.append(rem)
        if all(d.degree() <= 0 for d in digits):
            return True, s
    return False, None

set_random_seed(20260610)
print("n  D     density  sqfree  irred  #Fp-roots  decomposable")
for n in [3,4,5,6]:
    cs = [F.random_element() for _ in range(n)]
    ds = [F.random_element() for _ in range(n)]
    tau = F.random_element()
    f = build_f(n, cs, ds, tau)
    D = f.degree()
    dens = sum(1 for c in f.list() if c != 0) / (D+1)
    sqf = gcd(f, f.derivative()).degree() == 0
    irr = f.is_irreducible()
    nroots = len(f.roots())
    dec, s = is_decomposable(f)
    print(n, D, float(dens), sqf, irr, nroots, dec, s)

# cycle-type sampling at n=3 (D=16): Chebotarov-style check for Gal >= A_16
# Jordan: transitive + contains a q-cycle, q prime, D/2 < q <= D-3  ==> >= A_D.
# q in {11,13}; expected density of 11-cycle 1/11, 13-cycle 1/13 (~16.7% union)
t0 = time.time(); N = 300
irred_ct, longprime_ct, root_tot = 0, 0, 0
for _ in range(N):
    cs = [F.random_element() for _ in range(3)]
    ds = [F.random_element() for _ in range(3)]
    tau = F.random_element()
    f = build_f(3, cs, ds, tau)
    if gcd(f, f.derivative()).degree() != 0: continue
    degs = sorted([g.degree() for g,_ in f.factor()])
    if degs == [16]: irred_ct += 1
    if any(d in (11,13) for d in degs): longprime_ct += 1
    root_tot += degs.count(1)
print("samples", N, "irred", irred_ct/N, "(exp 1/16=0.0625)",
      "11or13cycle", longprime_ct/N, "(exp ~0.168)",
      "mean#roots", float(root_tot/N), "(exp ~1)", "time", time.time()-t0)
