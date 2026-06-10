# Production constants (BN254): (1) full Kozen-Landau indecomposability of theta_n,
# (2) Morse check: V(s) = Res_x(theta_n - s, theta_n') squarefree  (critical values
# distinct + critical points simple), via evaluation/interpolation.
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

for n in [3,4,5]:
    th = build_theta(n); D = th.degree()
    t0=time.time()
    dec, s = is_decomposable(th)
    t1=time.time()
    # Morse: V(s0) = Res(th - s0, th') for D interpolation points
    dth = th.derivative()
    sqf_dth = gcd(dth, dth.derivative()).degree() == 0
    pts = []
    Vdeg = dth.degree()  # = D-1
    for s0 in range(Vdeg+1):
        pts.append((F(s0), (th - F(s0)).resultant(dth)))
    Rs.<sv> = PolynomialRing(F)
    V = Rs.lagrange_polynomial(pts)
    morse = (V.degree() == Vdeg) and gcd(V, V.derivative()).degree() == 0
    t2=time.time()
    print("n=%d D=%d decomposable=%s split=%s (%.1fs) | theta' sqfree=%s V-deg=%d Morse(V sqfree)=%s (%.1fs)"
          % (n, D, dec, s, t1-t0, sqf_dth, V.degree(), morse, t2-t1))
