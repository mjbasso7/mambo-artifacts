# Independent re-check of every certificate row in this certificate set.
import hashlib
pB = 21888242871839275222246405745257275088548364400416034343698204186575808495617
pM = 2147483647

def build(p, phi, cs, ds, x):  # returns theta_n
    th, ps = x, 0
    for c, d in zip(cs, ds):
        th = phi*th + ps^2 + c
        ps = phi*ps + th^2 + d
    return th

def check(p, n, cs, ds, tau, want_pattern, want_q=None):
    F = GF(p); R.<x> = PolynomialRing(F)
    th = build(p, F(7), [F(c) for c in cs], [F(d) for d in ds], x)
    D = 4^(n-1)
    assert th.degree() == D
    f = th - F(tau)
    assert gcd(f, f.derivative()).degree() == 0, "not squarefree"
    degs = sorted([g.degree() for g,_ in f.factor()])
    assert degs == want_pattern, (degs, want_pattern)
    r = len(degs); odd = (r % 2 == 1)
    if want_q is not None:
        assert is_prime(want_q) and D//2 < want_q <= D-3
        assert degs.count(want_q) == 1
        rest = [d for d in degs if d != want_q]
        assert gcd(lcm(rest) if rest else 1, want_q) == 1
    return "OK D=%d pattern=%s q=%s oddperm=%s" % (D, degs, want_q, odd)

def rc(n, p):
    vals=[]
    for j in range(2*n):
        h = hashlib.sha256(b"Mambo_round_constants" + j.to_bytes(4,"big")).digest()
        v = int.from_bytes(h,"big") % p
        vals.append(v if v else 1)
    return vals[:n], vals[n:2*n]

# 3.1 production BN254
for n, tau, pat, q in [(3,3,[1,4,11],11),(3,1,[16],None),(4,7,[1,2,18,43],43),(4,5,[64],None),
                       (5,6,[1,1,3,251],251),(5,186,[256],None),
                       (6,11,[8,32,33,46,64,182,659],659)]:
    cs, ds = rc(n, pB)
    print("B n=%d tau=%d:" % (n,tau), check(pB, n, cs, ds, tau, pat, q))

# 3.3 generic M31
rows = [
 (4,[640785602,1617968796,2101798401,1165249862],[2123199745,1719219954,1878394761,1588345379],107788194,[1,1,1,6,14,41],41),
 (4,[1996465950,1393165331,1808553745,445941757],[572751535,269081540,1997441503,1732110744],533899672,[64],None),
 (5,[1748679906,1705043031,455844984,173210222,2096951283],[463086172,1987092169,1907487492,1435346975,184755444],2072557002,[1,1,2,15,56,181],181),
 (5,[1985288736,1207886123,845289828,628011290,1927953157],[2078629511,235807108,1229033941,1888445540,239188534],448911897,[256],None),
]
for n, cs, ds, tau, pat, q in rows:
    print("A n=%d:" % n, check(pM, n, cs, ds, tau, pat, q))
print("ALL CERTIFICATE ROWS VERIFIED")
