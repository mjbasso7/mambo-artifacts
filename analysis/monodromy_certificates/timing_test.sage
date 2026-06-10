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

def build_theta(n, rc):
    th, ps = x, R(0)
    for r in range(n):
        c, d = rc[r]
        th_new = phi*th + ps^2 + c
        ps = phi*ps + th_new^2 + d
        th = th_new
    return th

for n in [4,5]:
    rc = derive_rc(n)
    t0=time.time(); th = build_theta(n, rc); t1=time.time()
    f = th - F(1)
    t2=time.time(); fac = f.factor(); t3=time.time()
    print("n=%d deg=%d build=%.2fs factor=%.2fs pattern=%s" % (n, th.degree(), t1-t0, t3-t2, sorted([g.degree() for g,_ in fac])))
