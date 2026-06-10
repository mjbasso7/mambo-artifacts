# Verification battery for the rigorous non-telescoping proposition
# (paper label prop:nontelescoping), production constants and fields.
#
# Round map (paper app:reference):
#   theta' = phi*theta + psi^2 + c_i
#   psi'   = phi*psi   + (theta')^2 + d_i
# Sponge CICO convention: psi_0 = 0, output theta_n = tau, unknown a = theta_0.
#
# Cells (run: sage nontelescoping_verify.sage <CELL> ; CELL in 0,A,B,C,D,E,F,G):
#   0  test-vector cross-check against the paper appendix (BN254 + Goldilocks)
#   A  CICO iterate degrees and leading coefficients, n = 1..6, both fields:
#        deg Theta_n = 4^(n-1), lc = phi^(4^(n-1));
#        deg Psi_n   = 2*4^(n-1), lc = phi^(2*4^(n-1)).
#   B  free-input convention, n = 1..4: top homogeneous component of Psi_n is
#        the single monomial psi0^(4^n) with coefficient 1 (monic; no condition
#        on phi or the constants), and of Theta_n is psi0^(2*4^(n-1)).
#   C  backward-half weighted lemma, k = 1..4: with weights w(x)=1, w(y)=2 the
#        top weighted component of Theta'_k(x,y) is the single monomial
#        y^(2*4^(k-1)) with coefficient 1 (and of Psi'_k is y^(4^k)).
#   D  split exactness: for n = 2..5 and every round-boundary split m
#        (k = n-m <= 4), P_k(F_m, G_m) == Theta_n identically; same for
#        half-round cuts (state (theta_m, psi_(m-1)), dominant monomial
#        u^(4^(n-m)) with coefficient 1).
#   E  middle-state eliminant: f_n = Theta_n - tau squarefree at sampled tau;
#        minimal polynomial of F_m mod f_n has full degree 4^(n-1) for every
#        split m (Wiedemann projection + Berlekamp--Massey; a full-degree
#        recurrence minimal polynomial is a one-sided certificate, since the
#        sequence minimal polynomial divides the algebra-element minimal
#        polynomial).  n = 2..6 over BN254 and Goldilocks.
#   F  wider state t = 3, 4 (capacity zeroed): deg = 2^(t(n-1)),
#        lc = phi^(2^(t(n-1))), n = 2..3.
#   G  properness of the half-parametrization a -> (F_m(a), G_m(a)):
#        gcd(F_m(X)-F_m(Y), G_m(X)-G_m(Y)) = X - Y, m = 1..3.
#
# All cells are deterministic except the Wiedemann projection point in E,
# which is seeded.  Every cell runs in well under a minute on an M-class
# laptop.

import hashlib, sys, time

# ----------------------------------------------------------------- parameters

P_BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
P_GOLDI = 18446744069414584321
PHI_BN254 = 7
PHI_GOLDI = 16032412539219608744

FIELDS = [("BN254", P_BN254, PHI_BN254), ("Goldilocks", P_GOLDI, PHI_GOLDI)]


def derive_round_constants(n, p, seed=b"Mambo_round_constants"):
    vals = []
    for j in range(2 * n):
        h = hashlib.sha256(seed + int(j).to_bytes(4, "big")).digest()
        v = int.from_bytes(h, "big") % p
        vals.append(v if v != 0 else 1)
    return [(vals[i], vals[n + i]) for i in range(n)]


def tau_sample(p):
    t = int.from_bytes(hashlib.sha256(b"nontelescoping_tau").digest(), "big") % p
    return [0, 1, t]


# ------------------------------------------------------------------- iterates

def cico_iterates(p, phi, n):
    """Theta_i, Psi_i in GF(p)[a] with psi_0 = 0, i = 1..n."""
    K = GF(p)
    R = PolynomialRing(K, "a")
    a = R.gen()
    rc = derive_round_constants(n, p)
    th, ps = a, R(0)
    out = []
    for i in range(n):
        c, d = rc[i]
        th = phi * th + ps**2 + c
        ps = phi * ps + th**2 + d
        out.append((th, ps))
    return R, out


def free_iterates(p, phi, n):
    """Theta_i, Psi_i in GF(p)[t0, p0], both inputs free."""
    K = GF(p)
    R = PolynomialRing(K, ["t0", "p0"])
    t0, p0 = R.gens()
    rc = derive_round_constants(n, p)
    th, ps = t0, p0
    out = []
    for i in range(n):
        c, d = rc[i]
        th = phi * th + ps**2 + c
        ps = phi * ps + th**2 + d
        out.append((th, ps))
    return R, out


def backward_iterates(p, phi, n, m):
    """Theta'_j, Psi'_j in GF(p)[x, y] for rounds m+1..n of the n-round
    schedule, from a free middle state (x, y) = (theta_m, psi_m)."""
    K = GF(p)
    R = PolynomialRing(K, ["x", "y"])
    x, y = R.gens()
    rc = derive_round_constants(n, p)
    th, ps = x, y
    out = []
    for i in range(m, n):
        c, d = rc[i]
        th = phi * th + ps**2 + c
        ps = phi * ps + th**2 + d
        out.append((th, ps))
    return R, out


def top_weighted(poly, wx, wy):
    """Set of (exponent pair, coeff) attaining the max weighted degree."""
    best, arg = -1, []
    for (i, j), cf in poly.dict().items():
        w = i * wx + j * wy
        if w > best:
            best, arg = w, [((i, j), cf)]
        elif w == best:
            arg.append(((i, j), cf))
    return best, arg


def seq_minpoly_degree(f, b, gamma, D):
    """Degree of the minimal polynomial of the recurrent sequence
    s_j = (b^j mod f)(gamma), j = 0..2D-1, via Berlekamp--Massey."""
    from sage.matrix.berlekamp_massey import berlekamp_massey
    R = f.parent()
    cur = R(1)
    seq = []
    for _ in range(2 * D):
        seq.append(cur(gamma))
        cur = (cur * b) % f
    mp = berlekamp_massey(seq)
    return mp.degree()


# ----------------------------------------------------------------------- cells

def cell_0():
    print("[0] test-vector cross-check (paper app:testvectors)")
    for name, p, phi, want in [
        ("BN254", P_BN254, PHI_BN254,
         (17394732535357230360797223449306942855161894228674458177983473076235044019007,
          7276451156888393224863406760675751049923791015985763477840281348092940222991)),
        ("Goldilocks", P_GOLDI, PHI_GOLDI,
         (12438125745882980229, 10673594131594801318)),
    ]:
        rc = derive_round_constants(65, p)
        th, ps = 1, 1
        for i in range(65):
            c, d = rc[i]
            th = (phi * th + ps * ps + c) % p
            ps = (phi * ps + th * th + d) % p
        ok = (th, ps) == want
        print("    %-10s n=65 seed (1,1): %s" % (name, "MATCH" if ok else "MISMATCH"))
        assert ok
    print("[0] PASS")


def cell_A():
    print("[A] CICO degrees and leading coefficients, n = 1..6")
    for name, p, phi in FIELDS:
        K = GF(p)
        for n in range(1, 7):
            R, it = cico_iterates(p, phi, n)
            th, ps = it[-1]
            D = 4 ** (n - 1)
            assert th.degree() == D, (name, n, "deg theta")
            assert th.leading_coefficient() == K(phi) ** D, (name, n, "lc theta")
            assert ps.degree() == 2 * D, (name, n, "deg psi")
            assert ps.leading_coefficient() == K(phi) ** (2 * D), (name, n, "lc psi")
            print("    %-10s n=%d: deg(Theta)=%d lc=phi^%d, deg(Psi)=%d lc=phi^%d  OK"
                  % (name, n, D, D, 2 * D, 2 * D))
    print("[A] PASS")


def cell_B():
    print("[B] free-input top homogeneous components, n = 1..4 (BN254)")
    p, phi = P_BN254, PHI_BN254
    for n in range(1, 5):
        R, it = free_iterates(p, phi, n)
        th, ps = it[-1]
        for poly, J, lbl in [(th, 2 * 4 ** (n - 1), "Theta"), (ps, 4**n, "Psi")]:
            w, arg = top_weighted(poly, 1, 1)
            assert w == J and len(arg) == 1, (n, lbl)
            (i, j), cf = arg[0]
            assert (i, j) == (0, J) and cf == 1, (n, lbl)
            print("    n=%d %-5s: top component = psi0^%d, coeff 1  OK" % (n, lbl, J))
    print("[B] PASS")


def cell_C():
    print("[C] backward-half weighted lemma, w(x)=1 w(y)=2, k = 1..4 (BN254)")
    p, phi = P_BN254, PHI_BN254
    n = 5
    for m in range(1, 5):           # constants of rounds m+1..n; k = n - m
        R, it = backward_iterates(p, phi, n, m)
        for k in range(1, n - m + 1):
            th, ps = it[k - 1]
            for poly, J, W, lbl in [
                (th, 2 * 4 ** (k - 1), 4**k, "Theta'"),
                (ps, 4**k, 2 * 4**k, "Psi'"),
            ]:
                w, arg = top_weighted(poly, 1, 2)
                assert w == W and len(arg) == 1, (m, k, lbl)
                (i, j), cf = arg[0]
                assert (i, j) == (0, J) and cf == 1, (m, k, lbl)
        print("    m=%d: all k <= %d top components are single monomials y^(2*4^(k-1)) "
              "/ y^(4^k), coeff 1  OK" % (m, n - m))
    print("[C] PASS")


def cell_D():
    print("[D] split exactness, n = 2..5, all cuts (BN254)")
    p, phi = P_BN254, PHI_BN254
    K = GF(p)
    for n in range(2, 6):
        Ru, it_u = cico_iterates(p, phi, n)
        Theta_n = it_u[-1][0]
        D = 4 ** (n - 1)
        # round-boundary splits
        for m in range(1, n):
            F = it_u[m - 1][0]
            G = it_u[m - 1][1]
            assert F.degree() == 4 ** (m - 1) and G.degree() == 2 * 4 ** (m - 1)
            Rb, it_b = backward_iterates(p, phi, n, m)
            Pk = it_b[-1][0]                      # theta after rounds m+1..n
            comp = Pk(F, G)
            assert comp == Theta_n, (n, m, "round-boundary identity")
            assert comp.degree() == D
            assert comp.leading_coefficient() == K(phi) ** D
        # half-round cuts: state (theta_m, psi_(m-1)); remaining = psi-half of
        # round m, then rounds m+1..n
        rc = derive_round_constants(n, p)
        for m in range(2, n):
            Fu = it_u[m - 1][0]                   # theta_m, degree 4^(m-1)
            Gv = it_u[m - 2][1]                   # psi_(m-1), degree 4^(m-1)/2
            Rb = PolynomialRing(K, ["u", "v"])
            u, v = Rb.gens()
            th, ps = u, K(phi) * v + u**2 + rc[m - 1][1]
            for i in range(m, n):
                c, d = rc[i]
                th = phi * th + ps**2 + c
                ps = phi * ps + th**2 + d
            B = th
            w, arg = top_weighted(B, 2, 1)
            J = 4 ** (n - m)
            assert w == 2 * J and len(arg) == 1, (n, m, "half-cut weight")
            (i, j), cf = arg[0]
            assert (i, j) == (J, 0) and cf == 1, (n, m, "half-cut monomial")
            comp = B(Fu, Gv)
            assert comp == Theta_n, (n, m, "half-cut identity")
            assert comp.degree() == D
        print("    n=%d: all round-boundary and half-round cuts meet at degree %d, "
              "lc = phi^%d  OK" % (n, D, D))
    print("[D] PASS")


def cell_E(nmax_bn=6, nmax_go=6):
    print("[E] middle-state eliminant: squarefreeness of f_n and full-degree")
    print("    minimal polynomial of F_m mod f_n (Berlekamp--Massey certificate)")
    set_random_seed(20260610)
    for name, p, phi in FIELDS:
        K = GF(p)
        nmax = nmax_bn if name == "BN254" else nmax_go
        for n in range(2, nmax + 1):
            t0 = time.time()
            R, it = cico_iterates(p, phi, n)
            Theta_n = it[-1][0]
            D = 4 ** (n - 1)
            for tau in tau_sample(p):
                f = Theta_n - tau
                assert gcd(f, f.derivative()).degree() == 0, (name, n, tau, "squarefree")
            tau = tau_sample(p)[2]
            f = Theta_n - tau
            for m in range(1, n):
                b = it[m - 1][0] % f
                gamma = K.random_element()
                dmin = seq_minpoly_degree(f, b, gamma, D)
                assert dmin == D, (name, n, m, "minpoly degree %d != %d" % (dmin, D))
            print("    %-10s n=%d: f_n squarefree at tau in {0, 1, tau*}; "
                  "deg minpoly(F_m mod f_n) = %d for all m = 1..%d  OK  (%.1fs)"
                  % (name, n, D, n - 1, time.time() - t0))
    print("[E] PASS")


def cell_F():
    print("[F] wider state t = 3, 4 (capacity zeroed), n = 2..3")
    for name, p, phi in FIELDS:
        K = GF(p)
        for t in (3, 4):
            for n in (2, 3):
                R = PolynomialRing(K, "a")
                a = R.gen()
                # constants: same SHA-256 stream, t per round (the degree/lc
                # statement is constant-agnostic; the stream only needs to be
                # deterministic)
                vals = []
                j = 0
                while len(vals) < t * n:
                    h = hashlib.sha256(b"Mambo_round_constants" + int(j).to_bytes(4, "big")).digest()
                    v = int.from_bytes(h, "big") % p
                    vals.append(v if v != 0 else 1)
                    j += 1
                state = [a] + [R(0)] * (t - 1)
                for r in range(n):
                    new1 = phi * state[0] + state[t - 1] ** 2 + vals[r * t]
                    new = [new1]
                    for i in range(1, t):
                        new.append(phi * state[i] + new[i - 1] ** 2 + vals[r * t + i])
                    state = new
                D = 2 ** (t * (n - 1))
                assert state[0].degree() == D, (name, t, n)
                assert state[0].leading_coefficient() == K(phi) ** D, (name, t, n)
                print("    %-10s t=%d n=%d: deg(x1) = 2^%d = %d, lc = phi^%d  OK"
                      % (name, t, n, t * (n - 1), D, D))
    print("[F] PASS")


def cell_G():
    print("[G] properness of a -> (F_m(a), G_m(a)): gcd test, m = 1..3 (BN254)")
    p, phi = P_BN254, PHI_BN254
    n = 5
    Ru, it = cico_iterates(p, phi, n)
    RY = PolynomialRing(GF(p), "Y")
    Y = RY.gen()
    RX = PolynomialRing(RY.fraction_field(), "X")
    X = RX.gen()
    def euclid_gcd(u, w):
        while not w.is_zero():
            u, w = w, u % w
        return u / u.leading_coefficient()

    for m in range(1, 4):
        F, G = it[m - 1]
        g = euclid_gcd(F(X) - RX(F(Y)), G(X) - RX(G(Y)))
        assert g == X - RX(Y), (m, g)
        print("    m=%d: gcd(F_m(X)-F_m(Y), G_m(X)-G_m(Y)) = X - Y  OK" % m)
    print("[G] PASS")


CELLS = {"0": cell_0, "A": cell_A, "B": cell_B, "C": cell_C,
         "D": cell_D, "E": cell_E, "F": cell_F, "G": cell_G}

if __name__ == "__main__":
    args = [s for s in sys.argv[1:] if s in CELLS] or list(CELLS)
    for c in args:
        t0 = time.time()
        CELLS[c]()
        print("    cell %s wall time: %.1fs\n" % (c, time.time() - t0))
