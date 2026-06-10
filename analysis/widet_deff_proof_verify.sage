# widet_deff_proof_verify.sage
# Verification of the D_eff specialization-degree proof (gate G1/G2).
#
# Mambo-t round map (paper sec:inst:wider):
#   x_1' = phi*x_1 + x_t^2     + c_{r,1}
#   x_i' = phi*x_i + (x_{i-1}')^2 + c_{r,i}   (i=2..t, uses UPDATED x_{i-1}')
# Capacity c=1 sponge: x_t(0)=0, rate inputs x_1(0)..x_{t-1}(0).
# Free a single rate input x_j(0)=z, others = constants. Track deg_z x_1(n).
#
# THEOREM (this script tests):
#   (a) ladder      deg_z x_1(n) = 2^{ t(n-1) - (j-1) }         for n>=2
#   (b) lc-invariant lc_z(x_i(r)) = phi^{ deg_z x_i(r) }  along the live cascade
#       => lc_z(x_1(n)) = phi^{2^{t(n-1)-(j-1)}}, a FIXED NONZERO constant
#          INDEPENDENT of the t-2 specialized constants AND the round constants.
#       => the degree NEVER drops: floor is unconditional, no bad locus.
#   (c) min over all 1-parameter specializations is the latest single axis
#       j=t-1  =>  D_eff = 2^{t(n-1)-(t-2)}.

def run_uni(t, n, p, phi, RC, state0):
    # state0: list length t of polys/consts in z; returns x_1(n) as poly in z
    Fp = GF(p)
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    state = [Su(s) for s in state0]
    for r in range(n):
        new = [None]*t
        new[0] = phi*state[0] + state[t-1]**2 + RC[r][0]
        for i in range(1, t):
            new[i] = phi*state[i] + new[i-1]**2 + RC[r][i]
        state = new
    return state[0]

def axis_state(t, p, jfree, consts):
    Fp = GF(p)
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    st = []
    for j in range(t-1):
        st.append(z if j == jfree else Su(consts[j]))
    st.append(Su(0))          # capacity x_t(0)=0
    return st

def test_ladder(t, n, p, seed=1):
    set_random_seed(seed)
    Fp = GF(p); phi = Fp(7)
    RC = [[Fp.random_element() for _ in range(t)] for _ in range(n)]
    consts = [Fp.random_element() for _ in range(t-1)]
    print("--- LADDER test t=%d n=%d (p=%d) ---" % (t,n,p))
    ok = True
    for jfree in range(t-1):       # 0-indexed; paper j = jfree+1
        u = run_uni(t,n,p,phi,RC, axis_state(t,p,jfree,consts))
        d = u.degree()
        pred = t*(n-1) - jfree     # exponent: t(n-1)-(j-1), j=jfree+1
        match = (d == 2**pred)
        ok = ok and match
        # lc-invariant check: lc == phi^deg
        lc = u.leading_coefficient()
        lc_pred = phi**d
        lc_ok = (lc == lc_pred)
        print("   free x_%d(0): deg=2^%d  pred 2^%d  match=%s | lc==phi^deg? %s"
              % (jfree+1, int(round(float(log(d,2)))) if d>0 else 0, pred, match, lc_ok))
    print("   ladder all-match: %s" % ok)
    return ok

def test_lc_independence(t, n, p, ntuples=40):
    # free latest axis x_{t-1}(0); vary the t-2 OTHER constants AND round
    # constants; confirm degree is constant AND lc == phi^deg every time
    # (so no specialization lowers the degree -- floor unconditional).
    Fp = GF(p); phi = Fp(7)
    jfree = t-2                    # x_{t-1}(0), 0-indexed
    pred = t*(n-1) - jfree
    degs = set(); lc_consts_ok = True
    for s in range(ntuples):
        set_random_seed(1000+s)
        RC = [[Fp.random_element() for _ in range(t)] for _ in range(n)]
        consts = [Fp.random_element() for _ in range(t-1)]
        u = run_uni(t,n,p,phi,RC, axis_state(t,p,jfree,consts))
        degs.add(u.degree())
        if u.leading_coefficient() != phi**u.degree():
            lc_consts_ok = False
    # also test structured / adversarial tuples that an attacker might pick
    struct_ok = True
    for consts in ([Fp(0)]*(t-1), [Fp(1)]*(t-1), [Fp(7)]*(t-1),
                   [Fp(-1)]*(t-1), [Fp(i) for i in range(t-1)]):
        set_random_seed(7)
        RC = [[Fp.random_element() for _ in range(t)] for _ in range(n)]
        u = run_uni(t,n,p,phi,RC, axis_state(t,p,jfree,consts))
        degs.add(u.degree())
        if u.leading_coefficient() != phi**u.degree(): struct_ok = False
    print("--- LC-INDEPENDENCE t=%d n=%d : %d random + 5 structured tuples ---"
          % (t,n,ntuples))
    print("   degree set observed = %s (singleton 2^%d expected)"
          % ({int(round(float(log(d,2)))) for d in degs}, pred))
    print("   lc==phi^deg on ALL random tuples? %s ; on structured? %s"
          % (lc_consts_ok, struct_ok))
    print("   => unconditional floor holds: %s"
          % (degs == {2**pred} and lc_consts_ok and struct_ok))
    return degs == {2**pred} and lc_consts_ok and struct_ok

def test_multiaxis_only_raises(t, n, p, seed=3):
    # free latest axis as z; make an EARLIER coordinate also linear in z
    # (attacker's 2-parameter->1-parameter collapse). Should only RAISE degree.
    set_random_seed(seed)
    Fp = GF(p); phi = Fp(7)
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    RC = [[Fp.random_element() for _ in range(t)] for _ in range(n)]
    base = t*(n-1) - (t-2)
    # single best axis:
    consts = [Fp.random_element() for _ in range(t-1)]
    d_axis = run_uni(t,n,p,phi,RC, axis_state(t,p,t-2,consts)).degree()
    # 2-coordinate linear injection: x_{t-1}=z, x_{t-2}=a*z+b
    st = axis_state(t,p,t-2,consts)
    st[t-3] = Fp.random_element()*z + Fp.random_element()  # earlier axis t-2 (0-idx t-3)
    d_two = run_uni(t,n,p,phi,RC, st).degree()
    print("--- MULTI-AXIS t=%d n=%d : single-axis 2^%d vs 2-coord-linear deg %d (2^%s) ---"
          % (t,n,int(round(float(log(d_axis,2)))), d_two,
             round(float(log(d_two,2)),2) if d_two>0 else 0))
    print("   2-coord >= single-axis (only raises)? %s" % (d_two >= d_axis))
    return d_two >= d_axis

if __name__ == '__main__':
    p = 65521
    print("==== (a) LADDER: fresh cells beyond original study ====")
    test_ladder(3, 6, p, seed=11)     # best deg 2^14
    test_ladder(4, 5, p, seed=11)     # best deg 2^14
    test_ladder(5, 4, p, seed=11)     # best deg 2^12
    print()
    print("==== (b) LEADING-COEFFICIENT INDEPENDENCE (unconditional floor) ====")
    test_lc_independence(3, 4, p)     # deg 2^8
    test_lc_independence(4, 4, p)     # deg 2^10
    test_lc_independence(4, 3, p)     # deg 2^6
    test_lc_independence(5, 3, p)     # deg 2^7
    print()
    print("==== (c) AXIS OPTIMALITY: multi-coord only raises ====")
    test_multiaxis_only_raises(4, 4, p)
    test_multiaxis_only_raises(5, 3, p)
