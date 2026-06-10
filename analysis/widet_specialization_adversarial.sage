# widet_specialization_adversarial.sage
# Strategy (b): can the attacker beat the single-axis specialization degree
# 2^{t(n-2)+2} by exploiting the remaining t-2 dof more cleverly?
#
# We free x_{t-1}(0)=z (the optimal axis) and test whether ANY choice of the
# other t-2 rate inputs lowers the univariate degree of x_1(n) below the
# generic value via leading-coefficient cancellation:
#   (i) many random constant tuples (degree distribution),
#   (ii) structured tuples: all-zero, all-equal, arithmetic ramp,
#   (iii) "nonlinear" specialization: set a fixed var = a*z+b or a*z^2 (this can
#        only raise degree, included for completeness as a sanity check),
#   (iv) free a DIFFERENT axis and confirm the x_{t-1} axis is the global min.

def build_uni(t, n, p, RC, phi, state0):
    # state0: list of length t of univariate polys (in z) / constants
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

def probe(t, n, p, seed=1, trials=200):
    set_random_seed(seed)
    Fp = GF(p)
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    RC = [[Fp.random_element() for _ in range(t)] for _ in range(n)]
    phi = Fp(7)
    target = 2**(t*(n-2)+2)
    jfree = t-2   # 0-indexed: x_{t-1}(0)

    def state_with(consts, freeval=z):
        st = []
        for j in range(t-1):
            st.append(freeval if j == jfree else Su(consts[j]))
        st.append(Su(0))    # capacity
        return st

    # (i) random constant tuples
    mindeg = None; degset = {}
    for _ in range(trials):
        consts = [Fp.random_element() for _ in range(t-1)]
        d = build_uni(t,n,p,RC,phi, state_with(consts)).degree()
        degset[d] = degset.get(d,0)+1
        mindeg = d if mindeg is None else min(mindeg,d)
    # (ii) structured tuples
    struct = {}
    for name, consts in [
        ("all-zero", [Fp(0)]*(t-1)),
        ("all-one",  [Fp(1)]*(t-1)),
        ("ramp",     [Fp(j) for j in range(t-1)]),
        ("all-equal-7", [Fp(7)]*(t-1)),
    ]:
        struct[name] = build_uni(t,n,p,RC,phi, state_with(consts)).degree()
    # (iii) nonlinear specialization of fixed vars (set one fixed var = a*z+b)
    nonlin = None
    if t >= 3:
        consts = [Fp.random_element() for _ in range(t-1)]
        st = state_with(consts)
        # replace one fixed coordinate (the first non-free) with a*z+b
        jx = 0 if jfree != 0 else 1
        st[jx] = Fp.random_element()*z + Fp.random_element()
        nonlin = build_uni(t,n,p,RC,phi, st).degree()
    # (iv) every axis min (confirm x_{t-1} global min)
    consts0 = [Fp.random_element() for _ in range(t-1)]
    axis = []
    for jf in range(t-1):
        st = []
        for j in range(t-1):
            st.append(z if j==jf else Su(consts0[j]))
        st.append(Su(0))
        axis.append(build_uni(t,n,p,RC,phi, st).degree())

    print("=== t=%d n=%d (target single-axis deg = 2^%d = %d) ==="
          % (t,n,t*(n-2)+2,target))
    print("  (i) %d random constant tuples: degrees observed = %s ; MIN = %d (== target? %s)"
          % (trials, dict(sorted(degset.items())), mindeg, mindeg==target))
    print("  (ii) structured tuples: %s" % struct)
    print("  (iii) nonlinear fixed-var (a*z+b): deg = %s (>= target expected)" % nonlin)
    print("  (iv) per-axis degrees [free x_1..x_{t-1}] = %s ; global min = %d, x_{t-1}-axis = %d"
          % (axis, min(axis), axis[t-2]))
    print("  --> strategy (b) beats single-axis? %s" %
          (mindeg < target or (nonlin is not None and nonlin < target)
           or min(axis) < target))
    print()

if __name__ == '__main__':
    p = 65521
    for (t,n) in [(3,3),(4,3),(5,3),(3,4),(4,4)]:
        probe(t,n,p,seed=1,trials=300)
