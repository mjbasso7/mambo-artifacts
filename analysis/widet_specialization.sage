# widet_specialization.sage
# The free-variable / specialization question for wider-state Mambo sponge CICO.
#
# Mambo-t round map (paper sec:inst:wider):
#   x_1' = phi*x_1 + x_t^2 + c_{r,1}
#   x_i' = phi*x_i + (x_{i-1}')^2 + c_{r,i}   for i=2..t   (uses updated x_{i-1}')
#
# Deployed hash sponge convention: capacity c=1 => x_t(0)=0, rate inputs
# x_1(0)..x_{t-1}(0) FREE (t-1 unknowns), output x_1(n)=tau (1 equation).
# Underdetermined.  PROVEN: with capacity c=t-1 (only x_1(0) free) deg = 2^{t(n-1)}.
#
# Attacker at c=1 specializes t-2 free inputs to constants, leaves ONE free,
# solves the univariate.  We measure the univariate degree for EACH choice of
# free variable (others = generic random constants), so the multivariate blow-up
# is avoided: each measurement is a single univariate iteration.
#
# Outputs per cell: partial degree of x_1(n) in each free input, the attacker's
# best (minimum) choice + its squarefreeness, vs naive D_I=2^{t(n-1)} and the
# closed-form prediction E(t,n)=t(n-2)+2 (free the latest rate var x_{t-1}).

def partial_deg_in(t, n, p, jfree, RC, phi, consts):
    # univariate x_1(n) with x_jfree(0)=z free, other rate vars = consts[*],
    # capacity x_t(0)=0.  Returns the univariate polynomial in z.
    Fp = GF(p)
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    state = []
    for j in range(t-1):              # x_1(0)..x_{t-1}(0)
        state.append(z if j == jfree else Su(consts[j]))
    state.append(Su(0))               # x_t(0) capacity = 0
    for r in range(n):
        new = [None]*t
        new[0] = phi*state[0] + state[t-1]**2 + RC[r][0]
        for i in range(1, t):
            new[i] = phi*state[i] + new[i-1]**2 + RC[r][i]
        state = new
    return state[0]

def total_deg(t, n, p, RC, phi):
    # generic direction: all free rate vars = a_j*z + b_j  -> univariate degree
    # equals the total degree of the multivariate map generically.
    Fp = GF(p)
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    state = []
    for j in range(t-1):
        state.append(Fp.random_element()*z + Fp.random_element())
    state.append(Su(0))
    for r in range(n):
        new = [None]*t
        new[0] = phi*state[0] + state[t-1]**2 + RC[r][0]
        for i in range(1, t):
            new[i] = phi*state[i] + new[i-1]**2 + RC[r][i]
        state = new
    return state[0].degree()

def run_cell(t, n, p, seed=1, verbose=True):
    set_random_seed(seed)
    Fp = GF(p)
    RC = [[Fp.random_element() for _ in range(t)] for _ in range(n)]
    phi = Fp(7)
    consts = [Fp.random_element() for _ in range(t-1)]

    partial = []
    unis = []
    for jfree in range(t-1):
        u = partial_deg_in(t, n, p, jfree, RC, phi, consts)
        partial.append(u.degree())
        unis.append(u)
    td = total_deg(t, n, p, RC, phi)

    naive_DI = 2**(t*(n-1))
    pred_E   = 2**(t*(n-2)+2)
    jbest = min(range(t-1), key=lambda j: partial[j])
    ubest = unis[jbest]
    sqfree = ubest.is_squarefree() if ubest.degree() >= 1 else None

    if verbose:
        print("=== t=%d n=%d p=%d seed=%d ===" % (t, n, p, seed))
        print("  naive D_I = 2^%d = %d" % (t*(n-1), naive_DI))
        print("  total deg (generic direction) = %d (2^%d), == naive D_I? %s"
              % (td, int(round(float(log(td,2)))) if td>0 else 0, td == naive_DI))
        pe = [int(round(float(log(d,2)))) if d>0 else 0 for d in partial]
        print("  partial degs [free x_1(0)..x_{t-1}(0)] = %s  (exps %s)" % (partial, pe))
        print("  ATTACKER best: free x_%d(0), deg = %d (2^%d), squarefree=%s"
              % (jbest+1, partial[jbest],
                 int(round(float(log(partial[jbest],2)))) if partial[jbest]>0 else 0, sqfree))
        print("  closed-form E(t,n)=t(n-2)+2 = %d -> 2^%d = %d ; best==pred? %s"
              % (t*(n-2)+2, t*(n-2)+2, pred_E, partial[jbest]==pred_E))
        print("  reduction vs naive: factor 2^%d ; vs t=2-equiv(2^{2(n-1)}=%d): %s"
              % (t*(n-1)-(t*(n-2)+2), 2**(2*(n-1)),
                 "ABOVE t=2" if partial[jbest] > 2**(2*(n-1)) else "<= t=2"))
        print()
    return dict(t=t,n=n,naive=int(naive_DI),total=int(td),partial=[int(x) for x in partial],
                best_var=jbest+1,best=int(partial[jbest]),sqfree=(bool(sqfree) if sqfree is not None else None),
                predE=int(pred_E))

if __name__ == '__main__':
    p = 65521
    grid = []
    for t in [3,4,5]:
        for n in [2,3,4,5]:
            if t*(n-1) > 14:   # cap univariate degree at 2^14
                continue
            grid.append((t,n))
    res = []
    for (t,n) in grid:
        res.append(run_cell(t,n,p,seed=1))
    print("---- second seed ----")
    for (t,n) in grid:
        if t*(n-1) <= 12:
            run_cell(t,n,p,seed=2)
    # summary table
    print("\n==== SUMMARY ====")
    print("t  n | naiveExp totalExp | bestVar bestExp predExp | sqfree | E=t(n-2)+2")
    for r in res:
        be = int(round(float(log(r['best'],2)))) if r['best']>0 else 0
        ne = int(round(float(log(r['naive'],2))))
        te = int(round(float(log(r['total'],2)))) if r['total']>0 else 0
        pe = int(round(float(log(r['predE'],2))))
        print("%d  %d |   %2d      %2d   |   x%d     %2d      %2d   |  %s  |  %d"
              % (r['t'],r['n'],ne,te,r['best_var'],be,pe,r['sqfree'],r['t']*(r['n']-2)+2))
