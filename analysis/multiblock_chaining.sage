# multiblock_chaining.sage
# Review item (a): the multi-block chaining-value specialization gap.
#
# WITHIN-block study (analysis/widet_specialization.sage) established: at
# capacity c=1 a SINGLE
# permutation, freeing the t-1 rate inputs and solving the cheapest univariate,
# costs the attacker exactly (t-2) bits below the naive D_I = 2^{t(n-1)}:
#       D_eff(t,n) = 2^{t(n-1)-(t-2)} = 2^{t(n-2)+2}.
#
# THIS study: a TWO-block sponge absorption. The capacity output of block 1 is
# an intermediate CHAINING VALUE v that is fed as the incoming capacity of
# block 2. In a multi-block CICO / collision attack the adversary may get to
# CHOOSE v (freedom beyond a single block). QUESTION: does that extra freedom
# lower the effective eliminant degree BELOW the single-block D_eff -- does the
# (t-2)-bit per-block loss COMPOUND, or worse?
#
# Mambo-t round map (paper sec:inst:wider), phi=7:
#   x_1' = phi*x_1 + x_t^2 + c_{r,1}
#   x_i' = phi*x_i + (x_{i-1}')^2 + c_{r,i}    i=2..t  (uses UPDATED x_{i-1}')
#
# Sponge, capacity c=1:
#   state = (x_1,...,x_t); rate cells = x_1..x_{t-1}, capacity cell = x_t.
#   Block 1: input  x_1(0)=m1_1,...,x_{t-1}(0)=m1_{t-1}, x_t(0)=0.
#            P  (n rounds) -> output state s1; chaining value v := s1[t] (capacity).
#   Absorb m2 into rate: s1[i] += m2_i for i=1..t-1 ; capacity cell s1[t]=v kept.
#   Block 2: P (n rounds) -> output s2; CICO constraint s2[1] = tau.
#
# We measure the EFFECTIVE eliminant degree (the cheapest univariate the attacker
# must root-find) under several adversary models, all reduced to ONE free
# variable via specialization (so each measurement is a single univariate; no
# Groebner blow-up). Models:
#
#   MODEL B0 (baseline single block, for calibration): one block only, free the
#     best rate var x_{t-1}(0), others generic; deg == D_eff = 2^{t(n-2)+2}.
#
#   MODEL B1 (weak two-block / honest sponge): attacker controls m1, m2 but v is
#     DETERMINED by block 1 (v = s1[t] as a polynomial in m1). The full system in
#     the free m1/m2 inputs; we free one input, fix the rest to generic consts.
#     This is the real sponge: v is not independent.
#
#   MODEL B2 (STRONG / chosen chaining value): attacker treats v as a FREE
#     chosen variable for block 2 AND must satisfy the block-1 consistency
#     v = s1[t](m1). Two coupled equations:  s2[1](m2,v) = tau ,  s1[t](m1) = v.
#     The attacker's cheapest path: pick v and m2 to solve block 2's univariate,
#     then invert block 1 to hit that v. We measure (i) the degree of block 2's
#     map in its best free variable WITH v free, and (ii) the degree of the
#     block-1 inversion v = s1[t](m1) in its best free m1 variable. The honest
#     two-block effective degree is governed by the MAX of the two stages
#     (sequential root-finds), and the per-block bits-lost is what we compare to
#     the disclosed (t-2).
#
#   MODEL B3 (collision via chosen v, adversarial): scan which free variable in
#     block 2 (including v itself) minimizes the degree of s2[1]-tau; report the
#     worst (lowest) attacker degree found. This is the adversarial search:
#     can choosing v as the free axis beat the (t-2)-per-block floor?
#
# All measurements: univariate partial degrees via dense polynomial iteration.
# Two seeds; spot-check one BN254 cell. nice -n 19, sequential.

import time

# ----- BN254 scalar field prime (production spot-check) -----
BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617

def make_RC(Fp, t, n, seed):
    set_random_seed(seed)
    return [[Fp.random_element() for _ in range(t)] for _ in range(n)]

def perm(state, RC, phi, t, n):
    """One Mambo-t permutation P over a polynomial ring (n rounds)."""
    for r in range(n):
        new = [None]*t
        new[0] = phi*state[0] + state[t-1]**2 + RC[r][0]
        for i in range(1, t):
            new[i] = phi*state[i] + new[i-1]**2 + RC[r][i]
        state = new
    return state

# ---------------------------------------------------------------------------
# B0 / B1 / B2 measurement primitives
# ---------------------------------------------------------------------------

def single_block_best(t, n, Fp, RC, phi, consts):
    """Single block, capacity=0, free each rate var in turn (others=consts);
       return (min_deg, argmin_var, list_of_partial_degs)."""
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    degs = []
    for jfree in range(t-1):
        state = [ (z if j==jfree else Su(consts[j])) for j in range(t-1) ] + [Su(0)]
        out = perm(state, RC, phi, t, n)
        degs.append(out[0].degree())
    jbest = min(range(t-1), key=lambda j: degs[j])
    return degs[jbest], jbest, degs

def block1_chaining_poly(t, n, Fp, RC1, phi, jfree, consts):
    """Block 1 capacity output v = s1[t] as univariate in rate var x_jfree(0)
       (others = consts, capacity in = 0). Returns the polynomial (the chaining
       value as a function of one chosen input)."""
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    state = [ (z if j==jfree else Su(consts[j])) for j in range(t-1) ] + [Su(0)]
    out = perm(state, RC1, phi, t, n)
    return out  # full output state; out[t-1] is capacity v, out[0..t-2] rate

def block2_with_chosen_v(t, n, Fp, RC2, phi, free_axis, fixed_rate, v_const, m2_consts):
    """Block 2 with incoming capacity = v (a constant or the free var), rate
       inputs = m2_consts (constants) PLUS absorbed; free_axis picks the free var:
         free_axis in 0..t-2  -> free a rate input cell, v fixed to v_const
         free_axis == 'v'     -> free the capacity v, rate inputs fixed
       'fixed_rate' supplies the t-1 incoming rate-cell values (post block1+absorb),
       only the chosen free one is overridden by z.
       Returns univariate s2[1] (= s2[0]) polynomial."""
    Su = PolynomialRing(Fp, 'z'); z = Su.gen()
    if free_axis == 'v':
        rate = [Su(fixed_rate[j]) for j in range(t-1)]
        cap  = z
    else:
        rate = [ (z if j==free_axis else Su(fixed_rate[j])) for j in range(t-1) ]
        cap  = Su(v_const)
    state = rate + [cap]
    out = perm(state, RC2, phi, t, n)
    return out[0]

# ---------------------------------------------------------------------------
# Cell runner
# ---------------------------------------------------------------------------

def run_cell(t, n, p, seed=1, verbose=True, label=""):
    Fp = GF(p)
    phi = Fp(7)
    RC1 = make_RC(Fp, t, n, seed)
    RC2 = make_RC(Fp, t, n, seed+1000)   # distinct constants per block
    set_random_seed(seed)
    consts1 = [Fp.random_element() for _ in range(t-1)]   # block-1 fixed rate inputs
    fixed_rate2 = [Fp.random_element() for _ in range(t-1)]  # block-2 fixed rate (post-absorb)
    v_const = Fp.random_element()                          # a generic chaining value
    m2_consts = [Fp.random_element() for _ in range(t-1)]

    naive = t*(n-1)
    Deff_exp = t*(n-2)+2

    # --- B0: single-block D_eff (calibration) ---
    sb_deg, sb_var, sb_all = single_block_best(t, n, Fp, RC1, phi, consts1)
    sb_exp = log(sb_deg,2) if sb_deg>0 else 0

    # --- B1: block-2 map in its best free RATE var, with v fixed to a generic
    #         constant (the honest sponge: attacker varies one input of block 2,
    #         v determined upstream but treated as a generic value here). ---
    b2_rate_degs = []
    for fa in range(t-1):
        u = block2_with_chosen_v(t, n, Fp, RC2, phi, fa, fixed_rate2, v_const, m2_consts)
        b2_rate_degs.append(u.degree())
    b2_rate_best = min(b2_rate_degs)
    b2_rate_arg  = min(range(t-1), key=lambda j: b2_rate_degs[j])

    # --- B2/B3: STRONG model. Free the capacity v itself in block 2. ---
    u_v = block2_with_chosen_v(t, n, Fp, RC2, phi, 'v', fixed_rate2, v_const, m2_consts)
    v_axis_deg = u_v.degree()

    # adversarial: best over {all rate axes} U {v axis}
    strong_best = min(b2_rate_best, v_axis_deg)
    strong_arg  = ('v' if v_axis_deg <= b2_rate_best else 'x%d'%(b2_rate_arg+1))

    # --- block-1 inversion stage: degree of v = s1[t](m1) in its best m1 axis ---
    b1_cap_degs = []
    for jfree in range(t-1):
        out = block1_chaining_poly(t, n, Fp, RC1, phi, jfree, consts1)
        b1_cap_degs.append(out[t-1].degree())   # capacity cell degree
    b1_cap_best = min(b1_cap_degs)
    b1_cap_arg  = min(range(t-1), key=lambda j: b1_cap_degs[j])

    res = dict(t=t, n=n, p=p, seed=seed, label=label,
               naive_exp=naive, Deff_exp=Deff_exp,
               single_block_deg=int(sb_deg), single_block_exp=float(sb_exp),
               single_block_var=sb_var+1,
               b2_rate_best=int(b2_rate_best), b2_rate_arg=b2_rate_arg+1,
               b2_rate_all=[int(x) for x in b2_rate_degs],
               v_axis_deg=int(v_axis_deg),
               strong_best=int(strong_best), strong_arg=strong_arg,
               b1_cap_best=int(b1_cap_best), b1_cap_arg=b1_cap_arg+1,
               b1_cap_all=[int(x) for x in b1_cap_degs])

    if verbose:
        e = lambda d: ("2^%g"%float(log(d,2)) if d>0 else "1")
        print("=== t=%d n=%d p=%d seed=%d %s ===" % (t,n,p,seed,label))
        print("  naive D_I exp = %d ; predicted single-block D_eff exp = %d (2^%d)"
              % (naive, Deff_exp, Deff_exp))
        print("  [B0] single-block best: free x%d  deg=%d (%s)  all=%s"
              % (sb_var, sb_deg, e(sb_deg), sb_all))
        print("  [B1] block-2 best RATE axis: free x%d  deg=%d (%s)  all=%s"
              % (b2_rate_arg+1, b2_rate_best, e(b2_rate_best), b2_rate_degs))
        print("  [B2] block-2 free CHAINING v: deg=%d (%s)" % (v_axis_deg, e(v_axis_deg)))
        print("  [B3] STRONG adversarial best axis = %s, deg=%d (%s)"
              % (strong_arg, strong_best, e(strong_best)))
        print("  block-1 inversion v=s1[t](m1): best free x%d  deg=%d (%s)  all=%s"
              % (b1_cap_arg+1, b1_cap_best, e(b1_cap_best), b1_cap_degs))
        # bits-lost comparisons
        bl_strong = (Deff_exp - float(log(strong_best,2))) if strong_best>0 else Deff_exp
        print("  >> bits below single-block D_eff (strong best): %g" % bl_strong)
        print()
    return res

# ---------------------------------------------------------------------------

if __name__ == '__main__':
    T0 = time.time()
    p = 65521          # 16-bit prime, matches the within-block study
    results = []
    # keep cells TINY: two blocks => block-2 univariate degree can reach the
    # single-block total degree 2^{t(n-1)}; cap that exponent at 14.
    grid = []
    for t in [2,3]:
        for n in [2,3]:
            if t*(n-1) > 14:
                continue
            grid.append((t,n))

    print("######## SEED 1 ########")
    for (t,n) in grid:
        results.append(run_cell(t,n,p,seed=1))

    print("######## SEED 2 ########")
    for (t,n) in grid:
        run_cell(t,n,p,seed=2)

    # BN254 spot-check on the smallest cell
    print("######## BN254 SPOT-CHECK (t=2 n=2, t=3 n=2) ########")
    run_cell(2,2,BN254,seed=1,label="BN254")
    run_cell(3,2,BN254,seed=1,label="BN254")

    print("\n==== SUMMARY (p=%d) ====" % p)
    print("t n | D_eff_exp | B0_exp | B1(rate)_exp | B2(v)_exp | STRONG_best_exp | bits_below_Deff")
    for r in results:
        ee = lambda d: float(log(d,2)) if d>0 else 0.0
        bl = r['Deff_exp'] - ee(r['strong_best'])
        print("%d %d |    %2d     |  %4.1f  |    %4.1f      |   %4.1f    |     %4.1f        |   %+.1f"
              % (r['t'], r['n'], r['Deff_exp'], ee(r['single_block_deg']),
                 ee(r['b2_rate_best']), ee(r['v_axis_deg']),
                 ee(r['strong_best']), bl))
    print("\nelapsed %.1fs" % (time.time()-T0))
