#!/usr/bin/env sage
"""Module 2 done right — on the paper's actual ideal formulation.

Generators (m = 2n+2):
  g_1 = t_0                                   (linear)
  g_2 = t_n - target                          (linear)
  g_{3+2i} = t_{i+1} - PHI*t_i - s_i^2 - c_i  (quadratic)  i=0..n-1
  g_{4+2i} = s_{i+1} - PHI*s_i - t_{i+1}^2 - d_i (quadratic)  i=0..n-1

We compute syz(I), bucket by weighted degree (deg(a_i) + deg(g_i)),
compare against Koszul-pair count at each degree, and identify any
excess as candidate non-generic syzygies.

Observed HS numerator is (1+z)^{2n-1}, exactly ONE FACTOR SHORT of
the semi-regular (1+z)^{2n}. So one non-trivial syzygy must live
in the structure."""
from sage.all import *
from sage.libs.singular.function import singular_function
import hashlib
import time

BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
PHI = 7


def rc(seed, n):
    return [int.from_bytes(hashlib.sha256(f'{seed}_{i}'.encode()).digest(), 'big') % BN254
            for i in range(n)]


def forward_simulate(n, c, d, psi_0):
    theta, psi = 0, psi_0
    for i in range(n):
        theta = (PHI * theta + psi * psi + c[i]) % BN254
        psi = (PHI * psi + theta * theta + d[i]) % BN254
    return theta


def build_paper_ideal(n):
    c = rc('mambo_bn254_c', n)
    d = rc('mambo_bn254_d', n)
    psi_0 = 12345678901234567890
    target = forward_simulate(n, c, d, psi_0)

    names = [f't{i}' for i in range(n+1)] + [f's{i}' for i in range(n+1)]
    R = PolynomialRing(QQ, names, order='degrevlex')
    g = R.gens()
    tvars = [g[i] for i in range(n+1)]
    svars = [g[n+1+i] for i in range(n+1)]

    eqs = []
    eqs.append(tvars[0])                       # t_0 = 0
    eqs.append(tvars[n] - target)              # t_n = target
    for i in range(n):
        eqs.append(tvars[i+1] - PHI*tvars[i] - svars[i]**2 - c[i])
        eqs.append(svars[i+1] - PHI*svars[i] - tvars[i+1]**2 - d[i])

    return R.ideal(eqs), R, eqs


def wdeg(sz, eqs):
    degs = [a.degree() + f.degree() for a, f in zip(sz, eqs) if a != 0]
    return max(degs) if degs else -1


def run_n(n):
    print(f"\n{'='*70}")
    print(f"n = {n}")
    print('='*70)

    I, R, eqs = build_paper_ideal(n)
    m = len(eqs)
    print(f"  vars: {R.ngens()}   gens: {m}")
    gen_degs = [f.degree() for f in eqs]
    print(f"  gen degrees: {gen_degs}")

    syz = singular_function('syz')
    t0 = time.time()
    M = syz(I)
    print(f"  syz(I)    {time.time()-t0:6.2f}s   total generators: {len(M)}")

    # Bucket by weighted degree
    by_deg = {}
    for sz in M:
        sz_list = [R(x) for x in sz]
        d = wdeg(sz_list, eqs)
        by_deg.setdefault(d, []).append(sz_list)

    print(f"\n  syz(I) by weighted degree:")
    for dd in sorted(by_deg):
        print(f"    deg {dd:>3}: {len(by_deg[dd])} gens")

    # Koszul expected count per weighted degree
    # For each pair (i, j), weighted deg = deg(f_i) + deg(f_j)
    kos_by_deg = {}
    for i in range(m):
        for j in range(i+1, m):
            d = gen_degs[i] + gen_degs[j]
            kos_by_deg[d] = kos_by_deg.get(d, 0) + 1
    print(f"\n  Koszul pair count by weighted degree:")
    for dd in sorted(kos_by_deg):
        print(f"    deg {dd:>3}: {kos_by_deg[dd]} pairs")

    # Comparison
    print(f"\n  syz vs koszul (excess indicates non-generic syzygies):")
    all_degs = sorted(set(by_deg) | set(kos_by_deg))
    for dd in all_degs:
        so = len(by_deg.get(dd, []))
        ko = kos_by_deg.get(dd, 0)
        print(f"    deg {dd:>3}: syz={so:>4}  koszul={ko:>4}  "
              f"excess={so-ko:+4d}")

    # Print low-degree (most likely non-generic) syzygy representatives
    # Ignoring pure Koszul: if syz has generators at a degree where Koszul
    # has fewer, the extras are candidates.
    print(f"\n  Candidate non-generic syzygy reps (first at each excess degree):")
    for dd in all_degs:
        so = len(by_deg.get(dd, []))
        ko = kos_by_deg.get(dd, 0)
        if so > 0 and so != ko:
            # Print the first syzygy at this degree
            sz = by_deg[dd][0]
            print(f"\n    deg {dd} (excess {so-ko:+d}):")
            for i, a in enumerate(sz):
                if a != 0:
                    s = str(a)
                    if len(s) > 80:
                        s = s[:77] + '...'
                    print(f"      a_{i:>2} = {s}")


if __name__ == '__main__':
    for n in [2, 3, 4, 5]:
        run_n(n)
