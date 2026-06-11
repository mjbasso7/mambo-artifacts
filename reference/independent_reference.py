#!/usr/bin/env python3
"""
Independent Mambo reference — second implementation to cross-check the primary.
==============================================================================

Purpose: the primary Python reference in `reference/test_vectors.py` is the
single point of comparison for cross-implementation parity. If that file is
wrong — say, a bug in operator precedence, or an off-by-one in RC indexing
— every Rust/C++ implementation validated against it would inherit the
same bug.

This file provides a SECOND Python reference, derived from the paper's
equations with deliberately different:

  * field arithmetic library  — uses sympy's GF() wrapper, not % p
  * control flow             — uses functools.reduce, not for-loops
  * state representation     — uses @dataclass State instead of tuples
  * round-constant iteration — uses itertools.islice on a generator
  * variable naming          — different throughout

If this file produces bit-identical outputs to `test_vectors.py` on all 16
cross-impl KATs, the probability that both have the same bug drops
substantially: two implementations using different libraries and different
structural idioms would have to share a semantic mistake at the formula
level, not a code-level copy-paste mistake.

Running:
    python3 independent_reference.py
Exits 0 if all 16 KATs match, 1 if any diverge.
"""

from dataclasses import dataclass
from functools import reduce
from hashlib import sha256
from itertools import islice

import sympy


# ---------------------------------------------------------------------------
# Field layer — sympy-backed
# ---------------------------------------------------------------------------

def make_gf(p: int):
    """Build a sympy GF field and a lift function to integers."""
    F = sympy.GF(p)

    def lift(x):
        return int(F(x))

    return F, lift


# ---------------------------------------------------------------------------
# Round constants — re-derived from scratch, independent of test_vectors.py
# ---------------------------------------------------------------------------

def rc_generator(seed: bytes, p: int):
    """
    Infinite generator of round-constant integers mod p.

    Derivation:
        r_j = SHA256(seed || BE32(j))  as int, mod p
        if r_j == 0: yield 1 else yield r_j
    """
    j = 0
    while True:
        digest = sha256(seed + j.to_bytes(4, byteorder="big", signed=False)).digest()
        raw = int.from_bytes(digest, byteorder="big", signed=False)
        v = raw % p
        yield 1 if v == 0 else v
        j += 1


def take(iterable, n):
    """Return first n items from iterable (like itertools.take)."""
    return list(islice(iterable, n))


def derive_rcs(n_rounds: int, p: int, seed: bytes = b"Mambo_round_constants"):
    """
    Return (cs, ds) = (first n_rounds RC, second n_rounds RC).

    Matches the layout of `test_vectors.py::generate_round_constants`
    but reaches it by generator/itertools instead of list-comprehension.
    """
    gen = rc_generator(seed, p)
    both = take(gen, 2 * n_rounds)
    # Paper convention: first half is c, second half is d.
    cs = both[:n_rounds]
    ds = both[n_rounds:]
    return cs, ds


# ---------------------------------------------------------------------------
# State + step — dataclass + reduce, no explicit loop
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class State:
    theta: int
    psi: int


def t2_step(state: State, rc_pair, phi: int, F, lift) -> State:
    """
    One Mambo t=2 step using sympy field ops. Uses the field F directly for
    all arithmetic, lifts to int only at the end — intentionally different
    from the primary reference which uses Python ints with `% p` at every
    step.
    """
    c, d = rc_pair
    t = F(state.theta)
    p_ = F(state.psi)
    phi_f = F(phi)
    theta_next = phi_f * t + p_ * p_ + F(c)
    psi_next = phi_f * p_ + theta_next * theta_next + F(d)
    return State(lift(theta_next), lift(psi_next))


def mambo_t2_run(theta0: int, psi0: int, phi: int, p: int, n: int) -> State:
    """
    Apply n Mambo t=2 steps using sympy field arithmetic and functools.reduce.
    """
    # Canonical derive-fresh: 2n constants for an n-round permutation, d-offset=n.
    cs, ds = derive_rcs(n, p)
    F, lift = make_gf(p)
    state = State(theta0 % p, psi0 % p)
    rc_pairs = list(zip(cs[:n], ds[:n]))
    return reduce(
        lambda s, cd: t2_step(s, cd, phi, F, lift),
        rc_pairs,
        state,
    )


# ---------------------------------------------------------------------------
# t=4 step — chained update in sympy field
# ---------------------------------------------------------------------------

def t4_step(state4, rc4, phi, F, lift):
    """
    One t=4 Mambo step:
        new[0] = phi * old[0] + old[3]^2 + rc[0]
        new[1] = phi * old[1] + new[0]^2 + rc[1]
        new[2] = phi * old[2] + new[1]^2 + rc[2]
        new[3] = phi * old[3] + new[2]^2 + rc[3]
    Implemented with sympy field F.
    """
    s = [F(x) for x in state4]
    phi_f = F(phi)
    rc = [F(r) for r in rc4]
    n0 = phi_f * s[0] + s[3] * s[3] + rc[0]
    n1 = phi_f * s[1] + n0 * n0 + rc[1]
    n2 = phi_f * s[2] + n1 * n1 + rc[2]
    n3 = phi_f * s[3] + n2 * n2 + rc[3]
    return (lift(n0), lift(n1), lift(n2), lift(n3))


def mambo_t3_run(x1, x2, x3, phi, p, n, max_n=50):
    """
    t=3 reference over BN254 scalar field. Canonical layout: RC seed
    `b'Mambo_t3_round_constants'`, flat 150-element list, round-constants
    cycle over max_n=50.
    """
    rc_flat = take(rc_generator(b"Mambo_t3_round_constants", p), max_n * 3)
    F, lift = make_gf(p)
    state = (x1 % p, x2 % p, x3 % p)
    for i in range(n):
        idx_base = (i % max_n) * 3
        s = [F(x) for x in state]
        phi_f = F(phi)
        rc = [F(rc_flat[idx_base + j]) for j in range(3)]
        n0 = phi_f * s[0] + s[2] * s[2] + rc[0]
        n1 = phi_f * s[1] + n0 * n0 + rc[1]
        n2 = phi_f * s[2] + n1 * n1 + rc[2]
        state = (lift(n0), lift(n1), lift(n2))
    return state


def mambo_t4_run(x1, x2, x3, x4, phi, p, n, max_n=50):
    """
    t=4 reference over BN254 scalar field. Canonical layout:
    round-constants cycle over max_n=50.

    Note: t=4 uses a DIFFERENT RC-derivation seed than t=2 — specifically
    `b'Mambo_t4_round_constants'` (embedded `_t4_`), not
    `b'Mambo_round_constants'`.
    """
    rc_flat = take(rc_generator(b"Mambo_t4_round_constants", p), max_n * 4)
    # The t=4 RC table is a flat 200-element array; this reference re-derives
    # the same flat list, consumed as rc_flat[idx_base + {0..3}].
    F, lift = make_gf(p)
    state = (x1 % p, x2 % p, x3 % p, x4 % p)
    for i in range(n):
        idx_base = (i % max_n) * 4
        rc4 = (
            rc_flat[idx_base + 0],
            rc_flat[idx_base + 1],
            rc_flat[idx_base + 2],
            rc_flat[idx_base + 3],
        )
        state = t4_step(state, rc4, phi, F, lift)
    return state


# ---------------------------------------------------------------------------
# Comparison
# ---------------------------------------------------------------------------

BABYBEAR = 2**31 - 2**27 + 1
KOALABEAR = 2**31 - 2**24 + 1
BN254_FR = (
    21888242871839275222246405745257275088548364400416034343698204186575808495617
)

# BabyBear + KoalaBear t=2 KATs (canonical cross-implementation parity values)
BABYBEAR_KAT = [
    ("bb_t11_n18", 1, 1, 18, 1755000363, 1759250641),
    ("bb_arb_n33", 42, 137, 33, 1515376625, 1547513848),
    ("bb_arb_n65", 7, 11, 65, 366476442, 419740958),
]
KOALABEAR_KAT = [
    ("kb_t11_n18", 1, 1, 18, 105231457, 2055397737),
    ("kb_arb_n33", 42, 137, 33, 1942036357, 1417288425),
    ("kb_arb_n65", 7, 11, 65, 176626013, 1368808091),
]

# BN254 t=2 sponge KATs (canonical cross-implementation parity values for the
# 2-to-1 sponge). Sponge is 2-to-1 compression: H(m1, m2) = sponge_run(...)
# Format: (label, m1, m2, n, expected_theta, expected_psi)
# n=65 is the t=2 analysis-minimum / falsification-target cell. The recommended
# t=2 L1 deployment cell is n=82 (+25% margin). Canonical RC scheme is
# DERIVE-FRESH: an n-round permutation uses 2n fresh constants with d-offset=n
# (matches test_vectors.py). The in-circuit backends embed the derive-fresh
# table at the deployed n=82 cell; the legacy cycle-mod-65 with d-offset pinned
# to 65 coincided with derive-fresh only at exactly n=65.
SPONGE_KAT = [
    (
        "sponge_42_99_n65_min", 42, 99, 65,
        19683959081911025011706499332490938909405624445008367474487759325889985246881,
        13124149393838541721819082498789535294026283524720053701796687479290775239073,
    ),
    (
        "sponge_1_2_n65_min", 1, 2, 65,
        12855502813967808571856733968993265090047814806502131727288372177009695896921,
        10644358959610209771819347017990018779919812218253447993508349086038662179500,
    ),
]


def sponge_run(m1: int, m2: int, phi: int, p: int, n: int) -> State:
    """
    2-to-1 sponge compression:
      1. state = (m1, 0), permute n rounds → (theta1, psi1)
      2. state = (theta1 + m2, psi1), permute n rounds → (theta2, psi2)
      3. Output = (theta2, psi2)   [caller picks theta2 as the hash digest]

    Implements the canonical 2-to-1 sponge reference.
    """
    s1 = mambo_t2_run(m1, 0, phi, p, n)
    s2 = mambo_t2_run((s1.theta + m2) % p, s1.psi, phi, p, n)
    return s2


# BN254 t=3 KATs. n=55 is the recommended t=3 L1 deployment cell (+25% margin
# over the analysis-minimum cell n=44, where D_eff = 2^{3(n-1)-1} hits exactly
# 2^128); n=44 is that analysis-minimum / falsification-target cell and n=23
# the legacy FGLM-model research cell. RC cycle modulo the 50-entry table
# (matches mambo_t3_run max_n=50). Cross-checked against
# test/parity_vectors_bn254.json.
T3_KAT = [
    (
        "t3_n23_legacy",
        1, 1, 1, 23,
        11465960142887527216035340931699114626296198667795243583025105104764276505274,
        18704652440336640413025333157902945319866834460721733307931743972886313839721,
        3206858878025623961458653268498071822526451023406693205699363884915614895271,
    ),
    (
        "t3_n44_min",
        1, 1, 1, 44,
        12112684701175969467927093102787629300174523989703863772921217917646592614098,
        2100341269655051437293315357895921523800042228274592834178051380259571692847,
        9048906347859481940878020393034454712120670368422004698122728665895961706132,
    ),
    (
        "t3_n55_recommended",
        1, 1, 1, 55,
        11855794307609730773213059738302274123974433528587131742461132180818394299649,
        14631224765672410140753936815791983239768294679486136768554282611482822152372,
        6565080835519303174468743686919759887497723356591112206372330946713567733560,
    ),
]


# BN254 t=4 KATs (canonical cross-implementation parity values). n=44 is the recommended
# t=4 L1 deployment cell (+25% margin over the analysis-minimum n=34, where
# D_eff hits exactly 2^128; recommended floor n=43 rounded to 44 for packing
# alignment). n=34 is the analysis-minimum / falsification-target cell and
# n=18/n=33 are legacy FGLM-model research configurations. RC cycle modulo the
# 50-entry table.
T4_KAT = [
    (
        "t4_n44_recommended",
        1, 1, 1, 1, 44,
        14359910018053810871964566132425843355142161853528005630650394261756664499444,
        606696360151698791938533405885100762200340503758100156580860516672905051457,
        14532477509020994362539253778942467674162865890764754244297525746450410275769,
        5826113374530391994295285145349936908729364954251899339224022948306185799918,
    ),
    (
        "t4_n18_legacy",
        1, 2, 3, 4, 18,
        3281837389505770905802288579040767160867800700514464786734992712930764405610,
        20973871303391136528432684583495217955969071614196524032642438718523145990257,
        21674965019994845851918181121832588988494784602781856065664061864375669221410,
        13236999028131734600377093394482671492670234746743572752732435528506641628843,
    ),
    (
        "t4_mixed_n18_legacy",
        42, 137, 99, 7, 18,
        9129892924393177618811613712477274750365421966373307124658953873825336152924,
        7129817150127690781383194753016615401162480968799942738298392984290118882687,
        19225371996123924968203782832401250511768014364744686873196865771398342407094,
        2837677261745767162819784957884147428492356232022958118947373333450014646061,
    ),
    (
        "t4_sparse_n18_legacy",
        0, 0, 0, 1, 18,
        19430780234722860493907059783027733422924580659153701753656796350173171856433,
        1927819661602278431532760401646072639946127655282801741832669740274774535091,
        12307255204765138350762500333640439632046166350859130712095228356581138724168,
        1051893360545450911823115211014108665122585017944112759717769607307505897701,
    ),
    (
        "t4_n33_legacy",
        1, 2, 3, 4, 33,
        2049820081367886646486713350166535972292842507258997701380866003493034377659,
        14401905739674827153146370866131861888225582377697134211568595738292788266078,
        11723583681953460055911760743056417998572026857622612878148791785293407923743,
        3318979042729882230564324216929446723581697875423150918615056748803558209431,
    ),
    (
        "t4_n34_min",
        1, 1, 1, 1, 34,
        15158418665952842636549165003513983974577253410463430344889389254036807376710,
        3068093614493540858079883048271805206392642819679866016644902476596957190733,
        11164504969482773846007243156426618402463036576351390466650715794962802166773,
        8517034224721970857636637660945226580583189796353707857355427943504563519391,
    ),
]


def main():
    PHI = 7
    total = 0
    passed = 0
    failed = []

    print("=" * 72)
    print("Independent Mambo reference — bit-identity check against primary ref")
    print("=" * 72)

    # BabyBear
    for label, t0, p0, n, exp_t, exp_p in BABYBEAR_KAT:
        out = mambo_t2_run(t0, p0, PHI, BABYBEAR, n)
        ok = out.theta == exp_t and out.psi == exp_p
        total += 1
        if ok:
            passed += 1
            print(f"  [OK] {label}  theta={out.theta}  psi={out.psi}")
        else:
            failed.append(label)
            print(f"  [FAIL] {label}")
            print(f"         got:  theta={out.theta}  psi={out.psi}")
            print(f"         exp:  theta={exp_t}  psi={exp_p}")

    # KoalaBear
    for label, t0, p0, n, exp_t, exp_p in KOALABEAR_KAT:
        out = mambo_t2_run(t0, p0, PHI, KOALABEAR, n)
        ok = out.theta == exp_t and out.psi == exp_p
        total += 1
        if ok:
            passed += 1
            print(f"  [OK] {label}  theta={out.theta}  psi={out.psi}")
        else:
            failed.append(label)
            print(f"  [FAIL] {label}")
            print(f"         got:  theta={out.theta}  psi={out.psi}")
            print(f"         exp:  theta={exp_t}  psi={exp_p}")

    # BN254 sponge
    for label, m1, m2, n, exp_t, exp_p in SPONGE_KAT:
        out = sponge_run(m1, m2, PHI, BN254_FR, n)
        ok = out.theta == exp_t and out.psi == exp_p
        total += 1
        if ok:
            passed += 1
            print(f"  [OK] {label}  theta={out.theta}")
        else:
            failed.append(label)
            print(f"  [FAIL] {label}")
            print(f"         got:  theta={out.theta}  psi={out.psi}")
            print(f"         exp:  theta={exp_t}  psi={exp_p}")

    # t=3 BN254
    for label, x1, x2, x3, n, e1, e2, e3 in T3_KAT:
        o1, o2, o3 = mambo_t3_run(x1, x2, x3, PHI, BN254_FR, n)
        ok = (o1, o2, o3) == (e1, e2, e3)
        total += 1
        if ok:
            passed += 1
            print(f"  [OK] {label}")
        else:
            failed.append(label)
            print(f"  [FAIL] {label}")
            print(f"         got: {(o1, o2, o3)}")
            print(f"         exp: {(e1, e2, e3)}")

    # t=4 BN254
    for label, x1, x2, x3, x4, n, e1, e2, e3, e4 in T4_KAT:
        o1, o2, o3, o4 = mambo_t4_run(x1, x2, x3, x4, PHI, BN254_FR, n)
        ok = (o1, o2, o3, o4) == (e1, e2, e3, e4)
        total += 1
        if ok:
            passed += 1
            print(f"  [OK] {label}")
        else:
            failed.append(label)
            print(f"  [FAIL] {label}")
            print(f"         got: {(o1, o2, o3, o4)}")
            print(f"         exp: {(e1, e2, e3, e4)}")

    print("=" * 72)
    print(f"Total: {passed}/{total}  —  {'ALL PASS' if passed == total else 'FAILURES: ' + ', '.join(failed)}")
    print("=" * 72)

    import sys
    sys.exit(0 if passed == total else 1)


if __name__ == "__main__":
    main()
