p = 2147483647
F = GF(p); R.<x> = PolynomialRing(F)
import sys
sys.path.insert(0,'/tmp')
# inline the tester
def is_decomposable(f):
    D = f.degree(); f = f.monic()
    for s in divisors(D):
        if s == 1 or s == D: continue
        r = D // s
        frev = R(list(reversed(f.list())))
        S.<T> = PowerSeriesRing(F, default_prec=s+1)
        try: hrev_ser = S(frev.list()[:s+1]).nth_root(r)
        except (ValueError, ArithmeticError): continue
        h = R(list(reversed(hrev_ser.padded_list(s+1))))
        if h.degree() != s: continue
        g, digits = f, []
        while g != 0:
            g, rem = g.quo_rem(h); digits.append(rem)
        if all(d.degree() <= 0 for d in digits): return True, s
    return False, None
set_random_seed(1)
g = R.random_element(8).monic(); h = R.random_element(8).monic()
print("planted g(h):", is_decomposable(g(h)))   # expect True, 8
print("random deg64:", is_decomposable(R.random_element(64).monic()))  # expect False
print("planted x^4 comp:", is_decomposable((x^4+3*x+1)(x^4+5)))  # expect True
