# Mambo Proof Gaps: Status and Approaches

## 1. t>=3 Closed-Form Groebner Basis (Structural Proof)

### Status
- **t=2 (Appendix G)**: Proven in full -- FreeLunch system, explicit pairwise-coprime LMs, Boolean ring.
- **t=3 (empirical)**: Verified n=2..5 -- HS = (1+z)^{3n-2}, dim = 2^{3n-2}, dreg = 3n-1.
  Boolean ring structure confirmed despite non-pairwise-coprime LMs in the tail.
- **t=4 (empirical)**: Verified n=2..4 -- HS != (1+z)^{4n-3} for n>=3. Has Q4 correction.
  dim = 2^{4n-3} still holds (no collapse), but dreg = 4n-3 (lower than 4n-1).
- **t>=5**: Unknown -- suspected Q4 corrections compound.

### t=3 Proof Strategy
The tail triple `(x_{n-1,3}, x_{n,2}, x_{n,3})` constrains via interaction LMs:
- `x_{n-1,3}*x_{n,2}` (deg 2): no simultaneous presence
- `x_{n-1,3}*x_{n,3}^2` (deg 3): x_n_3^2 requires x_{n-1,3}=0
- `x_{n,2}*x_{n,3}^2` (deg 3): x_n_3^2 requires x_{n,2}=0
- `x_{n,3}^4` (deg 4): power <= 3

Tail state count = 8 = 2^3 (same as 3 independent Boolean vars).

Interior free vars (all others) have direct square LMs, power <= 1.
3n-4 interior vars x tail's 3 vars = 3n-2 variables, each Boolean.
Total: 2^{3n-2}. HS: (1+z)^{3n-2}. dreg = 3n-1.

**Writeup needed**: A lemma showing the 4 tail LMs generate the full
monomial ideal of the tail variables, followed by the free/fixed
variable decomposition. Then the t=3 case reduces to the same
counting as t=2.

### t>=4 Challenge
t=4 shows Q4 correction (Hilbert series != pure Boolean for n>=3).
The deeper cascade produces more tail interactions. This may require
a different approach -- possibly showing that dreg = tn - 3(n-1)
or similar, rather than a full Boolean ring.

---

## 2. Multi-Block CICO Proof

### Status
- "Open" in the security table (Section 11)
- Empirically checked at (t,n) in {(2,2),(2,3),(3,2),(3,3)} plus BN254 spot-check
- Finding: two-block effective degree = single-block D_eff = 2^{t(n-2)+2}
- No gain beyond per-block (t-2) bits

### The Gap
The paper states (line 2754-2758):
> "A general-(t,n) proof -- the degree-tracking argument of
> Proposition 6.3 applied to a nonzero incoming capacity --
> remains open."

The chaining value occupies the capacity cell (last position in the
squaring cascade). When the attacker chooses it, the second block's
capacity is a free parameter, entering at the deepest point.

### Why This Is Tricky
A free variable at capacity-position (last cascade) gives a HIGHER
eliminant degree than at rate-position (first cascade). Specifically:
- Single-block: 1 free rate var produces D_eff = 2^{t(n-1)-(t-2)}
- Second block: 1 free capacity var produces degree 2^{t(n-1)-1} > D_eff

But the attacker has TWO free variables across both blocks, plus the
chaining value connects them. The concern: Can the attacker exploit
the joint freedom to amortize the root-finding cost?

### Proof Sketch
1. Model 2-block system as a single algebraic system with 2n rounds
   and a shared (free) intermediate state variable.
2. Apply the degree vector (Lemma 6.1) to the joint 2n-round cascade.
   The chaining variable at position t acts as a parameter at round n.
3. Lemma 6.2 (no leading-coefficient cancellation) applies at every
   specialization -- the leading coefficient is phi^{deg} != 0.
4. The minimal joint degree occurs when the attacker frees exactly
   1 parameter in each block (the rate-1 cell in both blocks). But
   the chaining value is already free -- if it's the only extra degree
   of freedom, the joint degree is a single-block degree + chaining term.
5. Key: no syzygy connects the two block's cascade paths because
   the chaining value enters as a parameter at round n, and the
   degree-tracking separates the blocks' contributions additively.
6. Therefore total degree per block >= D_eff, and the attacker solves
   each block independently -- total cost >= 2 * single-block cost.

### What's Needed
- Formalize the degree-tracking for a 2n-round system with
  a free intermediate parameter at position t
- Show the joint eliminant degree = D_eff(block1) + D_eff(block2)
  (additive, not sub-additive)
- Generalize to m-block absorption by induction

---

## 3. Functional Indecomposability of theta_n

### Status
- Proven for outer degree <= 4 or inner degree 2 (unconditionally)
- Verified for remaining splits up to n=6 with production constants
- Full symmetric monodromy (S_{D_I}) certified for n=3..6
- The general case reduces to indecomposability hypothesis

### Why This Matters
If theta_n were decomposable as g.h, the attacker could solve the
eliminant f_n(x) = theta_n(x) - tau in two lower-degree stages:
- Find y s.t. g(y) = tau (degree deg(g))
- Find x s.t. h(x) = y (degree deg(h))
Total cost: O~(deg(g) + deg(h)) instead of O~(deg(g)*deg(h)).
This would beat the CICO security floor.

### Proof Approach (for the remaining cases)
- At tame total ramification at infinity, theta_n has a regular D_I-cycle
- By Schur's theorem, the Galois group is primitive
- The classification of primitive groups with a regular cyclic
  subgroup (Jones 2002) limits possibilities to:
  - A_n <= G <= S_n (full alternating/symmetric)
  - PGL_d(q) in specific embeddings
  - Some exceptional cases
- The degree is D_I = 2^{tn-(t-2)} at t=2 (or more generally)
- For t=2, D_I = 2^{2n-2}, an elementary arithmetic lemma excludes
  the projective-linear cases
- The remaining possibilities force full symmetric group S_{D_I}
- This holds exactly when theta_n is indecomposable (the block system
  of a decomposition corresponds to a system of imprimitivity)

### What's Needed
- Extend the outer-degree-4 proof to higher outer degrees via
  the cascade structure of theta_n (each round's composition with
  the next prevents low-degree outer decomposition)
- Alternatively, show that the nonzero coefficients of theta_n at
  all degrees from 1 to D_I-1 (a verified property up to n=6)
  prevents decomposability for all n

---

## 4. The 25% Margin Arbitrariness

### Status
- Paper uses 25% margin: n_rec = 82 vs n_min = 65
- Described as "conservative" but not derived from a formal model
- No rigorous argument that 25% covers all attack vectors

### What Would Be Needed
- A formal security model with parameterized attack surfaces
- A quantitative evaluation of each attack vector's scaling
- A derived margin formula based on model risk, not convention
- This is more of an engineering question than a math gap
