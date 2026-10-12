# Mambo-t3: Correct Structural Groebner Basis Analysis

## Correct Round Function (Section 9, mambo_tosc_2026.tex:3424-3428)

For Mambo-t with state width t:
```
x_1' = phi*x_1 + x_t^2 + c_{r,1}
x_i' = phi*x_i + (x_{i-1}')^2 + c_{r,i}  for i = 2, ..., t
```

Key: cell 1 wraps from cell t (the LAST cell of the previous round).
Each subsequent cell feeds from the NEW output of the previous cell.

## CICO Convention (rate=1, capacity=t-1)

- Capacity cells = positions 1..t-1 (fixed to 0 at input)
- Rate cell = position t (free at input)
- Output: position 1 = tau (fixed), positions 2..t = free

For t=3: capacity = positions 1,2 (cells x_{0,1}, x_{0,2}), rate = position 3 (x_{0,3})
For t=4: capacity = positions 1,2,3, rate = position 4

## Verified Properties (correct round function)

For the rate-1 CICO ideal with the correct round function:

| t | n | dim(R/I) | expected 2^{tn-(t-1)} | match | linear LMs | free vars |
|---|----|----------|----------------------|-------|------------|-----------|
| 3 | 2  | 16       | 2^4 = 16             | YES   | 5          | 4 = 3n-2  |
| 3 | 3  | 128      | 2^7 = 128            | YES   | 5          | 7 = 3n-2  |
| 3 | 4  | 1024     | 2^10 = 1024          | YES   | 5          | 10 = 3n-2 |
| 4 | 2  | 32       | 2^5 = 32             | YES   | 6          | 5 = 4n-3  |
| 4 | 3  | 512      | 2^9 = 512            | YES   | 6          | 9 = 4n-3  |

## Fixed Variables (Linear LMs)

t=3: {x_{0,1}, x_{0,2}, x_{n-2,3}, x_{n-1,2}, x_{n,1}} = 5 = 2t-1
t=4: {x_{0,1}, x_{0,2}, x_{0,3}, x_{n-2,4}, x_{n-1,3}, x_{n,1}} = 6 = 2t-2

## Free Variable Structure for t=3

The standard monomials are NOT pure squarefree monomials (some variables
appear with power > 1 in the normal basis), but the TOTAL COUNT equals
2^{3n-2} through interaction constraints that compensate.

### Partition of Free Variables

A. Interior free vars (3n-5 of them): each has a direct square LM -> power <= 1
   - x_{i,3} for i = 0..n-2 (from round eq: x_{i+1,1} = phi*x_{i,1} + x_{i,3}^2 + c)
   - x_{i,1} for i = 1..n-1 (from round eq: x_{i+1,2} = phi*x_{i,2} + x_{i+1,1}^2 + c)
   - x_{i,2} for i = 1..n-2 (from round eq: x_{i+1,3} = phi*x_{i,3} + x_{i+1,2}^2 + c)

B. Tail triple (x_{n-1,3}, x_{n,2}, x_{n,3}): 6 LMs produce 2^3 = 8 states
   - x_{n-1,3}^2 (square): power <= 1
   - x_{n,2}^2 (square): power <= 1
   - x_{n-1,3} * x_{n,2} (interaction): can't have both
   - x_{n-1,3} * x_{n,3}^2 (higher): if x_{n,3}^2 present, x_{n-1,3}=0
   - x_{n,2} * x_{n,3}^2 (higher): if x_{n,3}^2 present, x_{n,2}=0
   - x_{n,3}^4 (higher): power <= 3

   Tail state count:
   - deg(x_{n,3})=0: 3 choices for (x_{n-1,3}, x_{n,2})
   - deg(x_{n,3})=1: 3 choices
   - deg(x_{n,3})=2: (0,0) forced = 1
   - deg(x_{n,3})=3: (0,0) forced = 1
   Total: 8 = 2^3

### Dimension Count

stdmons = 2^{3n-5} (interior) * 8 (tail) = 2^{3n-2}. QED.

## Structural Proof Summary for t=3

1. Five fixed variables eliminated linearly (Lemma 1)
2. Interior free vars have direct square LMs -> power <= 1 (Lemma 2)
3. Tail triple constrained by 6 LMs -> 2^3 states (Lemma 3)
4. Total: 2^{3n-5} * 2^3 = 2^{3n-2}
5. Hilbert series: (1+z)^{3n-2}
6. dreg = 3n-1 (achieved at degree 3n-2)
