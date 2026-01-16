# Wolfram Browser Queries for PrimeCohomology.lean

These are copy-paste ready queries for browser-based Wolfram tools (Wolfram Alpha, ChatGPT with Wolfram plugin, etc.).

## Wolfram Alpha Direct Links

For Wolfram Alpha, you can also use these direct queries:

### First Zeta Zero
[wolfram alpha: first nontrivial zero of Riemann zeta function](https://www.wolframalpha.com/input?i=first+nontrivial+zero+of+Riemann+zeta+function)

### Von Mangoldt at 8
[wolfram alpha: Sum MoebiusMu[8/d] * Log[d] for d dividing 8](https://www.wolframalpha.com/input?i=Sum+MoebiusMu%5B8%2Fd%5D+*+Log%5Bd%5D+for+d+dividing+8)

---

## Query 1: First Zeta Zero Value

**Copy-paste:**
```
What is the imaginary part of the first non-trivial zero of the Riemann zeta function to 20 decimal places?
```

**Expected answer:** `14.134725141734693790...`

---

## Query 2: Verify Von Mangoldt at Primes

**Copy-paste:**
```
For each prime p in {2, 3, 5, 7, 11, 13}, compute Sum[MoebiusMu[p/d] * Log[d], {d, Divisors[p]}] and simplify
```

**Expected:** Each should equal `Log[p]`

---

## Query 3: Verify Von Mangoldt at Prime Powers

**Copy-paste:**
```
For n in {4, 8, 9, 16, 25, 27}, compute Sum[MoebiusMu[n/d] * Log[d], {d, Divisors[n]}] and simplify
```

**Expected:**
- 4, 8, 16 → `Log[2]`
- 9, 27 → `Log[3]`
- 25 → `Log[5]`

---

## Query 4: Verify Composites Give Zero

**Copy-paste:**
```
For n in {6, 10, 12, 15, 18, 20}, compute Sum[MoebiusMu[n/d] * Log[d], {d, Divisors[n]}] and simplify
```

**Expected:** All should equal `0`

---

## Query 5: Scalar Sum at First Zeta Zero

**Copy-paste:**
```
Let t = 14.134725141734693790. Compute Sum[n^(-1/2) * Cos[t * Log[n]], {n, 1, 1000}] numerically
```

**Expected:** Should be close to `0` (within ±0.1 or so)

---

## Query 6: Bivector Sum at First Zeta Zero

**Copy-paste:**
```
Let t = 14.134725141734693790. Compute Sum[-n^(-1/2) * Sin[t * Log[n]], {n, 1, 1000}] numerically
```

**Expected:** Should be close to `0` (within ±0.1 or so)

---

## Query 7: Prime Kernel Coefficients (CRITICAL)

This is the key query to get the actual coefficients for `firstZeroCoeffs`.

**Copy-paste:**
```
Let t = 14.134725141734693790 (first zeta zero imaginary part).
Let primes = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}.
Define scalarTerms[p] = p^(-1/2) * Cos[t * Log[p]] for each prime.
Define bivectorTerms[p] = -p^(-1/2) * Sin[t * Log[p]] for each prime.
Find the null space of the matrix formed by [scalarTerms; bivectorTerms].
Give me specific numerical coefficients c_2, c_3, c_5, c_7, c_11, c_13, c_17, c_19, c_23, c_29 that satisfy:
Sum[c_p * scalarTerms[p]] = 0 AND Sum[c_p * bivectorTerms[p]] = 0
```

**Expected:** A list of 10 real numbers (the null space vector)

**Alternative simpler query:**
```
Find coefficients c_2, c_3, c_5, c_7, c_11 such that:
c_2 * 2^(-1/2) * Cos[14.1347 * Log[2]] + c_3 * 3^(-1/2) * Cos[14.1347 * Log[3]] + c_5 * 5^(-1/2) * Cos[14.1347 * Log[5]] + c_7 * 7^(-1/2) * Cos[14.1347 * Log[7]] + c_11 * 11^(-1/2) * Cos[14.1347 * Log[11]] = 0
AND
c_2 * 2^(-1/2) * Sin[14.1347 * Log[2]] + c_3 * 3^(-1/2) * Sin[14.1347 * Log[3]] + c_5 * 5^(-1/2) * Sin[14.1347 * Log[5]] + c_7 * 7^(-1/2) * Sin[14.1347 * Log[7]] + c_11 * 11^(-1/2) * Sin[14.1347 * Log[11]] = 0
```

---

## Query 8: Verify Dirichlet Series Identity

**Copy-paste:**
```
Compare Sum[vonMangoldt[n] / n^2, {n, 2, 1000}] with -Zeta'[2]/Zeta[2]
```

Where `vonMangoldt[n] = Log[p] if n = p^k for prime p, else 0`.

**Expected:** Values should be very close (within 0.001)

---

## Query 9: Convergence Test at Multiple N

**Copy-paste:**
```
Let t = 14.134725. For N in {100, 500, 1000, 5000}, compute:
{N, Sum[n^(-1/2) * Cos[t * Log[n]], {n, 1, N}], Sum[-n^(-1/2) * Sin[t * Log[n]], {n, 1, N}]}
```

**Expected:** Both sums should approach 0 as N increases

---

## How to Use Results in Lean

Once you get the coefficients from Query 7, update `PrimeCohomology.lean`:

```lean
def firstZeroCoeffs : ℕ → ℝ
  | 2 => <c_2 from Wolfram>
  | 3 => <c_3 from Wolfram>
  | 5 => <c_5 from Wolfram>
  | 7 => <c_7 from Wolfram>
  | 11 => <c_11 from Wolfram>
  | 13 => <c_13 from Wolfram>
  | 17 => <c_17 from Wolfram>
  | 19 => <c_19 from Wolfram>
  | 23 => <c_23 from Wolfram>
  | 29 => <c_29 from Wolfram>
  | _ => 0.0
```

---

## Quick Verification Checklist

After running queries, confirm:

- [ ] Query 2: All primes give `Log[p]` ✓
- [ ] Query 3: All prime powers give `Log[base prime]` ✓
- [ ] Query 4: All composites give `0` ✓
- [ ] Query 5: Scalar sum ≈ 0 ✓
- [ ] Query 6: Bivector sum ≈ 0 ✓
- [ ] Query 7: Got coefficients ✓
- [ ] Query 9: Convergence confirmed ✓
