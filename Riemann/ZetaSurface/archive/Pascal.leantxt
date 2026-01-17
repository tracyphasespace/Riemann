/-
# Pascal's Triangle and Binomial Coefficient Symmetry

**Purpose**: Prove binomial coefficient symmetry and Pascal's identity.

**Connection to Riemann Project**:
The numerical reduction of coefficients in the prime-indexed Clifford algebra Cl(N,N)
is functionally identical to Pascal's Triangle with different spacing:

- Pascal's Triangle: C(n,k) arranged in triangular form
- Prime coefficients: Same combinatorial structure, indexed by prime products

The key insight is that both structures satisfy:
1. **Symmetry**: C(n,k) = C(n, n-k)
2. **Recursion**: C(n,k) = C(n-1,k-1) + C(n-1,k)
3. **Boundary**: C(n,0) = C(n,n) = 1

In Cl(N,N), the grade-k component has dimension C(2N, k), and the symmetry
C(2N, k) = C(2N, 2N-k) reflects the duality between k-vectors and (2N-k)-vectors.

**Author**: AI3
**Status**: PROVEN
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

open Finset

namespace Riemann.Pascal

/-!
## 1. Binomial Coefficient Symmetry

The fundamental symmetry: C(n,k) = C(n, n-k)

This reflects the combinatorial fact that choosing k items to include
is equivalent to choosing (n-k) items to exclude.
-/

/--
**Binomial Symmetry (from first principles)**

C(n,k) = C(n, n-k)

Proof: Both equal n! / (k! × (n-k)!)
-/
theorem choose_symm_explicit (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) := by
  -- Use Mathlib's proven symmetry (reversed direction)
  exact (Nat.choose_symm h).symm

/--
**Symmetry restated**: Choosing k from n equals choosing (n-k) from n.

This is the form most useful for Clifford algebra grade duality.
-/
theorem grade_duality (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) :=
  (Nat.choose_symm h).symm

/-!
## 2. Pascal's Identity

The recursive structure: C(n,k) = C(n-1,k-1) + C(n-1,k)

This is how Pascal's Triangle is constructed row by row.
-/

/--
**Pascal's Identity**

C(n+1, k+1) = C(n, k) + C(n, k+1)

Each entry is the sum of the two entries above it.
-/
theorem pascal_identity (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k

/-!
## 3. Boundary Conditions

The edges of Pascal's Triangle are all 1s.
-/

/-- C(n, 0) = 1: Choosing nothing from n items has exactly one way -/
theorem choose_zero (n : ℕ) : Nat.choose n 0 = 1 :=
  Nat.choose_zero_right n

/-- C(n, n) = 1: Choosing everything from n items has exactly one way -/
theorem choose_self (n : ℕ) : Nat.choose n n = 1 :=
  Nat.choose_self n

/-!
## 4. Row Sum

The sum of row n equals 2^n.

This connects to the dimension of the full Clifford algebra:
dim(Cl(n,n)) = 2^(2n) = Σₖ C(2n, k)
-/

/-- Sum of binomial coefficients in row n equals 2^n -/
theorem row_sum (n : ℕ) : (Finset.range (n + 1)).sum (Nat.choose n) = 2 ^ n :=
  Nat.sum_range_choose n

/-!
## 5. Fibonacci Numbers: Diagonal Sums of Pascal's Triangle

**The Remarkable Connection:**
The diagonal sums of Pascal's Triangle ARE the Fibonacci numbers!

```
        1                    → 1 = F₁
       1 1                   → 1 = F₂
      1 2 1                  → 1+1 = 2 = F₃
     1 3 3 1                 → 1+2 = 3 = F₄
    1 4 6 4 1                → 1+3+1 = 5 = F₅
   1 5 10 10 5 1             → 1+4+3 = 8 = F₆
  1 6 15 20 15 6 1           → 1+5+6+1 = 13 = F₇
```

The diagonal going ↗ from each leftmost 1 sums to a Fibonacci number:
- F_{n+1} = Σₖ C(n-k, k) summing along the antidiagonal

**Why This Works:**
- Pascal's recurrence: C(n,k) = C(n-1,k-1) + C(n-1,k)
- Fibonacci recurrence: F_n = F_{n-1} + F_{n-2}
- The diagonal sum inherits the additive structure!

**The Golden Ratio Connection:**

Binet's formula gives the closed form:
```
F_n = (φⁿ - ψⁿ) / √5

where φ = (1 + √5)/2 ≈ 1.618  (Golden Ratio)
      ψ = (1 - √5)/2 ≈ -0.618 (Conjugate)
```

The Golden Ratio satisfies φ² = φ + 1, which is the continuous analogue
of the Fibonacci recurrence F_n = F_{n-1} + F_{n-2}.

**Connection to Primes and RH:**

The Fibonacci sequence and primes share deep structural similarities:
- Both grow roughly exponentially (F_n ~ φⁿ/√5, π(n) ~ n/ln(n))
- Both have "pseudo-random" fine structure
- Both connect to algebraic number theory (φ is algebraic, primes are...)

The Golden Ratio appears in:
- Continued fraction of √5
- Optimal packing/spirals in nature
- Quasicrystal diffraction patterns

These "golden" patterns and prime patterns may share common origins
in number-theoretic structure.
-/

/-- **Fibonacci-Pascal Connection**: Fibonacci numbers are diagonal sums of Pascal's Triangle.
    F_{n+1} = Σ_{(i,j) on antidiagonal n} C(i, j) -/
theorem fibonacci_diagonal_sum (n : ℕ) :
    Nat.fib (n + 1) = ∑ p ∈ Finset.antidiagonal n, Nat.choose p.1 p.2 :=
  Nat.fib_succ_eq_sum_choose n

/-- Fibonacci recurrence: F_{n+2} = F_n + F_{n+1} -/
theorem fibonacci_recurrence (n : ℕ) : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
  Nat.fib_add_two

/-- Sum of first n Fibonacci numbers: F_0 + F_1 + ... + F_n = F_{n+2} - 1 -/
theorem fibonacci_sum (n : ℕ) : Nat.fib (n + 1) = (∑ k ∈ Finset.range n, Nat.fib k) + 1 :=
  Nat.fib_succ_eq_succ_sum n

/-- **Binet's Formula**: F_n = (φⁿ - ψⁿ) / √5
    Connects Fibonacci to the Golden Ratio. -/
theorem binet_formula (n : ℕ) :
    (Nat.fib n : ℝ) = (Real.goldenRatio ^ n - Real.goldenConj ^ n) / Real.sqrt 5 :=
  Real.coe_fib_eq n

/-- The Golden Ratio φ = (1 + √5)/2 satisfies φ² = φ + 1 -/
theorem golden_ratio_property : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 :=
  Real.goldenRatio_sq

/-- The Golden Ratio and its conjugate sum to 1: φ + ψ = 1 -/
theorem golden_sum : Real.goldenRatio + Real.goldenConj = 1 :=
  Real.goldenRatio_add_goldenConj

/-- The Golden Ratio and its conjugate multiply to -1: φ · ψ = -1 -/
theorem golden_product : Real.goldenRatio * Real.goldenConj = -1 :=
  Real.goldenRatio_mul_goldenConj

/-!
## 6. Connection to Clifford Algebra Grading

In Cl(N,N), the grade-k subspace has dimension C(2N, k).

The total dimension is:
  dim(Cl(N,N)) = Σₖ C(2N, k) = 2^(2N)

The symmetry C(2N, k) = C(2N, 2N-k) reflects:
- k-vectors ↔ (2N-k)-vectors under Hodge duality
- The pseudoscalar (grade 2N) pairs with scalars (grade 0)
-/

/-- Clifford algebra grade dimensions are symmetric -/
theorem clifford_grade_symmetry (N k : ℕ) (h : k ≤ 2 * N) :
    Nat.choose (2 * N) k = Nat.choose (2 * N) (2 * N - k) :=
  (Nat.choose_symm h).symm

/-- Total dimension of Cl(N,N) -/
theorem clifford_total_dim (N : ℕ) :
    (Finset.range (2 * N + 1)).sum (Nat.choose (2 * N)) = 2 ^ (2 * N) :=
  Nat.sum_range_choose (2 * N)

/-!
## 7. Numerical Reduction Pattern and Universal Structure

**Key Insight for Documentation**:

The prime-indexed reduction in the Riemann project follows the same
numerical pattern as Pascal's Triangle:

```
Pascal's Triangle (standard):     Prime Coefficient Pattern:
        1                              [scalar]
       1 1                            [grade 1]
      1 2 1                          [grade 2]
     1 3 3 1                        [grade 3]
    1 4 6 4 1                      [grade 4]
```

The spacing differs but the VALUES are identical because both are
governed by binomial coefficients.

### Additive vs Multiplicative: The Same Underlying Structure

**Pascal (Additive):**
- Each entry is the SUM of two entries above: C(n,k) = C(n-1,k-1) + C(n-1,k)
- Row sum: 1 + 1 = 2, 1 + 2 + 1 = 4, 1 + 3 + 3 + 1 = 8, ...
- Pattern: 2^n

**Primes (Multiplicative):**
- Fundamental theorem: every n is a PRODUCT of primes
- Prime counting: π(n) grows as n/ln(n)
- Euler product: ζ(s) = Π_p (1 - p^{-s})^{-1}

**The Overlap:**
Both structures encode the SAME combinatorial information:
- Binomial coefficients count subsets (additive viewpoint)
- Prime factorizations count multiplicative structures
- They meet in the zeta function where sums become products

### Fibonacci and Golden Ratio Connection

The diagonal sums of Pascal's Triangle ARE the Fibonacci numbers:
```
        1                    → 1 (F₁)
       1 1                   → 1 (F₂)
      1 2 1                  → 2 (F₃ = 1+1)
     1 3 3 1                 → 3 (F₄ = 1+2)
    1 4 6 4 1                → 5 (F₅ = 1+3+1)
   1 5 10 10 5 1             → 8 (F₆ = 1+4+3)
```

The Golden Ratio φ = (1 + √5)/2 emerges as:
- lim(Fₙ₊₁/Fₙ) = φ
- φ² = φ + 1 (the recursive structure)

**This connects to primes:**
- Prime gaps exhibit quasi-periodic structure
- The zeta zeros have spacing related to log structure
- Both Pascal diagonals and prime distributions follow
  similar statistical laws at large scale

### Primes: What Remains After Symmetry is Removed

**Key Principle**: Normally we find symmetry patterns first.
Primes are what's LEFT OVER when all symmetry is removed.

- **Composite numbers** have structure: 6 = 2 × 3, 12 = 2² × 3
- **Primes** have NO multiplicative structure - they're irreducible
- Primes are the "atoms" precisely because they lack internal symmetry

This is why:
- Pascal's Triangle has beautiful symmetry (C(n,k) = C(n,n-k))
- Composites factor symmetrically into prime products
- But primes themselves are the ASYMMETRIC residue

**The Sieve of Eratosthenes visualizes this:**
Start with all numbers (symmetric, regular)
Remove multiples of 2 (remove one symmetry)
Remove multiples of 3 (remove another symmetry)
... continue ...
What remains = primes = the irreducible, asymmetric core

### The Meta-Symmetry: Asymmetry Has Its Own Symmetry

**Key Insight**: The negative of all symmetries has its own symmetry.

Primes individually have no internal structure (they're irreducible).
But the COLLECTION of primes exhibits statistical regularity:
- Prime Number Theorem: π(x) ~ x/ln(x)
- Prime gaps have bounded average behavior
- The sum Σ 1/p diverges (slowly)

**This is the meta-symmetry**: What remains after removing all patterns
still follows a pattern - just at a higher level of abstraction.

### Why This Matters for Riemann Hypothesis

The RH is fundamentally about the RELATIONSHIP between:
1. **Symmetric structure**: zeros on Re(s) = 1/2 line (SYMMETRY of ζ)
2. **Asymmetric residue**: prime distribution (what's LEFT after sieving)
3. **Meta-symmetry**: The asymmetric primes create symmetric zero distribution

Pascal's Triangle shows us that additive recursion (binomial coefficients)
and multiplicative structure (factorial = product) are two views of
the SAME mathematical object.

The Cl(N,N) formalization makes this explicit:
- Grade structure follows binomial coefficients (SYMMETRIC)
- Prime-indexed generators are ORTHOGONAL (the irreducible basis)
- The critical line σ = 1/2 is where symmetric and asymmetric MEET

When we reduce modulo a prime p:
- Entries divisible by p vanish
- The pattern reveals p-adic structure
- Lucas' theorem governs C(n,k) mod p

This connects the combinatorial structure of Pascal's Triangle
to the prime factorization structure in the zeta function.
-/

/-!
## 8. Lucas' Theorem: Binomial Coefficients Modulo Primes

**Lucas' Theorem** (1878): For a prime p and non-negative integers m, n:

```
C(m, n) ≡ ∏ᵢ C(mᵢ, nᵢ) (mod p)
```

where m = Σᵢ mᵢ·pⁱ and n = Σᵢ nᵢ·pⁱ are the base-p representations.

**The Recursive Form:**
```
C(m, n) ≡ C(m mod p, n mod p) · C(m/p, n/p) (mod p)
```

**Why This Matters:**

1. **Fractal Structure of Pascal's Triangle mod p:**
   - Pascal's Triangle mod 2 gives Sierpiński's triangle (fractal!)
   - Pascal's Triangle mod 3 gives a similar self-similar pattern
   - Each prime p reveals different fractal structure

2. **Connection to p-adic Numbers:**
   - The base-p digits of m and n determine C(m,n) mod p
   - This is fundamentally p-adic in nature
   - Links combinatorics to p-adic analysis

3. **For the Riemann Hypothesis:**
   - Primes create fractal patterns in Pascal's Triangle
   - The zeta function encodes prime distribution
   - Both structures reflect the "prime skeleton" of integers

**Example (p = 2):**
```
C(5, 2) mod 2:
  5 = 101₂, 2 = 010₂
  C(1,0) · C(0,1) · C(1,0) = 1 · 0 · 1 = 0
  Indeed: C(5,2) = 10 ≡ 0 (mod 2) ✓
```

**The Sierpiński Pattern:**
Pascal's Triangle mod 2:
```
        1
       1 1
      1 0 1
     1 1 1 1
    1 0 0 0 1
   1 1 0 0 1 1
  1 0 1 0 1 0 1
 1 1 1 1 1 1 1 1
```
The zeros form a fractal pattern - Sierpiński's gasket!
-/

/-- **Lucas' Theorem (one step)**: C(n,k) ≡ C(n%p, k%p) · C(n/p, k/p) (mod p)
    This reduces binomial coefficients modulo p to their base-p digits. -/
theorem lucas_one_step (p n k : ℕ) [Fact p.Prime] :
    Nat.choose n k ≡ Nat.choose (n % p) (k % p) * Nat.choose (n / p) (k / p) [MOD p] :=
  Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- **Lucas' Theorem (full)**: C(n,k) ≡ ∏ᵢ C(nᵢ, kᵢ) (mod p)
    where nᵢ, kᵢ are the i-th base-p digits of n, k. -/
theorem lucas_theorem_full (p n k a : ℕ) [Fact p.Prime] (hn : n < p ^ a) (hk : k < p ^ a) :
    Nat.choose n k ≡ ∏ i ∈ Finset.range a,
      Nat.choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] :=
  Choose.lucas_theorem_nat hn hk

/-- Lucas' theorem implies: if any digit of k exceeds corresponding digit of n,
    then C(n,k) ≡ 0 (mod p). This creates the fractal "holes" in Pascal mod p. -/
theorem lucas_zero_pattern (p n k : ℕ) [Fact p.Prime] (h : k % p > n % p) :
    p ∣ Nat.choose n k := by
  have : Nat.choose (n % p) (k % p) = 0 := Nat.choose_eq_zero_of_lt h
  have step := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := n) (k := k)
  simp only [this, zero_mul, Nat.ModEq, Nat.zero_mod] at step
  exact Nat.dvd_of_mod_eq_zero step

/-!
### Lucas' Theorem and the Riemann Connection

The fractal patterns revealed by Lucas' theorem connect to the Riemann Hypothesis:

**Sierpiński Triangle (mod 2):**
- Dimension: log(3)/log(2) ≈ 1.585
- Self-similar at all scales
- Encodes divisibility by 2

**General mod p:**
- Each prime p creates a different fractal
- The "holes" (zeros) follow p-adic structure
- Prime detection through pattern recognition

**Link to Zeta:**
- ζ(s) = Π_p (1 - p^{-s})^{-1} (Euler product)
- Each prime p contributes independently
- Lucas shows each prime creates independent fractal in Pascal

**The Deep Pattern:**
- Additive structure (Pascal) + Prime modulus → Fractal
- Multiplicative structure (Primes) + Summation → Zeta
- Both reveal the same underlying number-theoretic reality
-/

/-!
## 9. Kummer's Theorem: Prime Power Divisibility

**Kummer's Theorem** (1852): The highest power of prime p dividing C(m+n, m)
equals the number of carries when adding m and n in base p.

```
p^k | C(m+n, m)  where k = #{carries when computing m + n in base p}
```

**Why Carries?**

When we add in base p, a carry occurs at position i when:
```
(m mod p^{i+1})/p^i + (n mod p^{i+1})/p^i ≥ p
```

Each carry "uses up" one factor of p from the factorials in C(m+n,m) = (m+n)!/(m!·n!).

**Example (p = 2, m = 5, n = 3):**
```
  5 = 101₂
+ 3 = 011₂
---------
  8 = 1000₂   (2 carries at positions 0 and 2)

So 2² | C(8,5) = 56 = 8 × 7 ✓
Indeed: 56 = 2³ × 7, and ν₂(56) = 3 ≥ 2
```

**Connection to Lucas:**
- Lucas: C(n,k) mod p depends on base-p digits
- Kummer: ν_p(C(n,k)) counts carries in base-p addition
- Both encode p-adic structure of binomial coefficients

**Connection to p-adic Valuations:**

The p-adic valuation ν_p(n) = max{k : p^k | n} satisfies:
- ν_p(m·n) = ν_p(m) + ν_p(n)  (multiplicative)
- ν_p(m+n) ≥ min(ν_p(m), ν_p(n))  (ultrametric inequality)

Kummer tells us: ν_p(C(m+n,m)) = (carries in m+n base p)

**For the Riemann Hypothesis:**

The p-adic valuations create a "stratification" of integers:
- ν_p(n) measures how "divisible by p" the number n is
- This stratification is key to understanding ζ(s)
- The functional equation ζ(s) = ζ(1-s) reflects p-adic symmetries
-/

/-- **Kummer's Theorem**: The p-adic valuation of C(n+k, k) equals the number of
    carries when adding n and k in base p.

    Formally: emultiplicity p (C(n+k,k)) = #{i ∈ [1,b) | p^i ≤ (k mod p^i) + (n mod p^i)}
    where b > log_p(n+k). -/
theorem kummer_theorem (p n k b : ℕ) (hp : p.Prime) (hb : Nat.log p (n + k) < b) :
    emultiplicity p (Nat.choose (n + k) k) =
      (Finset.filter (fun i => p ^ i ≤ k % p ^ i + n % p ^ i) (Finset.Ico 1 b)).card :=
  Nat.Prime.emultiplicity_choose' hp hb

/-- Kummer's theorem for C(n, k) where k ≤ n: counts carries when adding k and (n-k). -/
theorem kummer_theorem_choose (p n k b : ℕ) (hp : p.Prime) (hkn : k ≤ n)
    (hb : Nat.log p n < b) :
    emultiplicity p (Nat.choose n k) =
      (Finset.filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i) (Finset.Ico 1 b)).card :=
  Nat.Prime.emultiplicity_choose hp hkn hb

/-- Special case: For C(p^n, k), the p-adic valuation is n minus the p-adic valuation of k. -/
theorem kummer_prime_power (p n k : ℕ) (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    emultiplicity p (Nat.choose (p ^ n) k) = ↑(n - multiplicity p k) :=
  Nat.Prime.emultiplicity_choose_prime_pow hp hkn hk0

/-- Key corollary: p divides C(p^n, k) for 0 < k < p^n.
    This shows the "middle" of Pascal's row p^n is all divisible by p. -/
theorem prime_divides_middle_choose (p n k : ℕ) (hp : Nat.Prime p)
    (hk0 : k ≠ 0) (hkp : k ≠ p ^ n) :
    p ∣ Nat.choose (p ^ n) k :=
  Nat.Prime.dvd_choose_pow hp hk0 hkp

/-!
### Kummer, Lucas, and the Fractal-Valuation Duality

**Lucas** answers: What is C(n,k) mod p?
**Kummer** answers: What is the exact power of p dividing C(n,k)?

Together they give complete p-adic information about binomial coefficients:
- Lucas: the "horizontal" structure (residue classes)
- Kummer: the "vertical" structure (divisibility depth)

**The Carry Interpretation:**
```
No carries ⟺ C(m+n,m) coprime to p ⟺ All digit sums < p
```

This explains why:
- Row p^n of Pascal's Triangle is mostly divisible by p (many carries)
- Row p-1 has no entries divisible by p (no carries possible)

**For Riemann:**
The interplay of Lucas and Kummer shows how each prime p independently
"filters" Pascal's Triangle. The zeta function aggregates these filters:
- ζ(s) = Π_p (local p-information)
- RH = all this local information balances on Re(s) = 1/2
-/

/-!
## 10. Legendre's Formula: Prime Powers in Factorials

**Legendre's Formula** (1808): The exact power of prime p dividing n! is:

```
ν_p(n!) = Σ_{i=1}^∞ floor(n/p^i) = floor(n/p) + floor(n/p²) + floor(n/p³) + ...
```

**Alternative Form (using digit sums):**
```
ν_p(n!) = (n - s_p(n)) / (p - 1)
```
where s_p(n) = sum of digits of n in base p.

**Why This Works:**

Among 1, 2, ..., n:
- floor(n/p) are divisible by p
- floor(n/p²) are divisible by p²
- floor(n/p³) are divisible by p³
- etc.

Each contributes to the total power of p in n!.

**Example (p = 2, n = 10):**
```
ν₂(10!) = floor(10/2) + floor(10/4) + floor(10/8) + floor(10/16) + ...
        = 5 + 2 + 1 + 0 + ...
        = 8

Check: 10! = 3628800 = 2⁸ × 14175 ✓
```

**Alternative calculation:**
```
10 = 1010₂, so s₂(10) = 1 + 0 + 1 + 0 = 2
ν₂(10!) = (10 - 2)/(2 - 1) = 8 ✓
```

**Connection to Binomial Coefficients:**

Since C(n,k) = n! / (k! · (n-k)!), we have:
```
ν_p(C(n,k)) = ν_p(n!) - ν_p(k!) - ν_p((n-k)!)
```

This is exactly what Kummer's theorem computes via carries!

**The Deep Connection:**
- Legendre counts p-factors in factorials (building blocks)
- Kummer counts p-factors in binomial coefficients (combinations)
- Both use base-p digit structure
- Together they explain Pascal's Triangle mod p^k for all k

**For the Riemann Hypothesis:**

The factorial n! appears in:
- Gamma function: Γ(n+1) = n!
- Functional equation: ζ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s) ζ(1-s)
- Stirling's approximation: n! ~ √(2πn) (n/e)^n

Legendre's formula shows how primes "accumulate" in factorials,
which is fundamental to understanding Γ(s) and hence ζ(s).
-/

/-- **Legendre's Formula**: ν_p(n!) = Σ_{i∈[1,b)} floor(n/p^i)
    where b > log_p(n). -/
theorem legendre_formula (p n b : ℕ) (hp : p.Prime) (hb : Nat.log p n < b) :
    emultiplicity p n.factorial = (∑ i ∈ Finset.Ico 1 b, n / p ^ i : ℕ) :=
  Nat.Prime.emultiplicity_factorial hp hb

/-- **Legendre's Formula (digit sum form)**: (p-1) · ν_p(n!) = n - s_p(n)
    where s_p(n) is the sum of base-p digits of n. -/
theorem legendre_digit_sum (p n : ℕ) (hp : p.Prime) :
    (p - 1) * multiplicity p n.factorial = n - (Nat.digits p n).sum :=
  Nat.Prime.sub_one_mul_multiplicity_factorial hp

/-- The multiplicity of p in (p·n)! is n more than in n!.
    This shows how p "accelerates" accumulation in factorials. -/
theorem legendre_factorial_mul (p n : ℕ) (hp : p.Prime) :
    emultiplicity p (p * n).factorial = emultiplicity p n.factorial + n :=
  Nat.Prime.emultiplicity_factorial_mul hp

/-- The multiplicity of p in (p^n)! equals the geometric sum 1 + p + p² + ... + p^{n-1}. -/
theorem legendre_factorial_prime_pow (p n : ℕ) (hp : p.Prime) :
    multiplicity p (p ^ n).factorial = ∑ i ∈ Finset.range n, p ^ i :=
  Nat.Prime.multiplicity_factorial_pow hp

/-- Upper bound: ν_p(n!) ≤ n/(p-1). Equality when n = p^k - 1 (all digits are p-1). -/
theorem legendre_upper_bound (p n : ℕ) (hp : p.Prime) :
    emultiplicity p n.factorial ≤ (n / (p - 1) : ℕ) :=
  Nat.Prime.emultiplicity_factorial_le_div_pred hp n

/-- Criterion: p^r divides n! iff r ≤ Σ floor(n/p^i). -/
theorem legendre_divisibility (p n r b : ℕ) (hp : p.Prime) (hb : Nat.log p n < b) :
    p ^ r ∣ n.factorial ↔ r ≤ ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
  Nat.Prime.pow_dvd_factorial_iff hp hb

/-!
### Legendre, Kummer, and the Factorial-Binomial Bridge

**The Fundamental Relationship:**
```
C(n,k) = n! / (k! · (n-k)!)
```

So by Legendre:
```
ν_p(C(n,k)) = ν_p(n!) - ν_p(k!) - ν_p((n-k)!)
            = Σᵢ (floor(n/pⁱ) - floor(k/pⁱ) - floor((n-k)/pⁱ))
```

**The Carry Equivalence:**

For each i, the term `floor(n/pⁱ) - floor(k/pⁱ) - floor((n-k)/pⁱ)` equals:
- 1 if there's a carry at position i when adding k + (n-k) in base p
- 0 otherwise

This is exactly Kummer's theorem!

**Why Carries = Legendre Differences:**

When adding a + b in base p at position i:
- If aᵢ + bᵢ < p: no carry, floor((a+b)/pⁱ) = floor(a/pⁱ) + floor(b/pⁱ)
- If aᵢ + bᵢ ≥ p: carry, floor((a+b)/pⁱ) = floor(a/pⁱ) + floor(b/pⁱ) + 1

So Kummer = "Legendre applied to binomial coefficients".

**The Complete Picture:**

| Formula | What it computes | Method |
|---------|-----------------|--------|
| Legendre | ν_p(n!) | Sum floor(n/pⁱ) |
| Legendre (alt) | ν_p(n!) | (n - digit_sum)/(p-1) |
| Kummer | ν_p(C(n,k)) | Count carries |
| Lucas | C(n,k) mod p | Product of digit-wise C(nᵢ,kᵢ) |

All four are manifestations of the same p-adic structure!
-/

/-!
## 11. Wilson's Theorem: Prime Characterization via Factorials

**Wilson's Theorem** (1770): For n > 1:
```
n is prime  ⟺  (n-1)! ≡ -1 (mod n)
```

This gives a **characterization of primes** using factorials!

**Why It Works (for primes):**

In ℤ/pℤ (integers mod p), the nonzero elements form a group under multiplication.
Every element except 1 and -1 (= p-1) pairs with a distinct inverse:
```
2 · (2⁻¹) ≡ 1 (mod p)
3 · (3⁻¹) ≡ 1 (mod p)
...
```

The unpaired elements are exactly those where a = a⁻¹, i.e., a² ≡ 1 (mod p).
For prime p, only a = 1 and a = p-1 satisfy this.

So: (p-1)! = 1 · 2 · 3 · ... · (p-1)
         = (paired products) · 1 · (p-1)
         = 1 · 1 · ... · 1 · (p-1)
         ≡ -1 (mod p)

**Why It Fails (for composites):**

If n = ab with 1 < a, b < n:
- a divides (n-1)! (since a < n)
- So (n-1)! ≡ 0 (mod a)
- But -1 ≢ 0 (mod a) when a > 1
- Contradiction!

**Example:**
```
4! = 24 ≡ 4 (mod 5)  →  5 is prime ✓
    BUT  24 ≡ 0 (mod 4)  ≠ -1 = 3 (mod 4)  →  4 not prime ✓

6! = 720 ≡ 6 (mod 7)  →  7 is prime ✓
    (since -1 ≡ 6 (mod 7))
```

**Connection to Legendre and Primes:**

Wilson's theorem connects factorials to primality:
- Legendre: How many times does p divide n!
- Wilson: When does n divide (n-1)! + 1

Together they reveal the deep relationship between factorials and primes.

**For the Riemann Hypothesis:**

Wilson's theorem shows factorials "detect" primes through congruences.
The zeta function encodes primes through its Euler product.
Both are different views of the same prime structure:
- Wilson: local (mod p) behavior
- Zeta: global (analytic) behavior
-/

/-- **Wilson's Lemma**: For prime p, (p-1)! ≡ -1 (mod p).
    The product of all nonzero residues mod p equals -1. -/
theorem wilsons_lemma (p : ℕ) [Fact p.Prime] : ((p - 1).factorial : ZMod p) = -1 :=
  ZMod.wilsons_lemma p

/-- **Wilson's Theorem (converse)**: If (n-1)! ≡ -1 (mod n) and n ≠ 1, then n is prime.
    This direction shows Wilson's criterion detects primes. -/
theorem wilson_converse (n : ℕ) (h : ((n - 1).factorial : ZMod n) = -1) (hn : n ≠ 1) :
    n.Prime :=
  Nat.prime_of_fac_equiv_neg_one h hn

/-- **Wilson's Theorem (full characterization)**:
    For n ≠ 1: n is prime ⟺ (n-1)! ≡ -1 (mod n).
    This is the complete prime characterization via factorials. -/
theorem wilson_iff_prime (n : ℕ) (hn : n ≠ 1) :
    n.Prime ↔ ((n - 1).factorial : ZMod n) = -1 :=
  Nat.prime_iff_fac_equiv_neg_one hn

/-!
### Wilson, Legendre, and the Factorial-Prime Connection

**Three Views of Factorials and Primes:**

| Theorem | What it tells us |
|---------|------------------|
| **Legendre** | How much p divides n! (counting) |
| **Wilson** | When n divides (n-1)!+1 (characterization) |
| **Kummer** | How much p divides C(n,k) (combinatorics) |

**The Unifying Theme:**
All three connect factorials to prime structure:
- Legendre uses p-adic valuation (depth)
- Wilson uses modular arithmetic (residue)
- Kummer uses digit representation (carries)

**For Cryptography:**
Wilson's theorem gives a primality test (though inefficient: O(n)):
```
isPrime(n) = ((n-1)! + 1) mod n == 0
```

In practice, probabilistic tests (Miller-Rabin) are used instead.
But Wilson's theorem has theoretical importance for understanding primes.
-/

/-!
## 12. Fermat's Little Theorem: Prime Power Congruences

**Fermat's Little Theorem** (1640): For prime p and integer a not divisible by p:
```
a^{p-1} ≡ 1 (mod p)
```

**Equivalent Form**: For any integer a:
```
a^p ≡ a (mod p)
```

**Why It Works:**

In ℤ/pℤ, the nonzero elements form a multiplicative group of order p-1.
By Lagrange's theorem, every element's order divides the group order.
So for any nonzero a: a^{p-1} = 1.

**Example (p = 7):**
```
3^6 = 729 = 104 × 7 + 1 ≡ 1 (mod 7) ✓
5^6 = 15625 = 2232 × 7 + 1 ≡ 1 (mod 7) ✓
```

**Connection to Wilson's Theorem:**

| Theorem | Statement | Group Theory |
|---------|-----------|--------------|
| **Wilson** | (p-1)! ≡ -1 (mod p) | Product of all elements = -1 |
| **Fermat** | a^{p-1} ≡ 1 (mod p) | Order divides group order |

Both characterize primes through the multiplicative group structure of ℤ/pℤ.

**The Fermat-Euler Generalization:**

For any n and a coprime to n:
```
a^{φ(n)} ≡ 1 (mod n)
```
where φ(n) is Euler's totient function (count of integers ≤ n coprime to n).

For prime p: φ(p) = p-1, recovering Fermat's Little Theorem.

**Applications:**
- RSA cryptography (Fermat-Euler powers)
- Primality testing (Fermat test, Miller-Rabin)
- Computing modular inverses: a^{-1} ≡ a^{p-2} (mod p)

**For the Riemann Hypothesis:**

Fermat's Little Theorem shows primes create cyclic group structure in ℤ/pℤ.
The zeta function encodes how these local structures (at each prime p)
combine globally:
- Local: (ℤ/pℤ)ˣ has order p-1
- Global: ζ(s) = Π_p (1 - p^{-s})^{-1}

The critical line σ = 1/2 is where local and global behaviors balance.
-/

/-- **Fermat's Little Theorem (multiplicative form)**:
    For prime p and any x : ZMod p, we have x^p = x.
    This is the "strong form" that works for all elements including 0. -/
theorem fermat_little_full (p : ℕ) [Fact p.Prime] (x : ZMod p) : x ^ p = x :=
  ZMod.pow_card x

/-- **Fermat's Little Theorem (standard form)**:
    For prime p and nonzero a : ZMod p, we have a^{p-1} = 1.
    This is the classic formulation for nonzero elements. -/
theorem fermat_little (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one ha

/-- **Fermat's Little Theorem (units form)**:
    For prime p and any unit a : (ZMod p)ˣ, we have a^{p-1} = 1. -/
theorem fermat_little_units (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) :
    a ^ (p - 1) = 1 :=
  ZMod.units_pow_card_sub_one_eq_one p a

/-- **Fermat's Little Theorem (natural numbers)**:
    For prime p and n coprime to p, we have n^{p-1} ≡ 1 (mod p). -/
theorem fermat_little_nat (p : ℕ) (hp : p.Prime) {n : ℕ} (hpn : n.Coprime p) :
    n ^ (p - 1) ≡ 1 [MOD p] :=
  Nat.ModEq.pow_card_sub_one_eq_one hp hpn

/-- **Fermat's Little Theorem (integers)**:
    For prime p and n coprime to p, we have n^{p-1} ≡ 1 (mod p). -/
theorem fermat_little_int (p : ℕ) (hp : p.Prime) {n : ℤ} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] :=
  Int.ModEq.pow_card_sub_one_eq_one hp hpn

/-- **Fermat-Euler Totient Theorem (units)**:
    For any n and unit x : (ZMod n)ˣ, we have x^{φ(n)} = 1.
    This generalizes Fermat's Little Theorem to all moduli. -/
theorem fermat_euler (n : ℕ) (x : (ZMod n)ˣ) : x ^ Nat.totient n = 1 :=
  ZMod.pow_totient x

/-- **Fermat-Euler Totient Theorem (natural numbers)**:
    For n coprime to m, we have n^{φ(m)} ≡ 1 (mod m).
    This is the natural number version of Euler's theorem. -/
theorem fermat_euler_nat {x n : ℕ} (h : x.Coprime n) : x ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

/-- The order of any unit divides p - 1 (consequence of Lagrange).
    This is why Fermat's Little Theorem works. -/
theorem fermat_order_divides (p : ℕ) [Fact p.Prime] (u : (ZMod p)ˣ) :
    orderOf u ∣ p - 1 :=
  ZMod.orderOf_units_dvd_card_sub_one u

/-!
### Fermat, Wilson, and the Group Structure

**Three Views of (ℤ/pℤ)ˣ:**

| Theorem | What it computes | Group interpretation |
|---------|-----------------|---------------------|
| **Fermat** | a^{p-1} = 1 | Order divides |G| |
| **Wilson** | (p-1)! = -1 | Product of all elements |
| **Primitive Root** | generator exists | G is cyclic |

**Why Primes Are Special:**
- (ℤ/nℤ)ˣ has order φ(n)
- For prime p: φ(p) = p - 1 and (ℤ/pℤ)ˣ is cyclic
- For composite n: (ℤ/nℤ)ˣ may not be cyclic

**Connection to Quadratic Reciprocity:**
Fermat's Little Theorem leads to:
- Euler's criterion: a^{(p-1)/2} ≡ ±1 (mod p)
- The +1 case: a is a quadratic residue mod p
- This connects to quadratic reciprocity and beyond

**For Cryptography:**
RSA uses Fermat-Euler: if n = pq and ed ≡ 1 (mod φ(n)), then
(m^e)^d = m^{ed} ≡ m (mod n) for gcd(m,n) = 1.
-/

/-!
## 13. Möbius Inversion: The Multiplicative Analogue

**The Key Duality:**

| Additive (Pascal) | Multiplicative (Möbius) |
|-------------------|-------------------------|
| Binomial coefficients C(n,k) | Divisor structure d \| n |
| Pascal identity: C(n,k) = C(n-1,k-1) + C(n-1,k) | Multiplicativity: f(mn) = f(m)f(n) |
| Binomial inversion | **Möbius inversion** |
| Row sum: Σ C(n,k) = 2^n | Euler product: ζ(s) = Π_p (1-p^{-s})^{-1} |

**The Möbius Function μ(n):**
- μ(1) = 1
- μ(p₁p₂...pₖ) = (-1)^k for k distinct primes
- μ(n) = 0 if n has a squared prime factor

**Möbius Inversion Formula:**
```
If g(n) = Σ_{d|n} f(d)    then    f(n) = Σ_{d|n} μ(d)·g(n/d)
```

This is the multiplicative analogue of binomial inversion:
```
If g(n) = Σₖ C(n,k)·f(k)  then    f(n) = Σₖ (-1)^k·C(n,k)·g(k)
```

**Connection to Zeta Function:**
The Möbius function inverts the zeta function in Dirichlet convolution:
- ζ(s) = Σ n^{-s}           (sum over all n)
- 1/ζ(s) = Σ μ(n)·n^{-s}    (weighted by Möbius)

This is how the "fractal residue" (primes encoded in μ) connects back
to the symmetric structure (zeta function).
-/

open ArithmeticFunction in
/-- The Möbius function μ applied to 1 gives 1 -/
theorem moebius_one : moebius 1 = 1 := moebius_apply_one

open ArithmeticFunction in
/-- The Möbius function μ applied to a prime gives -1 -/
theorem moebius_prime (p : ℕ) (hp : p.Prime) : moebius p = -1 :=
  moebius_apply_prime hp

open ArithmeticFunction in
/-- Möbius function is multiplicative: μ(mn) = μ(m)μ(n) for coprime m, n -/
theorem moebius_multiplicative : IsMultiplicative moebius :=
  isMultiplicative_moebius

open ArithmeticFunction in
open scoped ArithmeticFunction.zeta in
/-- The fundamental identity: μ * ζ = 1 in Dirichlet convolution.
    This says Σ_{d|n} μ(d) = 1 if n=1, else 0. -/
theorem moebius_zeta_convolution : (moebius * ζ : ArithmeticFunction ℤ) = 1 :=
  moebius_mul_coe_zeta

open ArithmeticFunction in
/-- Möbius inversion: the multiplicative analogue of binomial inversion.
    If g(n) = Σ_{d|n} f(d), then f(n) = Σ_{d|n} μ(n/d)·g(d). -/
theorem moebius_inversion {f g : ℕ → ℤ} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (moebius x.fst : ℤ) * g x.snd = f n :=
  sum_eq_iff_sum_mul_moebius_eq

/-!
### Why Möbius Inversion Matters for Riemann Hypothesis

The Möbius function encodes the "prime residue" - what's left after
removing all composite structure. The identity μ * ζ = 1 says:

**"The sum of μ over divisors detects whether n = 1"**

This is the multiplicative version of:
**"The alternating sum of binomial coefficients is 0 for n > 0"**

Both are expressing: **inversion recovers the original from the cumulative**.

For the Riemann Hypothesis:
- ζ(s) encodes the cumulative prime structure (Euler product)
- 1/ζ(s) = Σ μ(n)/n^s recovers individual prime information
- Zeros of ζ(s) ↔ poles of 1/ζ(s)
- The distribution of zeros (RH) ↔ the behavior of μ(n)

**The Prime Number Theorem is equivalent to:** Σ_{n≤x} μ(n) = o(x)
**The Riemann Hypothesis is equivalent to:** Σ_{n≤x} μ(n) = O(x^{1/2+ε})

So Möbius inversion connects Pascal-like combinatorics to the deepest
questions about prime distribution.
-/

/-!
## 14. Euler Product: Sum Becomes Product

**The Fundamental Identity:**
```
ζ(s) = Σ_{n=1}^∞ n^{-s} = Π_p (1 - p^{-s})^{-1}
```

This says: **the sum over ALL positive integers equals the product over PRIMES**.

**Why This Is Revolutionary:**
- Left side: Additive structure (sum over n = 1, 2, 3, 4, ...)
- Right side: Multiplicative structure (product over primes 2, 3, 5, 7, ...)
- The equality connects additive and multiplicative number theory

**The Proof Idea (Euler's Sieve):**
```
Σ n^{-s} = 1 + 2^{-s} + 3^{-s} + 4^{-s} + ...

Multiply by (1 - 2^{-s}):
  (1 - 2^{-s}) · Σ n^{-s} = 1 + 3^{-s} + 5^{-s} + 7^{-s} + 9^{-s} + ...
                         = (sum over odd n only)

Multiply by (1 - 3^{-s}):
  (1 - 3^{-s})(1 - 2^{-s}) · Σ n^{-s} = 1 + 5^{-s} + 7^{-s} + 11^{-s} + ...
                                      = (sum over n coprime to 6)

Continue for all primes p → only n = 1 survives → product = 1/Σn^{-s}
```

**Connection to Pascal's Triangle:**

| Pascal (Additive) | Euler Product (Multiplicative) |
|-------------------|-------------------------------|
| Row sum: Σ C(n,k) = 2^n | ζ(s) = Π_p (1-p^{-s})^{-1} |
| Binomial expansion: (1+1)^n | Geometric expansion: (1-x)^{-1} = Σ x^k |
| Combinatorial counting | Prime factorization counting |

Both convert SUMS to PRODUCTS through the same algebraic identity:
- Pascal: (1+x)^n = Σ C(n,k) x^k
- Euler: (1-x)^{-1} = Σ x^k  (geometric series)

**The Fractal Connection:**
The Euler product shows why primes create fractal-like patterns:
- Each prime p contributes a factor (1 - p^{-s})^{-1}
- These factors are INDEPENDENT (primes are coprime)
- The product structure creates self-similar scaling at each prime
-/

/-- Euler product: For completely multiplicative f with summable norm,
    ∏' p prime, (1 - f(p))⁻¹ = Σ' n, f(n).

    This is THE fundamental identity connecting sums and products over primes. -/
theorem euler_product_completely_multiplicative {F : Type*} [NormedField F] [CompleteSpace F]
    {f : ℕ →*₀ F} (hsum : Summable (‖f ·‖)) :
    ∏' p : Nat.Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  EulerProduct.eulerProduct_completely_multiplicative_tprod hsum

/-- General Euler product for multiplicative functions:
    ∏' p prime, Σ' e, f(p^e) = Σ' n, f(n) -/
theorem euler_product_multiplicative {R : Type*} [NormedCommRing R] [CompleteSpace R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Nat.Primes, ∑' e, f (p ^ e) = ∑' n, f n :=
  hf.eulerProduct_tprod hsum

/-!
### The Deep Unity: Pascal, Möbius, and Euler

All three structures express the SAME mathematical reality:

1. **Pascal's Triangle**: (1 + x)^n = Σ C(n,k) x^k
   - Binomial coefficients count subsets
   - Row sums equal 2^n

2. **Möbius Inversion**: If g = Σ_{d|n} f(d), then f = Σ_{d|n} μ(d) g(n/d)
   - Recovers original from cumulative
   - μ * ζ = 1 in Dirichlet convolution

3. **Euler Product**: Σ n^{-s} = Π_p (1 - p^{-s})^{-1}
   - Sum over integers = Product over primes
   - Geometric series at each prime

**The Unifying Theme:**
- **Pascal** says: subsets of {1,...,n} are counted by binomial coefficients
- **Möbius** says: divisors of n are "inverted" by the Möbius function
- **Euler** says: integers factor uniquely into primes

All three are manifestations of the **Fundamental Theorem of Arithmetic**:
every integer > 1 is a unique product of primes.

The FRACTAL nature of primes emerges because:
- Primes have no internal structure (irreducible)
- But their DISTRIBUTION follows statistical laws (PNT, RH)
- The Euler product makes this distribution visible

**For the Riemann Hypothesis:**
- ζ(s) = 0 ⟺ the Euler product "balances perfectly"
- RH says this balance occurs exactly on Re(s) = 1/2
- The critical line is where additive (Σ) and multiplicative (Π) structures MEET
-/

/-!
## Summary

**What's Proven:**

*Additive (Pascal's Triangle):*
1. `choose_symm_explicit`: C(n,k) = C(n, n-k)
2. `pascal_identity`: C(n+1, k+1) = C(n,k) + C(n, k+1)
3. `choose_zero`, `choose_self`: Boundary conditions
4. `row_sum`: Σₖ C(n,k) = 2ⁿ

*Fibonacci (Diagonal Sums):*
5. `fibonacci_diagonal_sum`: F_{n+1} = Σ C(i,j) along antidiagonal
6. `fibonacci_recurrence`: F_{n+2} = F_n + F_{n+1}
7. `binet_formula`: F_n = (φⁿ - ψⁿ) / √5
8. `golden_ratio_property`: φ² = φ + 1
9. `golden_sum`, `golden_product`: φ + ψ = 1, φ · ψ = -1

*Clifford Algebra:*
10. `clifford_grade_symmetry`: Grade duality in Cl(N,N)
11. `clifford_total_dim`: dim(Cl(N,N)) = 2^(2N)

*Lucas' Theorem (mod p):*
12. `lucas_one_step`: C(n,k) ≡ C(n%p, k%p) · C(n/p, k/p) (mod p)
13. `lucas_theorem_full`: C(n,k) ≡ ∏ᵢ C(nᵢ, kᵢ) (mod p)
14. `lucas_zero_pattern`: Digit overflow ⟹ p | C(n,k)

*Kummer's Theorem (prime power divisibility):*
15. `kummer_theorem`: ν_p(C(n+k,k)) = #{carries in n+k base p}
16. `kummer_theorem_choose`: ν_p(C(n,k)) = #{carries in k+(n-k) base p}
17. `kummer_prime_power`: ν_p(C(p^n,k)) = n - ν_p(k)
18. `prime_divides_middle_choose`: p | C(p^n, k) for 0 < k < p^n

*Legendre's Formula (factorial prime powers):*
19. `legendre_formula`: ν_p(n!) = Σᵢ floor(n/pⁱ)
20. `legendre_digit_sum`: (p-1)·ν_p(n!) = n - s_p(n)
21. `legendre_factorial_mul`: ν_p((p·n)!) = ν_p(n!) + n
22. `legendre_factorial_prime_pow`: ν_p((p^n)!) = Σᵢ pⁱ
23. `legendre_upper_bound`: ν_p(n!) ≤ n/(p-1)
24. `legendre_divisibility`: p^r | n! ⟺ r ≤ Σᵢ floor(n/pⁱ)

*Wilson's Theorem (prime characterization):*
25. `wilsons_lemma`: (p-1)! ≡ -1 (mod p) for prime p
26. `wilson_converse`: (n-1)! ≡ -1 (mod n) ∧ n ≠ 1 ⟹ n prime
27. `wilson_iff_prime`: n ≠ 1 ⟹ (n prime ⟺ (n-1)! ≡ -1 (mod n))

*Fermat's Little Theorem (prime power congruences):*
28. `fermat_little_full`: x^p = x in ZMod p
29. `fermat_little`: a^{p-1} = 1 for nonzero a : ZMod p
30. `fermat_little_units`: a^{p-1} = 1 for units a : (ZMod p)ˣ
31. `fermat_little_nat`: n^{p-1} ≡ 1 (mod p) for n coprime to p
32. `fermat_little_int`: n^{p-1} ≡ 1 (mod p) for integers coprime to p
33. `fermat_euler`: x^{φ(n)} = 1 for units in (ZMod n)ˣ
34. `fermat_euler_nat`: x^{φ(n)} ≡ 1 (mod n) for x coprime to n
35. `fermat_order_divides`: orderOf u ∣ (p - 1) for units in (ZMod p)ˣ

*Multiplicative (Möbius):*
36. `moebius_one`: μ(1) = 1
37. `moebius_prime`: μ(p) = -1 for prime p
38. `moebius_multiplicative`: μ(mn) = μ(m)μ(n) for coprime m,n
39. `moebius_zeta_convolution`: μ * ζ = 1 (Dirichlet convolution)
40. `moebius_inversion`: The inversion formula

*Euler Product (Sum ↔ Product):*
41. `euler_product_completely_multiplicative`: ∏' p, (1-f(p))⁻¹ = Σ' n, f(n)
42. `euler_product_multiplicative`: ∏' p, Σ' e, f(p^e) = Σ' n, f(n)

**Connection to Riemann Project:**
The numerical structure of Pascal's Triangle (binomial coefficients)
appears in the grading of Cl(N,N) and governs the combinatorics of
prime-indexed basis elements. The symmetry C(n,k) = C(n,n-k) manifests
as the duality between k-vectors and (n-k)-vectors in geometric algebra.
-/

end Riemann.Pascal
