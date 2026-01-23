# AI2 API Failures - Mathlib 4.27 Reference

**Last Updated**: 2026-01-22
**Purpose**: Document failed API calls so AI2 can learn correct Mathlib 4.27 patterns

---

## DiophantineGeometry.lean

### sum_split_three (line 39)

**ATTEMPTED**:
```lean
rw [h_union, Finset.sum_union h_disj_total, Finset.sum_union h_disj_3]
```

**FAILED**: Pattern mismatch - union associativity
- `s_pos ∪ s_neg ∪ s_zero` is `(s_pos ∪ s_neg) ∪ s_zero` (left-associative)
- But the rewrite expected `s_pos ∪ (s_neg ∪ s_zero)`

**CORRECT APPROACH**:
```lean
-- Use Finset.sum_filter_add_sum_filter_not or handle associativity explicitly
rw [Finset.union_assoc] -- if needed
-- Or use: Finset.sum_filter_add_sum_filter_not
```

---

### fta_all_exponents_zero (line 53)

**ATTEMPTED**:
```lean
simp only [Real.exp_sum, Real.exp_mul, Real.exp_log_natCast] at h_exp
```

**FAILED**: `Real.exp_log_natCast` doesn't exist

**CORRECT API**:
```lean
-- For Real.exp (Real.log (n : ℕ)) = n, use:
Real.exp_log  -- requires x > 0
Nat.cast_pos  -- to show (n : ℝ) > 0 for n > 0
```

---

**ATTEMPTED**:
```lean
exact Finset.not_mem_empty p
```

**FAILED**: `Finset.not_mem_empty` doesn't exist

**CORRECT API**:
```lean
-- In Mathlib 4.27, use:
Finset.not_mem_empty  -- IS the correct lemma, but called differently
-- Or use: absurd hp (Finset.not_mem_empty p)
-- Or use: simp at hp (if hp : p ∈ ∅)
```

---

**ATTEMPTED**:
```lean
apply eq_neg_of_add_eq_zero_left at h_sum
```

**FAILED**: `eq_neg_of_add_eq_zero` doesn't exist

**CORRECT API**:
```lean
-- In Mathlib 4.27, use:
neg_eq_of_add_eq_zero_left  -- or
add_eq_zero_iff_neg_eq      -- or
eq_neg_of_add_eq_zero       -- check exact spelling
```

---

### dominant_prevents_closure_norm (line 70)

**ATTEMPTED**:
```lean
(h_sum : ∑ p ∈ S, ((-Real.log p / (p : ℝ) ^ σ) : ℂ) * cexp (θ p * I) = 0)
```

**FAILED**: `HPow ℂ ℝ` type class not found

**CAUSE**: When coercing `((-Real.log p / (p : ℝ) ^ σ) : ℂ)`, Lean tries to interpret parts as ℂ first

**CORRECT APPROACH**:
```lean
-- Define helper function to compute in ℝ first:
private def coeff (p : ℕ) (σ : ℝ) : ℝ := -Real.log p / (p : ℝ) ^ σ
-- Then use:
(h_sum : ∑ p ∈ S, (coeff p σ : ℂ) * Complex.exp ((θ p : ℂ) * Complex.I) = 0)
```

---

## ArithmeticAxioms.lean

### prod_prime_pow_ne_zero (line 23)

**ATTEMPTED**:
```lean
apply Finset.prod_ne_zero
exact Nat.pow_ne_zero_iff.mpr (Nat.Prime.ne_zero ...)
```

**FAILED**:
- `Finset.prod_ne_zero` doesn't exist
- `Nat.pow_ne_zero_iff.mpr` doesn't exist

**CORRECT API**:
```lean
-- For Finset.prod_ne_zero, use:
Finset.prod_ne_zero_iff  -- exists, use .mpr

-- For Nat.pow_ne_zero, use:
pow_ne_zero n (Nat.Prime.ne_zero hp)  -- direct application
-- Or: Nat.pos_pow_of_pos for positivity
```

---

## LinearIndependenceSolved.lean

### clear_denominators (line 37)

**ATTEMPTED**:
```lean
rw [Rat.mul_comm, Rat.mul_natCast_eq_coe_num_of_den_dvd _ _ h_dvd]
```

**FAILED**: `Rat.mul_natCast_eq_coe_num_of_den_dvd` doesn't exist

**CORRECT API**:
```lean
-- For clearing denominators in ℚ, use:
Rat.mul_den_eq_num       -- q * q.den = q.num
Rat.num_div_den          -- q = q.num / q.den
-- Or construct explicitly using Rat.divInt
```

---

### log_primes_linear_independent (line 55)

**ATTEMPTED**:
```lean
rw [linearIndependent_iff']
-- then use ∑ g p * log p = 0
```

**FAILED**: `linearIndependent_iff'` uses smul (•), not mul (*)

**CORRECT API**:
```lean
-- linearIndependent_iff' gives: ∑ g i • v i = 0 → ∀ i, g i = 0
-- For ℚ acting on ℝ, (q : ℚ) • (x : ℝ) = (q : ℝ) * x
-- Need to convert between • and * explicitly:
simp only [smul_eq_mul]  -- converts • to * when applicable
```

---

## ClusterBound.lean

### c2_stability_transfer (line 75)

**ATTEMPTED**:
```lean
rw [Filter.Eventually, Filter.mem_nhds_iff] at h_approx h_g_convex
```

**FAILED**: `Filter.mem_nhds_iff` doesn't exist

**CORRECT API**:
```lean
-- In Mathlib 4.27, use:
Metric.eventually_nhds_iff  -- for metric spaces
-- Or use Filter.eventually_iff with appropriate filter basis
-- Or use: Filter.Eventually.exists_mem
```

---

## CalculusAxioms.lean

### taylor_second_order (line 21)

**ATTEMPTED**:
```lean
deriv_comp_sub_const  -- for d/dx f(x - c) = f'(x - c)
```

**FAILED**: `deriv_comp_sub_const` doesn't exist

**CORRECT API**:
```lean
-- Use chain rule explicitly:
deriv_comp  -- general chain rule
HasDerivAt.comp  -- for HasDerivAt composition
-- Or: deriv.comp with the appropriate inner function
```

---

### effective_convex_implies_min_proven (line 33)

**ATTEMPTED**:
```lean
have hd_sq_pos : d ^ 2 > 0 := sq_pos_of_ne_zero d hd_ne
```

**FAILED**: Wrong argument order

**CORRECT API**:
```lean
-- sq_pos_of_ne_zero takes just the proof, not the element:
sq_pos_of_ne_zero hd_ne  -- correct (no explicit d)
```

---

## TraceAtFirstZero.lean

### product_in_corners (line 99)

**ATTEMPTED**:
```lean
constructor <;> simp only [le_min_iff, min_le_iff]
nlinarith [sq_nonneg (x - a), sq_nonneg (x - b), ...]
```

**FAILED**: simp made no progress, nlinarith couldn't find proof

**CORRECT APPROACH**:
```lean
-- For interval arithmetic multiplication bounds:
-- The extrema of x*y on [a,b]×[c,d] occur at corners
-- Need case analysis on signs of a, b, c, d
-- Or use: mul_le_mul variants with appropriate sign hypotheses
```

---

## General Patterns

### Finset Membership
```lean
-- OLD: Finset.not_mem_empty p
-- NEW: use simp or absurd pattern
```

### Filter Eventually
```lean
-- OLD: Filter.mem_nhds_iff
-- NEW: Metric.eventually_nhds_iff or Filter.Eventually.exists_mem
```

### Rational Arithmetic
```lean
-- Clearing denominators:
-- Use Rat.num_div_den, Rat.mul_den_eq_num
-- NOT: Rat.mul_natCast_eq_coe_num_of_den_dvd
```

### Power Nonzero
```lean
-- OLD: Nat.pow_ne_zero_iff.mpr
-- NEW: pow_ne_zero n h where h : base ≠ 0
```

### Linear Independence
```lean
-- linearIndependent_iff' uses smul (•)
-- For scalar multiplication as multiplication, use smul_eq_mul
```

---

## Tips for AI2

1. **Always check lemma existence** with `#check` before using
2. **Use `exact?` or `apply?`** to find correct lemmas
3. **Test small proof fragments** before combining
4. **Document failures** with exact error messages
5. **Prefer `simp` over manual rewrites** when possible - simp knows current API
