# Plan: trace_tail_bounded (Option A - Full Analysis)

**STATUS: ⚠️ MATHEMATICAL ISSUE DISCOVERED**

---

## Problem Statement

```lean
theorem trace_tail_bounded
    (N : ℕ) (h_large : 1000 ≤ N)
    (t : ℝ) (h_t : 0 < t) :
    ∃ C : ℝ, ∀ primes : List ℕ, (∀ p ∈ primes, N < p ∧ Nat.Prime p) →
      |CliffordRH.rotorTrace (1/2) t primes| ≤ C * Real.sqrt N * Real.log N
```

---

## Mathematical Analysis

### The Claim
For fixed N, there exists C such that for ALL finite lists of primes > N:
|trace| ≤ C * √N * log N

### Issue: This appears FALSE

**Why**: The trace includes `Σ log(p) * p^(-1/2)` (after removing |cos| ≤ 1).

The sum `Σ_{p prime} log(p)/√p` **diverges** (like prime harmonic series at σ=1/2).

So for any fixed C:
- Take a long enough list of primes p₁, p₂, ..., p_k all > N
- The partial sum `Σᵢ log(pᵢ)/√pᵢ` can exceed C * √N * log N

**The theorem as stated has no valid C for arbitrarily large lists.**

---

## Correct Statements (Options)

### Option A1: Bound depends on list
```lean
∀ primes : List ℕ, (∀ p ∈ primes, N < p ∧ Nat.Prime p) →
  ∃ C : ℝ, |CliffordRH.rotorTrace (1/2) t primes| ≤ C
```
This is trivially true (take C = |trace| + 1) but not useful.

### Option A2: Bound the rate of decay (integral comparison)
The SUM from N to M is bounded by the INTEGRAL:
```lean
∑_{N < p ≤ M, p prime} log(p)/√p ≤ ∫_N^M log(x)/√x dx = O(√M log M - √N log N)
```
This bounds the partial sum but requires knowing M.

### Option A3: Use prime counting function
By PNT: `Σ_{p ≤ x} log(p)/√p ~ 2√x` (Mertens-like result)
The tail from N: `Σ_{p > N} log(p)/√p = divergent - partial = ∞`
But for finite M: `Σ_{N < p ≤ M} log(p)/√p = O(√M - √N)`

---

## What the RH proof actually needs

Looking at context, `trace_tail_bounded` is meant to bound the error from truncating an infinite prime sum.

For the RH proof to work, we need:
1. For FIXED large prime list (e.g., primes below 7920): trace is computable
2. The ERROR from missing primes > max(list) is controllable

**Better formulation**:
```lean
theorem trace_error_bound (N M : ℕ) (h_N_large : 1000 ≤ N) (h_NM : N < M) (t : ℝ) :
    |CliffordRH.rotorTrace (1/2) t (primesInRange N M)| ≤ 4 * (Real.sqrt M - Real.sqrt N)
```
This bounds the contribution from primes in [N, M] interval.

---

## Recommendation

**The current theorem statement is mathematically incorrect.** Options:

1. **Fix the statement**: Change to bound partial sums with explicit M
2. **Add as hypothesis**: Document what's actually assumed
3. **Delete as unused**: The theorem isn't referenced elsewhere

### Recommended fix:
```lean
/-- Bound on trace from primes in a finite range [N, M] -/
theorem trace_range_bounded (N M : ℕ) (h_large : 1000 ≤ N) (h_lt : N ≤ M) (t : ℝ) :
    ∀ primes : List ℕ, (∀ p ∈ primes, N ≤ p ∧ p ≤ M ∧ Nat.Prime p) →
      |CliffordRH.rotorTrace (1/2) t primes| ≤ 4 * Real.sqrt M * Real.log M
```
This IS provable using:
- |cos| ≤ 1
- Σ_{N≤p≤M} log(p)/√p ≤ Σ_{N≤n≤M} log(n)/√n ≤ ∫_N^{M+1} log(x)/√x dx

---

## Mathlib Lemmas Available

| Lemma | Location | Purpose |
|-------|----------|---------|
| `Real.abs_cos_le_one` | Trigonometric/Deriv | Bound |cos(x)| ≤ 1 |
| `Finset.abs_sum_le_sum_abs` | BigOperators/Group | |Σf| ≤ Σ|f| |
| `AntitoneOn.sum_le_integral_Ico` | SumIntegralComparisons | Sum ≤ Integral |
| `integral_log_div_sqrt` | (needs derivation) | ∫ log(x)/√x dx |

---

## Decision Needed

Before implementing, please choose:

1. **Fix statement** to bound finite ranges → provable but different theorem
2. **Add as hypothesis** → documents assumption explicitly
3. **Mark as false** → add comment explaining mathematical issue
4. **Delete** → not used elsewhere anyway

---

## TraceAtFirstZero Summary

| Line | Theorem | Status | Recommendation |
|------|---------|--------|----------------|
| 263 | `trace_negative_at_first_zero` | BLOCKED | Needs interval arithmetic |
| 295 | `trace_tail_bounded` | **FALSE** | Fix statement or delete |
| 311 | `trace_monotone_from_large_set` | FALSE | Already marked deprecated |
