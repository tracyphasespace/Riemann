# Priority 3-5: ClusterBound.lean Sorries

**File**: `Riemann/ProofEngine/ClusterBound.lean`
**Lines**: 139, 167, 187

---

## Overview

ClusterBound provides the bridge between:
- Analytic energy (ZetaEnergy based on riemannXi)
- Finite rotor sums (rotorSumNormSq)

The key insight: if the finite sum approximates the analytic energy closely enough, minima transfer.

---

## Priority 3: Line 139 - c2_stability_transfer

### Statement
```lean
lemma c2_stability_transfer {f g : ℝ → ℝ} {x₀ ε : ℝ} (hε : 0 < ε)
    (h_approx : ∀ᶠ x in 𝓝 x₀, |f x - g x| < ε)
    (h_g_deriv_zero : deriv g x₀ = 0)
    (h_g_convex : ∀ᶠ x in 𝓝 x₀, deriv (deriv g) x > 2 * ε)
    (h_g_diff2 : ContDiffAt ℝ 2 g x₀) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → x ≠ x₀ → f x > f x₀
```

### Mathematical Idea
By Taylor: g(x) ≈ g(x₀) + g''(c)(x-x₀)²/2.
Since g'' > 2ε: g(x) - g(x₀) > ε(x-x₀)² for small |x-x₀|.
Since |f-g| < ε: f(x) > f(x₀) + ε(x-x₀)² - 2ε.

### Known Issue
The predicate has a scaling problem. Need g'' > 2ε/δ² (not just > 2ε).

### Proof Approach
```lean
-- 1. Extract neighborhoods from Filter.Eventually
rw [Filter.Eventually, Filter.mem_nhds_iff] at h_approx h_g_convex
obtain ⟨s₁, hs₁_sub, hs₁_open, hx₀_s₁⟩ := h_approx
obtain ⟨s₂, hs₂_sub, hs₂_open, hx₀_s₂⟩ := h_g_convex

-- 2. Take δ from the intersection of neighborhoods
obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.isOpen_iff.mp hs₁_open x₀ hx₀_s₁
obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.isOpen_iff.mp hs₂_open x₀ hx₀_s₂

-- 3. Apply Taylor's theorem to g
-- g(x) = g(x₀) + g'(x₀)(x-x₀) + g''(c)(x-x₀)²/2
-- Since g'(x₀) = 0: g(x) - g(x₀) = g''(c)(x-x₀)²/2 ≥ ε(x-x₀)² (since g'' > 2ε)

-- 4. Combine with approximation bound
-- f(x) - f(x₀) = (f(x) - g(x)) + (g(x) - g(x₀)) + (g(x₀) - f(x₀))
--              > -ε + ε(x-x₀)² - ε = ε[(x-x₀)² - 2]
-- For (x-x₀)² > 2, this is positive. But we need this for ALL x ≠ x₀...
```

### Resolution
The condition needs refinement. Either:
1. Change hypothesis to `g'' > C/δ²` for some C depending on ε
2. Or require δ-dependent ε: `ε < δ² * g_min_second_deriv / 4`

---

## Priority 4: Line 167 - norm_strict_min_at_half_proven

### Statement
```lean
theorem norm_strict_min_at_half_proven (t : ℝ) (primes : List ℕ)
    (_h_large : primes.length > 1000)
    (h_approx : AdmissibleNormApproximation t primes) :
    CliffordRH.NormStrictMinAtHalf t primes
```

### Dependencies
- Depends on `c2_stability_transfer` (line 139)
- Uses `AdmissibleNormApproximation` predicate

### Proof Sketch
```lean
-- 1. Extract E, h_close, h_dom from h_approx
obtain ⟨E, hE_pos, h_close, h_dom⟩ := h_approx

-- 2. Apply c2_stability_transfer with:
--    f := rotorSumNormSq
--    g := ZetaEnergy
--    x₀ := 1/2
--    ε := E

-- 3. The AdmissibleNormApproximation ensures the hypotheses of c2_stability_transfer
```

---

## Priority 5: Line 187 - zero_implies_norm_min_proven

### Statement
```lean
theorem zero_implies_norm_min_proven (s : ℂ) (_h_zero : riemannZeta s = 0)
    (_h_strip : 0 < s.re ∧ s.re < 1)
    (primes : List ℕ)
    (_h_large : primes.length > 1000) :
    CliffordRH.ZeroHasMinNorm s.re s.im primes
```

### Mathematical Idea
At a zeta zero:
- Analytic energy E = 0 (minimum possible)
- Finite sum is close to E
- Therefore finite sum is small (approximately 0)

### Proof Approach
```lean
-- 1. At zero s, ZetaEnergy s.im s.re = 0 (uses zero_implies_energy_min)
have h_energy_zero : EnergySymmetry.ZetaEnergy s.im s.re = 0 :=
  zero_implies_energy_min s h_zero h_strip

-- 2. Finite sum approximates ZetaEnergy within error E
-- rotorSumNormSq σ t primes ≈ ZetaEnergy t σ ± E

-- 3. Away from s.re, ZetaEnergy grows (convexity)
-- Therefore rotorSumNormSq also grows away from s.re
```

---

## Mathlib Lemmas Reference

```lean
-- Taylor expansion
taylor_mean_remainder_lagrange_iteratedDeriv

-- Neighborhood extraction
Filter.Eventually
Filter.mem_nhds_iff
Metric.isOpen_iff

-- Continuity/Differentiability
ContDiffAt.continuousAt
ContDiffAt.differentiableAt
```

---

## Test Command

```bash
lake build Riemann.ProofEngine.ClusterBound
```
