# Priority 1: EnergySymmetry.lean:360 - Strict Minimum Upgrade

**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
**Line**: 360
**Theorem**: `symmetry_and_convexity_imply_local_min`

---

## Goal

Prove that E(σ) > E(1/2) for all σ ≠ 1/2 in a neighborhood (upgrade from ≤ to <).

## Current State

The proof has established:
1. `h_le : f σ ≤ f (1/2)` - local minimum (via second derivative test)
2. `h_cont : ContinuousAt f (1/2)` - continuity
3. `h_deriv_zero : deriv f (1/2) = 0` - critical point (from symmetry)
4. `h_convex : deriv (deriv f) (1/2) > 0` - positive second derivative (hypothesis)

## Proof Strategy (Documented in Code)

```
1. Assume f(σ) = f(1/2) for some σ ≠ 1/2 (contradiction)
2. By Rolle's theorem: ∃ c strictly between σ and 1/2 with f'(c) = 0
3. Since f'' > 0 on a neighborhood, f' is strictly increasing
4. Since f'(1/2) = 0 and f' is strictly increasing, 1/2 is the ONLY zero
5. But c ≠ 1/2 and f'(c) = 0 - contradiction
```

## Mathlib Lemmas Needed

```lean
-- Rolle's theorem
exists_deriv_eq_zero : ContinuousOn f (Icc a b) → DifferentiableOn ℝ f (Ioo a b) →
  f a = f b → ∃ c ∈ Ioo a b, deriv f c = 0

-- Strict monotonicity from positive derivative
strictMonoOn_of_deriv_pos : Convex ℝ s → ContinuousOn f s →
  (∀ x ∈ interior s, 0 < deriv f x) → StrictMonoOn f s
```

## Blocker

The proof needs `ContDiff ℝ 2 f` (C² regularity) to derive:
- `StrictMonoOn (deriv f)` from `∀ x, deriv (deriv f) x > 0`

## Resolution Options

### Option A: Add ContDiff hypothesis
Add to theorem signature:
```lean
(h_C2 : ContDiff ℝ 2 f)
```
Then apply:
```lean
have h_deriv_strict_mono : StrictMonoOn (deriv f) (Ioo (1/2 - δ) (1/2 + δ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact (h_C2.continuous_deriv one_le_two).continuousOn
  · intro x hx
    simp only [interior_Ioo] at hx
    -- Use h_convex extended to neighborhood
    sorry
```

### Option B: Prove ZetaEnergy is C²
```lean
-- ZetaEnergy t σ = ‖riemannXi(σ + t*I)‖²
-- riemannXi is entire (analytic everywhere)
-- normSq of analytic function is smooth (C∞)

lemma ZetaEnergy_contDiff (t : ℝ) : ContDiff ℝ 2 (fun σ => ZetaEnergy t σ) := by
  -- riemannXi is Differentiable (entire)
  have h_xi : Differentiable ℂ riemannXi := differentiable_riemannXi
  -- The composition σ ↦ (σ : ℂ) + t*I is smooth
  -- normSq = re² + im² of a smooth function is smooth
  sorry
```

### Option C: Direct approach without C²
Use the proven local minimum and a different argument:
```lean
-- If f has a non-strict local minimum at x₀ with f''(x₀) > 0,
-- then the minimum is actually strict.
-- This is a direct consequence of the second derivative test.

-- Apply isLocalMin_of_deriv_deriv_pos from Mathlib.Analysis.Calculus.DerivativeTest
```

## Recommended Approach

Try **Option C** first:
```lean
-- The isLocalMin_of_deriv_deriv_pos gives IsStrictLocalMin under:
-- 1. f is C² at x₀
-- 2. f'(x₀) = 0
-- 3. f''(x₀) > 0

-- Check if this is in Mathlib 4.27:
import Mathlib.Analysis.Calculus.DerivativeTest

-- Look for: isStrictLocalMin_of_deriv_eq_zero_of_deriv_deriv_pos
```

## Code Location Context

Lines 295-360 in EnergySymmetry.lean contain:
- The proof setup with `set f := fun σ => ZetaEnergy t σ`
- Continuity proof `h_cont`
- Local minimum proof `h_le` using `isLocalMin_of_deriv_deriv_pos`
- The remaining sorry at line 360

---

## Test After Fixing

After implementing a fix, the build should pass:
```bash
lake build Riemann.ProofEngine.EnergySymmetry
```

The theorem `symmetry_and_convexity_imply_local_min` is used by `convexity_implies_norm_strict_min` (line 369).
