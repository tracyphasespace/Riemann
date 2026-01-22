# EnergySymmetry.lean - LLM Review Request

**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
**Lean Version**: 4.27.0-rc1 / Mathlib v4.27.0-rc1
**Sorries**: 4
**Priority**: HIGH - Critical path to master theorem

---

## Mathematical Context

This file establishes the **energy minimum principle** for the Riemann Hypothesis proof.

**Key Insight**: The Riemann Xi function ξ(s) = s(1-s)Λ₀(s) - 1 satisfies:
1. **Functional equation**: ξ(s) = ξ(1-s)
2. **Conjugate symmetry**: ξ(conj s) = conj(ξ(s))

This implies the "energy" E(σ,t) = ‖ξ(σ + it)‖² satisfies:
- E(σ,t) = E(1-σ,t) (reflection symmetry)
- E'(1/2) = 0 (critical point by symmetry)

If E''(1/2) > 0 (convexity hypothesis), then σ=1/2 is a strict local minimum.

---

## File Structure

```lean
-- Line 48: Definition of riemannXi using completedRiemannZeta₀
def riemannXi (s : ℂ) : ℂ := s * (1 - s) * completedRiemannZeta₀ s - 1

-- Line 54: Functional equation (PROVEN)
theorem riemannXi_symmetric (s : ℂ) : riemannXi s = riemannXi (1 - s)

-- Line 66: Conjugate symmetry (PROVEN)
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s)

-- Line 75: Xi↔Zeta equivalence (2 SORRIES at lines 101, 109)
theorem riemannXi_zero_iff_zeta_zero {s : ℂ} (h_strip : 0 < s.re ∧ s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0

-- Line 126: Energy definition
def ZetaEnergy (t : ℝ) (σ : ℝ) : ℝ := Complex.normSq (riemannXi (σ + t * I))

-- Line 142: Energy symmetry (PROVEN)
theorem zeta_energy_symmetric (t : ℝ) (σ : ℝ) : ZetaEnergy t σ = ZetaEnergy t (1 - σ)

-- Line 180: Generic symmetry → zero derivative (PROVEN)
theorem deriv_zero_of_symmetric {f : ℝ → ℝ} (h_diff : Differentiable ℝ f)
    (h_symm : ∀ x, f x = f (1 - x)) : deriv f (1/2) = 0

-- Line 209: Energy derivative zero at 1/2 (PROVEN)
theorem energy_deriv_zero_at_half (t : ℝ) : deriv (fun σ => ZetaEnergy t σ) (1/2) = 0

-- Line 263: Second derivative test (1 SORRY at line 296)
theorem symmetry_and_convexity_imply_local_min (t : ℝ) (h_convex : EnergyIsConvexAtHalf t) :
    ∃ δ > 0, ∀ σ, σ ≠ 1/2 ∧ |σ - 1/2| < δ → ZetaEnergy t (1/2) < ZetaEnergy t σ

-- Line 305: Bridge to finite sums (1 SORRY at line 315)
theorem convexity_implies_norm_strict_min (t : ℝ) (primes : List ℕ)
    (_h_large : primes.length > 1000) (_h_convex : EnergyIsConvexAtHalf t) :
    CliffordRH.NormStrictMinAtHalf t primes
```

---

## Sorry #1: Line 296 - Second Derivative Test (HIGHEST PRIORITY)

**Goal**: Prove σ=1/2 is a strict local minimum given E'(1/2)=0 and E''(1/2)>0.

**What we have**:
```lean
h_deriv_zero : deriv (fun σ => ZetaEnergy t σ) (1/2) = 0
h_convex : deriv (deriv (fun σ => ZetaEnergy t σ)) (1/2) > 0
```

**What we need to show**:
```lean
∃ δ > 0, ∀ σ, σ ≠ 1/2 ∧ |σ - 1/2| < δ → ZetaEnergy t (1/2) < ZetaEnergy t σ
```

**Proof Strategy**:
1. Since E''(1/2) > 0, by continuity ∃ δ > 0 such that E'' > 0 on (1/2-δ, 1/2+δ)
2. E'' > 0 ⟹ E' is strictly increasing on this interval
3. Since E'(1/2) = 0 and E' is strictly increasing:
   - E'(σ) < 0 for σ ∈ (1/2-δ, 1/2)
   - E'(σ) > 0 for σ ∈ (1/2, 1/2+δ)
4. By MVT, for σ ≠ 1/2: E(σ) - E(1/2) = E'(ξ)(σ - 1/2) for some ξ between 1/2 and σ
5. Both cases give E(σ) > E(1/2)

**KEY DISCOVERY - Mathlib has the exact lemma needed!**

```lean
-- From Mathlib.Analysis.Calculus.DerivativeTest (line 202)
theorem isLocalMin_of_deriv_deriv_pos (hf : deriv (deriv f) x₀ > 0) (hd : deriv f x₀ = 0)
    (hc : ContinuousAt f x₀) : IsLocalMin f x₀
```

**This gives us `IsLocalMin`** (non-strict: f(1/2) ≤ f(σ) near 1/2).

**We need `strict` local min** (f(1/2) < f(σ) for σ ≠ 1/2).

**Path to strict minimum**:

`IsLocalMin f a` means `∀ᶠ x in 𝓝 a, f a ≤ f x` (non-strict, from Mathlib).

We need: `∃ δ > 0, ∀ σ ≠ 1/2, |σ - 1/2| < δ → f(1/2) < f(σ)` (strict).

**Two approaches**:

*Approach A (Taylor)*:
1. Get `IsLocalMin` from `isLocalMin_of_deriv_deriv_pos`
2. Suppose for contradiction: ∃ σ ≠ 1/2 arbitrarily close with E(σ) = E(1/2)
3. Taylor: E(σ) = E(1/2) + 0·(σ-1/2) + E''(c)(σ-1/2)²/2 > E(1/2)
4. Contradiction, so minimum is strict

*Approach B (Direct sign analysis)*:
1. E''(1/2) > 0 and continuous ⟹ E'' > 0 on (1/2-δ, 1/2+δ)
2. E' strictly increasing on this interval
3. E'(1/2) = 0, so E' < 0 on (1/2-δ, 1/2) and E' > 0 on (1/2, 1/2+δ)
4. Apply MVT: E(σ) - E(1/2) = E'(ξ)·(σ-1/2) has correct sign ⟹ E(σ) > E(1/2)

**Other relevant Mathlib lemmas**:
```lean
-- For step 2: positive derivative implies strictly increasing
strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) :
    StrictMonoOn f D

-- Continuity of deriv for smooth functions
ContDiff.continuous_deriv : ContDiff ℝ n f → 1 ≤ n → Continuous (deriv f)
```

**Required import**:
```lean
import Mathlib.Analysis.Calculus.DerivativeTest
```

**Main task**: Prove `ContinuousAt (fun σ => ZetaEnergy t σ) (1/2)` - this should be straightforward since ZetaEnergy is a composition of continuous functions.

---

## Sorry #2: Line 315 - C² Approximation Transfer

**Goal**: Transfer the analytic minimum property to finite prime sums.

**Context**: If the analytic energy ZetaEnergy has a strict minimum at σ=1/2, then for sufficiently many primes, the finite rotor sum `rotorSumNormSq` also has a strict minimum there.

**This sorry depends on**: ClusterBound.lean helpers (not yet implemented). Lower priority.

---

## Sorries #3-4: Lines 101, 109 - Xi↔Zeta Equivalence

**Goal**: Prove that in the critical strip, ξ(s)=0 ↔ ζ(s)=0.

**Mathematical Fact**:
- completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s)
- completedRiemannZeta s = π^(-s/2) · Γ(s/2) · ζ(s)

Therefore:
- ξ(s) = s(1-s)·Λ₀(s) - 1 = s(1-s)·Λ(s) + (1-s) + s - 1 = s(1-s)·Λ(s)
- ξ(s) = s(1-s)·π^(-s/2)·Γ(s/2)·ζ(s)

In the critical strip:
- s ≠ 0, s ≠ 1, so s(1-s) ≠ 0
- π^(-s/2) ≠ 0
- Γ(s/2) ≠ 0 (s/2 not a non-positive integer when 0 < s.re < 1)

Therefore ξ(s) = 0 ↔ ζ(s) = 0.

**Blocker**: Mathlib may not have the explicit relationship:
```lean
completedRiemannZeta₀_eq (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta₀ s = completedRiemannZeta s + s⁻¹ + (1 - s)⁻¹
```

**Options**:
1. Find this lemma in Mathlib (search `completedRiemannZeta₀`)
2. Add as axiom if not available
3. Prove from Mathlib's definition of completedRiemannZeta₀

---

## Mathlib Imports Currently Used

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
```

---

## Suggested Approach

**Priority 1**: Attack Sorry #1 (line 296)
- This is pure calculus, no zeta-specific facts needed
- The proof strategy is clear
- Main task: establish C² differentiability of ZetaEnergy

**Priority 2**: Investigate Mathlib for completedRiemannZeta₀ decomposition
- Search: `completedRiemannZeta₀`, `riemannCompletedZeta₀`
- If found, sorries #3-4 become tractable
- If not found, document as axiom requirement

**Priority 3**: Skip sorry #2 for now (depends on other module)

---

## Questions for Review

1. Is there a standard Mathlib approach for the second derivative test that we're missing?
2. Does Mathlib have the completedRiemannZeta₀ decomposition lemma?
3. Is there a simpler way to establish C² differentiability for compositions of analytic functions?

---

*Prepared for external LLM review - 2026-01-21*
