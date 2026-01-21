import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic

noncomputable section
open Real Complex BigOperators Filter Topology

namespace OutstandingProofs

/-!
# Outstanding Proofs: Remaining Sorries for ChiralPath

**STATUS**: 4 sorries remaining (reduced from original 9)

This file documents the remaining gaps in the IsChiral proof via Diophantine analysis.
The main proof is now in `Riemann/ProofEngine/ChiralPath.lean`.

## Summary of Remaining Work

| Sorry | Location | Description | Difficulty |
|-------|----------|-------------|------------|
| 1 | Job 1 | FTA application for z_p = 0 | MEDIUM |
| 2 | Job 2a | Norm calculation for dominant term | EASY |
| 3 | Job 2b | Case analysis dominant vs Baker | MEDIUM |
| 4 | Job 4 | Infinite sum limit argument | HARD |

## Fully Proven Components (in ProofEngine/)
- `ErgodicTimeAverages.lean` - Oscillating integrals vanish (0 sorries)
- `NumberTheoryFTA.lean` - Log ratio irrationality via FTA (0 sorries)
- `GeometricClosure.lean` - Polygon inequality (0 sorries)
- `BakerRepulsion.lean` - Trajectory repulsion (1 axiom, 0 sorries)
- `ChiralPath.lean` - Main assembly (4 sorries)
-/

-- ==============================================================================
-- SORRY 1: FTA APPLICATION
-- ==============================================================================

/-!
## Sorry 1: Fundamental Theorem of Arithmetic Application

**Context**: In `log_primes_linear_independent`, after establishing
  ∑ p ∈ s, (z p : ℝ) * log p = 0
where z : Prime → ℤ, we need to prove all z p = 0.

**Strategy**:
1. Exponentiate: ∏ p^{z_p} = 1
2. Split into positive/negative exponents
3. Use unique factorization: disjoint prime products equal ⟹ both trivial

**Mathlib tools needed**:
- `Nat.factorization_eq_iff`
- `Nat.Prime.factorization_self`
- `Finsupp.single_eq_single_iff`
-/

theorem fta_all_exponents_zero (s : Finset {x : ℕ // x.Prime}) (z : {x : ℕ // x.Prime} → ℤ)
    (h_sum : ∑ p ∈ s, (z p : ℝ) * Real.log (p : ℕ) = 0) :
    ∀ p ∈ s, z p = 0 := by
  intro p hp
  -- Step 1: From h_sum, we get exp(sum) = 1
  -- Step 2: exp(sum) = ∏ p^{z_p}
  -- Step 3: Split positive and negative

  -- If z p > 0 for some p, then p^{z_p} appears on LHS
  -- If z q < 0 for some q, then q^{|z_q|} appears on RHS
  -- LHS = RHS requires same prime factorization
  -- But p ≠ q and both are prime, contradiction unless exponents = 0

  by_contra h_ne
  -- Detailed FTA argument
  sorry

-- ==============================================================================
-- SORRY 2: NORM CALCULATION FOR DOMINANT TERM
-- ==============================================================================

/-!
## Sorry 2: Dominant Term Norm Calculation

**Context**: In `dominant_term_prevents_closure`, we need to show
that if |c_dom| > Σ|c_rest|, then the sum cannot be zero.

**Strategy**:
1. Split sum: S = {p_dom} ∪ (S \ {p_dom})
2. If sum = 0, then c_dom·e^{iθ} = -Σ(rest)
3. Take norms: |c_dom| = |Σ(rest)| ≤ Σ|rest|
4. Contradiction with dominance hypothesis

**Mathlib tools needed**:
- `norm_sum_le` (triangle inequality)
- `norm_mul`, `Complex.norm_exp_ofReal_mul_I`
-/

theorem dominant_prevents_closure_norm (σ : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (p_dom : ℕ) (h_mem : p_dom ∈ S)
    (h_dominant : |(-Real.log p_dom / (p_dom : ℝ) ^ σ)| >
                  ∑ p ∈ S.erase p_dom, |(-Real.log p / (p : ℝ) ^ σ)|)
    (θ : ℕ → ℝ)
    (h_sum : ∑ p ∈ S, ((-Real.log p / (p : ℝ) ^ σ) : ℂ) * cexp (θ p * I) = 0) :
    False := by
  -- Split the sum
  have h_split := Finset.add_sum_erase S
    (fun p => ((-Real.log p / (p : ℝ) ^ σ) : ℂ) * cexp (θ p * I)) h_mem
  rw [h_sum] at h_split
  -- dominant + tail = 0 ⟹ dominant = -tail
  have h_eq : ((-Real.log p_dom / (p_dom : ℝ) ^ σ) : ℂ) * cexp (θ p_dom * I) =
              -(∑ p ∈ S.erase p_dom, ((-Real.log p / (p : ℝ) ^ σ) : ℂ) * cexp (θ p * I)) := by
    linarith [h_split]
  -- Take norms
  have h_norm_eq : ‖((-Real.log p_dom / (p_dom : ℝ) ^ σ) : ℂ) * cexp (θ p_dom * I)‖ =
                   ‖∑ p ∈ S.erase p_dom, ((-Real.log p / (p : ℝ) ^ σ) : ℂ) * cexp (θ p * I)‖ := by
    rw [h_eq, norm_neg]
  -- LHS = |c_dom| (since |e^{iθ}| = 1)
  -- RHS ≤ Σ|c_rest| by triangle inequality
  sorry

-- ==============================================================================
-- SORRY 3: CASE ANALYSIS (DOMINANT VS BAKER)
-- ==============================================================================

/-!
## Sorry 3: Case Analysis for General Polygon Impossibility

**Context**: In `zeta_derivative_no_closure`, we need to handle all finite sets.

**Strategy**:
1. For small sets: Check if dominant > tail numerically
2. For large sets: Use Baker's theorem

**Key insight**: For σ = 1/2, the dominant term is always p=2 (smallest prime).
Check: |c_2| = log(2)/√2 ≈ 0.49
       |c_3| = log(3)/√3 ≈ 0.63

So c_3 > c_2! This means the simple dominant argument doesn't immediately work.
We need the full Baker argument for phase frustration.
-/

theorem zeta_no_closure_analysis (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ¬∃ (θ : ℕ → ℝ), (∑ p ∈ S, ((-Real.log p / (p : ℝ) ^ (1/2 : ℝ)) : ℂ) * cexp (θ p * I)) = 0 := by
  -- The phases θ_p in a zero of the zeta derivative are NOT free parameters.
  -- They are locked to t·log(p) for some fixed t.
  -- Baker's theorem shows these constrained phases cannot hit the zero-sum locus.
  sorry

-- ==============================================================================
-- SORRY 4: INFINITE SUM LIMIT
-- ==============================================================================

/-!
## Sorry 4: Infinite Sum Limit Argument

**Context**: In `is_chiral_proven`, we need to pass from finite truncations
to the infinite sum.

**Strategy**:
1. Show ∑' p, |c_p| converges (Dirichlet series at σ > 0)
2. Use dominated convergence: if f_n → f and |f_n| ≤ g with ∫g < ∞
3. Show uniform lower bound on f_n survives in limit

**Key difficulty**: Need to show the lower bound δ_n doesn't shrink to 0.

**Possible approach**:
- Use compactness of the torus
- Apply Weierstrass M-test for uniform convergence
- Show minimum over compact set is achieved and positive
-/

/-- The deriv_coeff series is summable for σ > 0 -/
lemma summable_deriv_coeff (σ : ℝ) (hσ : 0 < σ) :
    Summable (fun p : {n : ℕ // n.Prime} => |(-Real.log p / (p : ℕ) ^ σ)|) := by
  -- log(p)/p^σ ≤ C·p^{-σ/2} for large p (since log grows slower than any power)
  -- Series ∑ p^{-σ/2} converges for σ > 0 (prime zeta function)
  sorry

theorem infinite_sum_preserves_bound (σ : ℝ) (hσ : σ = 1/2) :
    ∃ δ > 0, ∀ t : ℝ, ‖∑' (p : {n : ℕ // n.Prime}),
      ((-Real.log p / (p : ℕ) ^ σ) : ℂ) * cexp (t * Real.log p * I)‖ ≥ δ := by
  -- This is the most challenging step.
  -- Need to combine:
  -- 1. Summability (for well-defined infinite sum)
  -- 2. Uniform lower bounds on truncations (from trajectory_avoids_zero)
  -- 3. Limit argument preserving the bound
  sorry

-- ==============================================================================
-- DEPENDENCIES AND NEXT STEPS
-- ==============================================================================

/-!
## Proof Dependencies

```
Mathlib.Nat.Factorization ────► Sorry 1 (FTA application)
                                     │
                                     ▼
                         log_primes_linear_independent
                                     │
                    ┌────────────────┴────────────────┐
                    │                                 │
                    ▼                                 ▼
              Sorry 2 (norms)                  Baker Axiom
                    │                                 │
                    ▼                                 ▼
              Sorry 3 (cases)              trajectory_avoids_zero
                    │                                 │
                    └─────────────┬───────────────────┘
                                  ▼
                            Sorry 4 (limits)
                                  │
                                  ▼
                           is_chiral_proven
```

## Recommended Order of Attack

1. **Sorry 2** (EASY): Direct norm calculation with triangle inequality
2. **Sorry 1** (MEDIUM): FTA via Mathlib's factorization API
3. **Sorry 3** (MEDIUM): Reduces to Baker once Sorry 1 is done
4. **Sorry 4** (HARD): Requires careful limit argument with summability

## Notes for AI Agents

- Sorry 1 requires `Nat.factorization` machinery from Mathlib
- Sorry 2 is mostly bookkeeping with `norm_sum_le`
- Sorry 3 can use the hypothesis that phases are constrained (not free)
- Sorry 4 may require additional lemmas about uniform convergence
-/

end OutstandingProofs
