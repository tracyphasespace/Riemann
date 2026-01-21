/-!
# Job 4: Chirality Final Assembly
# Agent Task: Prove IsChiral at σ = 1/2

## Context
This combines:
- Job 1: Linear independence (DONE - in DiophantineGeometry.lean)
- Job 2: Trajectory avoidance (uses Baker's theorem)
- Dominated convergence for infinite sum

## What You Need To Prove
Show that the infinite sum inherits the lower bound from finite truncations.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
open Real Complex BigOperators Filter Topology

namespace Job4

-- GIVEN DEFINITIONS --

/-- The coefficient for prime p at σ = 1/2 -/
def deriv_coeff (σ : ℝ) (p : ℕ) : ℝ := -Real.log p / (p : ℝ) ^ σ

/-- IsChiral: Derivative norm bounded away from zero -/
def IsChiral (σ : ℝ) : Prop :=
  ∃ δ > 0, ∀ t : ℝ, ‖∑' (p : {n : ℕ // n.Prime}),
    (deriv_coeff σ p : ℂ) * cexp (t * Real.log p * I)‖ ≥ δ

-- GIVEN: From trajectory_avoids_zero (uses Baker axiom)
axiom trajectory_avoids_zero_finite (σ : ℝ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hS_ne : S.Nonempty) :
    ∃ δ > 0, ∀ t : ℝ, ‖∑ p ∈ S, (deriv_coeff σ p : ℂ) * cexp (t * Real.log p * I)‖ ≥ δ

-- HELPER LEMMAS TO PROVE --

/-- The series converges absolutely for σ > 1/2 -/
lemma series_summable (σ : ℝ) (hσ : σ > 1/2) (t : ℝ) :
    Summable fun (p : {n : ℕ // n.Prime}) =>
      ‖(deriv_coeff σ p : ℂ) * cexp (t * Real.log p * I)‖ := by
  -- log(p)/p^σ is summable for σ > 1/2 (Dirichlet series convergence)
  sorry -- YOUR TASK: Complete

/-- Tail of series is small -/
lemma tail_bound (σ : ℝ) (hσ : σ > 1/2) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ t : ℝ,
      ‖∑' (p : {n : ℕ // n.Prime ∧ n > N}),
        (deriv_coeff σ p.1 : ℂ) * cexp (t * Real.log p.1 * I)‖ < ε := by
  -- Convergent series have arbitrarily small tails
  sorry -- YOUR TASK: Complete

/-- The uniform bound survives the infinite limit -/
lemma infinite_inherits_bound (σ : ℝ) (hσ : σ = 1/2) :
    ∃ δ > 0, ∀ t : ℝ,
      ‖∑' (p : {n : ℕ // n.Prime}),
        (deriv_coeff σ p : ℂ) * cexp (t * Real.log p * I)‖ ≥ δ := by
  -- Strategy:
  -- 1. Get δ from trajectory_avoids_zero_finite for large S
  -- 2. Get ε < δ/2 from tail_bound
  -- 3. Triangle inequality: ‖infinite‖ ≥ ‖finite‖ - ‖tail‖ ≥ δ - ε > δ/2
  sorry -- YOUR TASK: Complete

-- MAIN THEOREM --

/--
**The Main Goal**: IsChiral at σ = 1/2.
-/
theorem is_chiral_proven (σ : ℝ) (hσ : σ = 1/2) : IsChiral σ := by
  -- Use infinite_inherits_bound
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := infinite_inherits_bound σ hσ
  exact ⟨δ, hδ_pos, hδ_bound⟩

end Job4
