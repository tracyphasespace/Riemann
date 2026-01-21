/-!
# Residues.lean
# Pole Analysis and Domination

This file establishes the analytic behavior of the Zeta function near its poles,
specifically proving that the pole at s=1 (and potential zeros) dominates
bounded holomorphic terms.

References:
- RemainingProofs.lean Lines 160-247
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Complex Filter Topology

namespace Residues

/-!
## Section 1: Helper Lemmas for Continuity and Derivatives
Resolves Line 160: Continuity of derivative of holomorphic function
-/

/-- Helper: The derivative of a holomorphic function is continuous on open sets. -/
lemma holomorphic_deriv_continuous {f : ℂ → ℂ} {s : Set ℂ}
    (h_diff : DifferentiableOn ℂ f s) (h_open : IsOpen s) :
    ContinuousOn (deriv f) s := by
  -- In complex analysis, differentiability implies analyticity (Goursat),
  -- which implies C^∞. Mathlib handles this via DifferentiableOn.deriv.
  have h_deriv_diff : DifferentiableOn ℂ (deriv f) s :=
    DifferentiableOn.deriv h_diff h_open
  exact h_deriv_diff.continuousOn

/-!
## Section 2: Pole Arithmetic
Resolves Line 163: Derivative of pole + holomorphic
-/

/-- Helper: Derivative of a simple pole plus a holomorphic function.
    Computes d/ds (1/(s-ρ) + f(s)). -/
lemma deriv_pole_add_holomorphic {f : ℂ → ℂ} {ρ s : ℂ}
    (h_holo : DifferentiableAt ℂ f s) (h_ne : s ≠ ρ) :
    deriv (fun z => (z - ρ)⁻¹ + f z) s = -(s - ρ)^(-2) + deriv f s := by
  rw [deriv_add]
  · -- Handle the pole part (z - ρ)⁻¹
    rw [deriv_inv_sub_const] -- Mathlib: d/dz (z-c)⁻¹ = -(z-c)⁻²
    · simp only [neg_mul, one_mul]
      -- Ensure power notation matches expected output if needed, or leave as is
      rfl
    · exact h_ne
  · -- Handle the holomorphic part f(z)
    exact differentiableAt_inv_sub_const h_ne
  · exact h_holo

/-!
## Section 3: Pole Domination
Resolves Line 196: Pole domination arithmetic
-/

/-- Core Lemma: A pole dominates any constant bound.
    For any C, 1/|s-ρ| > C for s sufficiently close to ρ. -/
lemma pole_dominates_constant (ρ : ℂ) (C : ℝ) :
    ∀ᶠ s in 𝓝[≠] ρ, C < ‖(s - ρ)⁻¹‖ := by
  -- Filter argument: We look at the deleted neighborhood 𝓝[≠] ρ
  -- Case 1: C ≤ 0 (Trivial, norm is non-negative)
  by_cases hC : C ≤ 0
  · filter_upwards with s
    exact lt_of_le_of_lt hC (norm_nonneg _)

  -- Case 2: C > 0
  · push_neg at hC
    -- We want ‖(s - ρ)⁻¹‖ > C ↔ 1/‖s - ρ‖ > C ↔ ‖s - ρ‖ < 1/C
    have h_inv : 0 < 1/C := one_div_pos.mpr hC
    -- The metric ball of radius 1/C around ρ satisfies this
    rw [Metric.eventually_nhdsWithin_iff]
    use 1/C
    constructor
    · exact h_inv
    · intro s hs_dist hs_neq
      simp only [norm_eq_abs, Complex.abs_inv]
      rw [dist_eq_norm] at hs_dist
      -- Algebraic rearrangement
      have h_pos : 0 < Complex.abs (s - ρ) := Complex.abs.pos hs_neq
      rw [one_div_lt_iff h_pos hC]
      rwa [one_div_one_div] at hs_dist

/-!
## Section 4: Filter Intersection and Extraction
Resolves Line 247: Filter intersection and δ extraction
-/

/--
Extracts a concrete δ > 0 from a filter statement about a deleted neighborhood.
Useful for converting topological limits into "exists δ" statements for ε-δ proofs.
-/
lemma extract_delta_from_nhds {ρ : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ s in 𝓝[≠] ρ, P s) :
    ∃ δ > 0, ∀ s, 0 < Complex.abs (s - ρ) ∧ Complex.abs (s - ρ) < δ → P s := by
  rw [Metric.eventually_nhdsWithin_iff] at h
  rcases h with ⟨δ, hδ_pos, h_imp⟩
  use δ, hδ_pos
  intro s ⟨h_pos, h_lt⟩
  rw [dist_eq_norm] at h_imp
  apply h_imp
  · rw [dist_eq_norm]
    exact h_lt
  · -- Convert 0 < abs(s-ρ) to s ≠ ρ
    intro h_eq
    rw [h_eq] at h_pos
    simp at h_pos

end Residues
