/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7374ee37-a901-46c5-99ea-af0b265ded24

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- axiom zeta_taylor_at_zero (ρ :ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (r : ℂ → ℂ), (∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) * deriv riemannZeta ρ +
      (s - ρ) ^ 2 * r s) ∧ ContinuousAt r ρ

- theorem log_deriv_near_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (h : ℂ → ℂ), DifferentiableAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s

- theorem holomorphic_part_bounded (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (C : ℝ) (δ : ℝ), 0 < C ∧ 0 < δ ∧
      ∀ s, ‖s - ρ‖ < δ → s ≠ ρ →
        ‖deriv riemannZeta s / riemannZeta s - (s - ρ)⁻¹‖ ≤ C

- theorem log_deriv_real_part_large (proved by Aristotle)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.Order.Basic
import Riemann.ProofEngine.AnalyticBasics

noncomputable section
open Complex Filter Topology Set
open ProofEngine.AnalyticBasics

namespace ProofEngine.Residues

/-!
## 1. Real Part of Pole Term
-/

theorem real_part_pole (s ρ : ℂ) (h_ne : s ≠ ρ) :
    (1 / (s - ρ)).re = (s.re - ρ.re) / ‖s - ρ‖ ^ 2 := by
  have h_sub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr h_ne
  rw [one_div, inv_re, normSq_eq_norm_sq]
  simp only [sub_re]

theorem imag_part_pole (s ρ : ℂ) (h_ne : s ≠ ρ) :
    (1 / (s - ρ)).im = -(s.im - ρ.im) / ‖s - ρ‖ ^ 2 := by
  have _h_sub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr h_ne
  rw [one_div, inv_im, normSq_eq_norm_sq, sub_im]

/-!
## 2. Limit Behavior Near Pole
-/

theorem pos_in_right_nhds (ρ : ℂ) :
    ∀ᶠ σ : ℝ in 𝓝[>] ρ.re, 0 < σ - ρ.re := by
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact sub_pos.mpr hσ

theorem normSq_tendsto_zero_on_line (ρ : ℂ) :
    Tendsto (fun σ : ℝ => ‖(σ : ℂ) + ρ.im * I - ρ‖ ^ 2) (𝓝[>] ρ.re) (𝓝 0) := by
  have h_eq : ∀ σ : ℝ, ‖(σ : ℂ) + ρ.im * I - ρ‖ ^ 2 = (σ - ρ.re) ^ 2 := by
    intro σ
    have h_sub : (σ : ℂ) + ρ.im * I - ρ = (σ - ρ.re : ℝ) := by
      apply Complex.ext <;> simp [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    rw [h_sub]
    simp only [norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h_eq]
  have h_sq : Tendsto (fun σ : ℝ => (σ - ρ.re) ^ 2) (𝓝[>] ρ.re) (𝓝 0) := by
    have h_sub_tendsto : Tendsto (fun σ => σ - ρ.re) (𝓝[>] ρ.re) (𝓝[>] 0) := by
      have h1 : Tendsto (fun σ => σ - ρ.re) (𝓝 ρ.re) (𝓝 0) := by
        have := continuous_sub_right ρ.re |>.tendsto ρ.re
        simp only [sub_self] at this
        exact this
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (h1.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [mem_Ioi] at hσ
      exact sub_pos.mpr hσ
    have h_sq_cont : Continuous (fun x : ℝ => x ^ 2) := continuous_pow 2
    have := h_sq_cont.continuousAt.tendsto.comp (h_sub_tendsto.mono_right nhdsWithin_le_nhds)
    simp only [Function.comp_def] at this
    convert this using 1
    norm_num
  exact h_sq

theorem pole_real_part_tendsto_atTop (ρ : ℂ) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) + ρ.im * I - ρ)⁻¹.re) (𝓝[>] ρ.re) atTop := by
  have h_eq : ∀ σ : ℝ, σ ≠ ρ.re →
      ((σ : ℂ) + ρ.im * I - ρ)⁻¹.re = (σ - ρ.re)⁻¹ := by
    intro σ hσ
    have h_sub : (σ : ℂ) + ρ.im * I - ρ = (σ - ρ.re : ℝ) := by
      apply Complex.ext <;> simp [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    rw [h_sub, ← ofReal_inv, ofReal_re]
  have h_tendsto : Tendsto (·⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have h_sub : Tendsto (fun σ => σ - ρ.re) (𝓝[>] ρ.re) (𝓝[>] 0) := by
    have h1 : Tendsto (fun σ => σ - ρ.re) (𝓝 ρ.re) (𝓝 0) := by
      have := continuous_sub_right ρ.re |>.tendsto ρ.re
      simp only [sub_self] at this
      exact this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h1.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [mem_Ioi] at hσ
    exact sub_pos.mpr hσ
  have h_inv := h_tendsto.comp h_sub
  have h_ev_eq : (fun σ : ℝ => (σ - ρ.re)⁻¹) =ᶠ[𝓝[>] ρ.re]
      (fun σ : ℝ => ((σ : ℂ) + ρ.im * I - ρ)⁻¹.re) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : ρ.re < σ := hσ
    exact (h_eq σ (ne_of_gt hσ')).symm
  exact Tendsto.congr' h_ev_eq h_inv

/-!
## 3. Analytic Lemmas (Taylor Expansions)
-/

theorem differentiable_zeta_away_from_one (s : ℂ) (h : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta h

theorem log_deriv_near_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (h : ℂ → ℂ), DifferentiableAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s :=
  log_deriv_zeta_near_zero ρ h_zero h_not_one h_simple

/-!
## 4. Stiffness Pole (Derivative of Log Derivative)
Here we prove the divergence of the derivative of the log derivative.
-/

/--
Near a simple zero, (ζ'/ζ)'(s) = -1/(s-ρ)² + h'(s).
This replaces the stiffness axiom.
-/
theorem stiffness_near_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (h' : ℂ → ℂ), ContinuousAt h' ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ,
        deriv (fun z => deriv riemannZeta z / riemannZeta z) s =
          -(s - ρ) ^ (-2 : ℤ) + h' s := by
  obtain ⟨h, h_diff, h_eq⟩ := log_deriv_near_zero ρ h_zero h_not_one h_simple
  -- Differentiate the relation: D(1/(s-ρ) + h) = -1/(s-ρ)^2 + h'
  let h' := deriv h
  use h'
  constructor
  · -- h is differentiable at ρ, so deriv h is continuous at ρ
    -- This is a consequence of h being analytic (since differentiable in ℂ implies analytic)
    sorry -- (Continuity of derivative of holomorphic function)
  · -- The derivative of 1/(s-ρ) + h(s) is -1/(s-ρ)^2 + h'(s)
    -- This requires showing differentiability at points near ρ
    sorry -- (Derivative of pole + holomorphic: standard complex analysis)

/--
The stiffness (derivative of log derivative) real part tends to -∞ on horizontal approach.
This is the theorem referenced in PhaseClustering.lean.
-/
theorem stiffness_real_part_tendsto_atBot (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun σ : ℝ =>
      (deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re)
      (𝓝[>] ρ.re) atBot := by
  -- The stiffness is (ζ'/ζ)'(s) = -1/(s-ρ)² + h'(s) near a zero
  -- On the horizontal line s = σ + iρ.im, s - ρ = σ - ρ.re (purely real)
  -- So -1/(s-ρ)² = -1/(σ - ρ.re)² → -∞ as σ → ρ.re⁺
  -- The holomorphic part h'(s) is bounded near ρ
  -- Therefore the sum → -∞

  -- 1. Pole term: -1/(σ - ρ.re)² → -∞ as σ → ρ.re⁺
  have h_pole_lim : Tendsto (fun σ : ℝ => -((σ - ρ.re) ^ 2)⁻¹) (𝓝[>] ρ.re) atBot := by
    have h_sq : Tendsto (fun σ => (σ - ρ.re) ^ 2) (𝓝[>] ρ.re) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h_cont : Continuous (fun σ : ℝ => (σ - ρ.re) ^ 2) := by continuity
        have h_val : (ρ.re - ρ.re) ^ 2 = 0 := by ring
        rw [← h_val]
        exact (h_cont.tendsto ρ.re).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        simp only [mem_Ioi] at hσ
        exact pow_pos (sub_pos.mpr hσ) 2
    have h_inv : Tendsto (·⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    exact tendsto_neg_atTop_atBot.comp (h_inv.comp h_sq)

  -- 2. The full stiffness = pole + bounded behaves like -∞ + O(1) = -∞
  -- This is the pole domination argument
  sorry -- (Pole domination: -∞ + bounded = -∞)

/-!
## 5. Negative Clustering Consequence
-/

/--
Definition: The weighted cosine sum (the "Finite Sum" in the Explicit Formula).
-/
def weightedCosSum (primes : List ℕ) (σ t : ℝ) : ℝ :=
  primes.foldl (fun (acc : ℝ) (p : ℕ) =>
    acc + Real.log p * Real.log p * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)) 0

/--
Structure representing the Explicit Formula for the Stiffness (Derivative).
This hypothesis asserts that the Finite Sum approximates the Derivative of the Log Derivative.
-/
structure AdmissibleStiffnessApproximation (ρ : ℂ) (primes : List ℕ) : Prop where
  error_bound : ∃ E : ℝ, 0 < E ∧ ∀ᶠ σ in 𝓝[>] ρ.re,
    |weightedCosSum primes σ ρ.im -
        (deriv (fun s => deriv riemannZeta s / riemannZeta s) ((σ : ℂ) + ρ.im * I)).re| < E

/-- Main theorem: Zeta zero implies clustering condition for sums.
    The weighted cosine sum becomes negative near zeros. -/
theorem zeta_zero_gives_negative_clustering (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_strip : 0 < ρ.re ∧ ρ.re < 1) (h_simple : deriv riemannZeta ρ ≠ 0)
    (primes : List ℕ) (_h_primes : ∀ p ∈ primes, Nat.Prime p)
    (h_approx : AdmissibleStiffnessApproximation ρ primes) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioo (ρ.re) (ρ.re + δ),
      weightedCosSum primes σ ρ.im < 0 := by

  -- ρ ≠ 1 because ρ.re < 1
  have h_not_one : ρ ≠ 1 := by
    intro h_eq
    rw [h_eq] at h_strip
    simp only [one_re] at h_strip
    linarith [h_strip.2]

  -- 1. Stiffness (Derivative) goes to -∞
  have _h_lim := stiffness_real_part_tendsto_atBot ρ h_zero h_not_one h_simple

  -- 2. Get error bound
  obtain ⟨E, hE_pos, h_err⟩ := h_approx.error_bound

  -- 3. The argument:
  -- Since Analytic → -∞, eventually Analytic < -E - 1
  -- Since |Finite - Analytic| < E, we have Finite < Analytic + E < -1 < 0
  --
  -- The detailed filter manipulation to extract δ requires:
  -- - Intersecting the "eventually < -E-1" set with the "eventually |..| < E" set
  -- - Extracting a metric ball from the intersection
  sorry -- (Filter intersection and extraction of δ)

end ProofEngine.Residues

end
