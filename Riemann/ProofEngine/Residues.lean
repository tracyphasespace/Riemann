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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.Order.Basic
import Riemann.ProofEngine.AnalyticBasics

noncomputable section
open Complex Filter Topology Set
open ProofEngine.AnalyticBasics

namespace ProofEngine.Residues

/-!
## 0. Helper Lemmas (from llm_input/002_Residues.lean)
These help fill in sorries below.
-/

/-- Helper: The derivative of a holomorphic function is continuous on open sets. -/
lemma holomorphic_deriv_continuous {f : ℂ → ℂ} {s : Set ℂ}
    (h_diff : DifferentiableOn ℂ f s) (h_open : IsOpen s) :
    ContinuousOn (deriv f) s := by
  have h_deriv_diff : DifferentiableOn ℂ (deriv f) s :=
    DifferentiableOn.deriv h_diff h_open
  exact h_deriv_diff.continuousOn

/-- Core Lemma: A pole dominates any constant bound.
    For any C, 1/|s-ρ| > C for s sufficiently close to ρ. -/
lemma pole_dominates_constant (ρ : ℂ) (C : ℝ) :
    ∀ᶠ s in 𝓝[≠] ρ, C < ‖(s - ρ)⁻¹‖ := by
  -- As s → ρ (s ≠ ρ), ‖s - ρ‖ → 0⁺, so ‖(s - ρ)⁻¹‖ = 1/‖s - ρ‖ → +∞
  -- For any C, eventually 1/‖s - ρ‖ > C
  -- Use: for δ = 1/(max C 1 + 1), if 0 < ‖s - ρ‖ < δ then ‖(s - ρ)⁻¹‖ > C
  let δ := 1 / (max C 1 + 1)
  have hδ_pos : 0 < δ := by positivity
  -- The punctured ball is in the deleted neighborhood filter
  have h_mem : Metric.ball ρ δ ∩ {ρ}ᶜ ∈ 𝓝[≠] ρ := by
    rw [Set.inter_comm]
    apply inter_mem_nhdsWithin
    exact Metric.ball_mem_nhds ρ hδ_pos
  apply Filter.eventually_of_mem h_mem
  intro s hs
  simp only [mem_inter_iff, Metric.mem_ball, mem_compl_iff, mem_singleton_iff] at hs
  obtain ⟨hs_ball, hs_ne⟩ := hs
  rw [dist_eq_norm] at hs_ball
  have h_norm_pos : 0 < ‖s - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne)
  rw [norm_inv]
  have h_bound : ‖s - ρ‖ < δ := hs_ball
  -- If 0 < x < δ then 1/x > 1/δ
  have h_inv_bound : δ⁻¹ < ‖s - ρ‖⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) h_norm_pos]
    exact h_bound
  calc C ≤ max C 1 := le_max_left C 1
    _ < max C 1 + 1 := lt_add_one _
    _ = δ⁻¹ := by simp only [δ, one_div, inv_inv]
    _ < ‖s - ρ‖⁻¹ := h_inv_bound

/--
Extracts a concrete δ > 0 from a filter statement about a deleted neighborhood.
-/
lemma extract_delta_from_nhds {ρ : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ s in 𝓝[≠] ρ, P s) :
    ∃ δ > 0, ∀ s, 0 < ‖s - ρ‖ ∧ ‖s - ρ‖ < δ → P s := by
  -- Get a set U in the neighborhood filter such that P holds on U ∩ {ρ}ᶜ
  rw [Filter.Eventually] at h
  -- mem_nhdsWithin gives: ∃ U, IsOpen U ∧ ρ ∈ U ∧ U ∩ {ρ}ᶜ ⊆ P
  obtain ⟨U, hU_open, hρ_in_U, hU_P⟩ := mem_nhdsWithin.mp h
  -- From IsOpen U and ρ ∈ U, get U ∈ 𝓝 ρ
  have hU_nhds : U ∈ 𝓝 ρ := hU_open.mem_nhds hρ_in_U
  -- U is in 𝓝 ρ, so there's a ball around ρ contained in U
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp hU_nhds
  use ε, hε_pos
  intro s ⟨hs_pos, hs_lt⟩
  apply hU_P
  constructor
  · apply hε_ball
    rw [Metric.mem_ball, dist_eq_norm]
    exact hs_lt
  · simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    rw [heq, sub_self, norm_zero] at hs_pos
    exact lt_irrefl 0 hs_pos

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
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s := by
  obtain ⟨h, h_analytic, h_eq⟩ := log_deriv_zeta_near_zero ρ h_zero h_not_one h_simple
  exact ⟨h, h_analytic.differentiableAt, h_eq⟩

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
  -- Get the decomposition: ζ'/ζ = (z-ρ)⁻¹ + h(z) with h analytic at ρ
  obtain ⟨h, h_analytic, h_eq_nhds⟩ := log_deriv_zeta_near_zero ρ h_zero h_not_one h_simple

  -- Define h' as the derivative of h, prove it's continuous (since h is analytic)
  refine ⟨deriv h, h_analytic.deriv.continuousAt, ?_⟩

  -- Extract the open set where equality holds from h_eq_nhds
  rw [Filter.Eventually, mem_nhdsWithin] at h_eq_nhds
  obtain ⟨U, hU_open, hρ_in_U, hU_eq⟩ := h_eq_nhds
  -- hU_eq : U ∩ {ρ}ᶜ ⊆ {s | equality holds at s}

  -- Get neighborhood where h is differentiable (from analyticity)
  have h_diff_nhds : ∀ᶠ s in 𝓝 ρ, DifferentiableAt ℂ h s :=
    h_analytic.eventually_analyticAt.mono fun s hs => hs.differentiableAt

  -- Combine: eventually in 𝓝[≠] ρ, s ∈ U and h is differentiable at s
  have h_in_U : ∀ᶠ s in 𝓝[≠] ρ, s ∈ U := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hU_open.mem_nhds hρ_in_U

  have h_diff_within : ∀ᶠ s in 𝓝[≠] ρ, DifferentiableAt ℂ h s :=
    h_diff_nhds.filter_mono nhdsWithin_le_nhds

  filter_upwards [h_in_U, h_diff_within, self_mem_nhdsWithin] with s hs_in_U h_diff_s hs_ne_rho
  have h_sub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr hs_ne_rho

  -- The equality ζ'/ζ = (z-ρ)⁻¹ + h holds at s (from hU_eq)
  have hs_eq : deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s := by
    apply hU_eq
    exact ⟨hs_in_U, Set.mem_compl_singleton_iff.mpr hs_ne_rho⟩

  -- Now construct EventuallyEq at 𝓝 s
  -- Key: Since U is open and s ∈ U, and {ρ}ᶜ is open and s ∈ {ρ}ᶜ,
  -- the intersection U ∩ {ρ}ᶜ is open and contains s.
  -- So eventually near s, points are in U ∩ {ρ}ᶜ where hU_eq applies.

  have h_compl_open : IsOpen ({ρ}ᶜ : Set ℂ) := isOpen_compl_singleton
  have h_inter_open : IsOpen (U ∩ {ρ}ᶜ) := hU_open.inter h_compl_open
  have hs_in_inter : s ∈ U ∩ {ρ}ᶜ := ⟨hs_in_U, Set.mem_compl_singleton_iff.mpr hs_ne_rho⟩

  have h_eq_at_s : (fun z => deriv riemannZeta z / riemannZeta z) =ᶠ[𝓝 s]
      (fun z => (z - ρ)⁻¹ + h z) := by
    filter_upwards [h_inter_open.mem_nhds hs_in_inter] with z hz
    -- hz : z ∈ U ∩ {ρ}ᶜ, so hU_eq applies
    exact hU_eq hz

  -- Now differentiate both sides
  rw [Filter.EventuallyEq.deriv_eq h_eq_at_s]

  -- Differentiability of RHS components at s
  have h_diff_sub : DifferentiableAt ℂ (fun z => z - ρ) s :=
    differentiableAt_id.sub (differentiableAt_const ρ)
  have h_inv_diff : DifferentiableAt ℂ (fun z => (z - ρ)⁻¹) s := h_diff_sub.inv h_sub_ne

  -- Compute deriv of (z - ρ)⁻¹ using HasDerivAt
  -- For f(z) = (z - ρ)⁻¹, f'(s) = -1/(s - ρ)² = -((s - ρ)⁻¹)²
  have h_deriv_inv : deriv (fun z => (z - ρ)⁻¹) s = -((s - ρ)⁻¹)^2 := by
    -- (z - ρ)⁻¹ = Inv.inv (z - ρ), use chain rule
    have h_has_deriv_sub : HasDerivAt (fun z => z - ρ) 1 s := by
      simpa using hasDerivAt_id s |>.sub_const ρ
    -- HasDerivAt.inv gives: HasDerivAt c⁻¹ (-c' / c x ^ 2) x
    -- Here c' = 1, c x = s - ρ, so result is -1 / (s - ρ)^2
    have h_has_deriv_inv : HasDerivAt (fun z => (z - ρ)⁻¹) (-1 / (s - ρ)^2) s :=
      h_has_deriv_sub.inv h_sub_ne
    -- Now show -1 / (s - ρ)^2 = -((s - ρ)⁻¹)^2
    rw [h_has_deriv_inv.deriv]
    -- -1 / (s - ρ)^2 = -((s - ρ)⁻¹)^2
    simp only [neg_div, one_div, inv_pow]

  -- Compute deriv of (z - ρ)⁻¹ + h z using deriv_add
  have h_deriv_sum : deriv (fun z => (z - ρ)⁻¹ + h z) s =
      deriv (fun z => (z - ρ)⁻¹) s + deriv h s := deriv_add h_inv_diff h_diff_s
  rw [h_deriv_sum, h_deriv_inv]

  -- Goal: -((s - ρ)⁻¹) ^ 2 + deriv h s = -(s - ρ) ^ (-2 : ℤ) + deriv h s
  congr 1
  -- -((s - ρ)⁻¹) ^ 2 = -(s - ρ) ^ (-2)
  rw [zpow_neg, zpow_ofNat, inv_pow]

/--
The stiffness (derivative of log derivative) real part tends to -∞ on horizontal approach.
This is the theorem referenced in PhaseClustering.lean.
-/
theorem stiffness_real_part_tendsto_atBot (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun σ : ℝ =>
      (deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re)
      (𝓝[>] ρ.re) atBot := by
  -- Strategy: Use stiffness_near_zero decomposition: (ζ'/ζ)'(s) = -(s-ρ)^(-2) + h'(s)
  -- The pole term -(σ - ρ.re)^(-2) → -∞ dominates the bounded h' term.
  obtain ⟨h', h'_cont, h'_eq⟩ := stiffness_near_zero ρ h_zero h_not_one h_simple

  -- Step 1: Prove -(σ - ρ.re)⁻² → -∞ as σ → ρ.re⁺
  have h_sub : Tendsto (fun σ => σ - ρ.re) (𝓝[>] ρ.re) (𝓝[>] 0) := by
    have h1 : Tendsto (fun σ => σ - ρ.re) (𝓝 ρ.re) (𝓝 0) := by
      have := continuous_sub_right ρ.re |>.tendsto ρ.re
      simp only [sub_self] at this
      exact this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h1.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ
    exact sub_pos.mpr hσ

  have h_inv : Tendsto (fun σ => (σ - ρ.re)⁻¹) (𝓝[>] ρ.re) atTop :=
    tendsto_inv_nhdsGT_zero.comp h_sub

  -- Use tendsto_pow_atTop instead of atTop_mul_atTop (Mathlib 4.27 API fix)
  have h_sq : Tendsto (fun σ => (σ - ρ.re)⁻¹ ^ 2) (𝓝[>] ρ.re) atTop := by
    have h_pow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    exact h_pow.comp h_inv

  have h_pole_neg : Tendsto (fun σ => -((σ - ρ.re)⁻¹ ^ 2)) (𝓝[>] ρ.re) atBot :=
    tendsto_neg_atTop_atBot.comp h_sq

  -- Step 2: The real part of -(s-ρ)^(-2) on the horizontal line through ρ.im
  -- On this line: s = σ + ρ.im * I, so s - ρ = σ - ρ.re (purely real)
  -- Hence (s-ρ)^(-2) = (σ - ρ.re)^(-2) which is real and positive
  have h_pole_real_eq : ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re,
      (-(((σ : ℂ) + ρ.im * I - ρ) ^ (-2 : ℤ))).re = -((σ - ρ.re)⁻¹ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    -- hσ : σ ∈ Ioi ρ.re, meaning ρ.re < σ
    -- s - ρ is purely real on the horizontal line
    have h_sub_eq : (σ : ℂ) + ρ.im * I - ρ = (σ - ρ.re : ℝ) := by
      apply Complex.ext <;> simp [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    rw [h_sub_eq]
    have h_pos : 0 < σ - ρ.re := sub_pos.mpr hσ
    have h_ne : (σ - ρ.re : ℝ) ≠ 0 := ne_of_gt h_pos
    -- Simplify: (x : ℂ)^(-2) = (x^2)⁻¹ for x : ℝ ≠ 0
    have h_zpow : ((σ - ρ.re : ℝ) : ℂ) ^ (-2 : ℤ) = (((σ - ρ.re)^2)⁻¹ : ℝ) := by
      rw [zpow_neg, zpow_ofNat]
      simp only [ofReal_pow, ofReal_inv]
    rw [h_zpow]
    -- The real part of a real number is itself
    simp only [neg_re, ofReal_re]
    -- Goal: -((σ - ρ.re) ^ 2)⁻¹ = -(σ - ρ.re)⁻¹ ^ 2
    rw [inv_pow]

  -- Step 3: h' is continuous at ρ, so bounded near ρ
  have h'_bounded : ∃ M : ℝ, ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re, |(h' ((σ : ℂ) + ρ.im * I)).re| ≤ M := by
    -- h' is continuous at ρ, so bounded in some neighborhood
    have h_cont_at : ContinuousAt (fun z => (h' z).re) ρ := ContinuousAt.comp continuous_re.continuousAt h'_cont
    -- Continuous functions are bounded near ρ
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := Metric.continuousAt_iff.mp h_cont_at 1 one_pos
    -- Use |h'(s).re| ≤ |h'(ρ).re| + 1 for s near ρ
    use |(h' ρ).re| + 1
    -- Map the ball through the embedding σ ↦ σ + ρ.im * I
    -- For σ close to ρ.re, the point σ + ρ.im * I is close to ρ
    have h_dist_eq : ∀ σ : ℝ, dist ((σ : ℂ) + ρ.im * I) ρ = |σ - ρ.re| := by
      intro σ
      rw [Complex.dist_eq]
      have h_sub_eq : (σ : ℂ) + ρ.im * I - ρ = (σ - ρ.re : ℝ) := by
        apply Complex.ext <;> simp [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
      rw [h_sub_eq]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    have h_ball_real : Metric.ball ρ.re δ ∈ 𝓝 ρ.re := Metric.ball_mem_nhds ρ.re hδ_pos
    filter_upwards [nhdsWithin_le_nhds h_ball_real] with σ hσ_ball
    -- hσ_ball : σ ∈ ball ρ.re δ, i.e., |σ - ρ.re| < δ
    have h_in_ball : (σ : ℂ) + ρ.im * I ∈ Metric.ball ρ δ := by
      rw [Metric.mem_ball, h_dist_eq]
      rw [Metric.mem_ball, Real.dist_eq] at hσ_ball
      exact hσ_ball
    specialize hδ_bound h_in_ball
    rw [Real.dist_eq] at hδ_bound
    -- hδ_bound : |(h' (↑σ + ↑ρ.im * I)).re - (h' ρ).re| < 1
    -- Goal: |(h' (↑σ + ↑ρ.im * I)).re| ≤ |(h' ρ).re| + 1
    have h1 := abs_sub_abs_le_abs_sub (h' (↑σ + ↑ρ.im * I)).re (h' ρ).re
    linarith

  -- Step 4: Combine pole divergence with bounded perturbation
  -- The derivative equals -(s-ρ)^(-2) + h'(s), so the real part is
  -- -(σ - ρ.re)^(-2) + h'(s).re eventually
  -- Since -(σ - ρ.re)^(-2) → -∞ and h'(s).re is bounded, the sum → -∞

  obtain ⟨M, hM⟩ := h'_bounded

  -- Extract δ such that h'_eq holds on deleted neighborhood
  obtain ⟨δ_eq, hδ_eq_pos, h_deriv_eq⟩ := extract_delta_from_nhds h'_eq

  -- The function we're computing the limit of decomposes as pole + bounded
  have h_decomp : ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re,
      (deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re =
      (-(((σ : ℂ) + ρ.im * I - ρ) ^ (-2 : ℤ))).re + (h' ((σ : ℂ) + ρ.im * I)).re := by
    -- Eventually, (σ : ℂ) + ρ.im * I is in the deleted neighborhood of ρ
    have h_ball : Metric.ball ρ.re δ_eq ∈ 𝓝 ρ.re := Metric.ball_mem_nhds ρ.re hδ_eq_pos
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h_ball] with σ hσ_gt hσ_ball
    simp only [Set.mem_Ioi] at hσ_gt
    -- The point s = σ + ρ.im * I satisfies ‖s - ρ‖ = |σ - ρ.re| < δ_eq
    have h_norm : ‖(σ : ℂ) + ρ.im * I - ρ‖ = |σ - ρ.re| := by
      have h_sub_eq : (σ : ℂ) + ρ.im * I - ρ = (σ - ρ.re : ℝ) := by
        apply Complex.ext <;> simp [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
      rw [h_sub_eq]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    have h_norm_pos : 0 < ‖(σ : ℂ) + ρ.im * I - ρ‖ := by
      rw [h_norm]
      exact abs_pos.mpr (ne_of_gt (sub_pos.mpr hσ_gt))
    have h_norm_lt : ‖(σ : ℂ) + ρ.im * I - ρ‖ < δ_eq := by
      rw [h_norm]
      rw [Metric.mem_ball, Real.dist_eq] at hσ_ball
      exact hσ_ball
    -- Apply h_deriv_eq
    have h_apply := h_deriv_eq ((σ : ℂ) + ρ.im * I) ⟨h_norm_pos, h_norm_lt⟩
    -- h_apply says: deriv(ζ'/ζ)(s) = -(s-ρ)^(-2) + h'(s)
    rw [h_apply]
    simp only [add_re, neg_re]

  -- Now combine: pole → -∞ and h' bounded implies sum → -∞
  -- h_pole_real_eq : ∀ᶠ σ, complex_pole.re = real_pole
  -- We need: Tendsto complex_pole.re atBot
  -- Strategy: Use Tendsto.congr' with EventuallyEq.symm

  -- Convert ∀ᶠ to =ᶠ using EventuallyEq
  have h_pole_eq : (fun σ => -((σ - ρ.re)⁻¹ ^ 2)) =ᶠ[𝓝[>] ρ.re]
      (fun σ => (-(((σ : ℂ) + ρ.im * I - ρ) ^ (-2 : ℤ))).re) :=
    h_pole_real_eq.mono fun _ h => h.symm

  have h_pole_tendsto : Tendsto (fun (σ : ℝ) =>
      (-(((σ : ℂ) + ρ.im * I - ρ) ^ (-2 : ℤ))).re) (𝓝[>] ρ.re) atBot :=
    Tendsto.congr' h_pole_eq h_pole_neg

  -- h_decomp : ∀ᶠ σ, deriv_stiffness.re = pole.re + h'.re
  -- Convert to =ᶠ for Tendsto.congr'
  have h_decomp_eq : (fun σ => (-(((σ : ℂ) + ρ.im * I - ρ) ^ (-2 : ℤ))).re +
      (h' ((σ : ℂ) + ρ.im * I)).re) =ᶠ[𝓝[>] ρ.re]
      (fun σ => (deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re) :=
    h_decomp.mono fun _ h => h.symm

  apply Tendsto.congr' h_decomp_eq
  -- Goal: Tendsto (pole.re + h'.re) (𝓝[>] ρ.re) atBot
  -- Since pole → -∞ and h'.re is bounded (|h'.re| ≤ M), we have pole + h'.re → -∞

  -- Proof using Filter.tendsto_atBot directly:
  -- For any N, eventually pole.re < N - M, and since -M ≤ h'.re,
  -- we have pole.re + h'.re < N
  rw [Filter.tendsto_atBot]
  intro B
  -- From h_pole_tendsto, eventually pole.re ≤ B - M - 1 (using B - M - 1 to get strict inequality)
  -- Note: The function maps ℝ → ℝ (via .re projection), so the comparison is on ℝ
  have h_pole_ev : ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re,
      (-(((σ : ℂ) + ρ.im * I - ρ) ^ (-2 : ℤ))).re ≤ B - M - 1 := by
    rw [Filter.tendsto_atBot] at h_pole_tendsto
    exact h_pole_tendsto (B - M - 1)
  -- Combine: pole.re + h'.re ≤ (B - M - 1) + M = B - 1 < B
  filter_upwards [h_pole_ev, hM] with σ h_pole_bound h_h'_bound
  -- From |h'.re| ≤ M, we get -M ≤ h'.re ≤ M
  have h_h'_lower : -M ≤ (h' ((σ : ℂ) + ρ.im * I)).re := by
    have habs : |(h' ((σ : ℂ) + ρ.im * I)).re| ≤ M := h_h'_bound
    exact (abs_le.mp habs).1
  -- We want to show: pole + h'.re ≤ B
  -- We have: pole ≤ B - M - 1 and h'.re ≥ -M
  -- So: pole + h'.re ≤ (B - M - 1) + (something ≤ M)
  -- Need: pole + h'.re ≤ B, i.e., h'.re ≤ B - pole ≥ B - (B - M - 1) = M + 1
  -- Since h'.re ≤ M (from |h'.re| ≤ M), we have h'.re ≤ M < M + 1
  have h_h'_upper : (h' ((σ : ℂ) + ρ.im * I)).re ≤ M := by
    have habs : |(h' ((σ : ℂ) + ρ.im * I)).re| ≤ M := h_h'_bound
    exact (abs_le.mp habs).2
  -- Now: pole + h'.re ≤ (B - M - 1) + M = B - 1 ≤ B
  linarith

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

  -- Define shorthand for stiffness real part
  let stiffness := fun σ : ℝ =>
    (deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re
  let cosSum := fun σ : ℝ => weightedCosSum primes σ ρ.im

  -- Since stiffness → -∞, eventually stiffness < -E - 1
  have h_stiff_small : ∀ᶠ σ in 𝓝[>] ρ.re, stiffness σ < -E - 1 := by
    -- Iio_mem_atBot says: Iio a ∈ atBot for any a
    have h_mem : Iio (-E - 1) ∈ atBot := Iio_mem_atBot (-E - 1)
    exact _h_lim.eventually h_mem

  -- Combine with error bound
  have h_both : ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re, stiffness σ < -E - 1 ∧ |cosSum σ - stiffness σ| < E :=
    h_stiff_small.and h_err

  -- Extract δ from eventually using metric ball approach
  -- TIER6_FIX: mem_nhdsWithin_Ioi_iff_exists_Ioo_subset may not exist in Mathlib 4.27
  -- Use Metric.eventually_nhdsWithin_iff instead
  rw [Filter.eventually_iff_exists_mem] at h_both
  obtain ⟨S, hS_mem, hS_holds⟩ := h_both
  -- S ∈ 𝓝[>] ρ.re means ∃ ball around ρ.re intersected with Ioi ρ.re
  rw [Metric.mem_nhdsWithin_iff] at hS_mem
  obtain ⟨δ_ball, hδ_pos, hδ_subset⟩ := hS_mem
  -- Use δ = δ_ball as our bound
  use δ_ball
  constructor
  · exact hδ_pos
  · intro σ hσ
    -- hσ : σ ∈ Ioo ρ.re (ρ.re + δ_ball)
    -- We need to show σ ∈ S to apply hS_holds
    have hσ_in_S : σ ∈ S := by
      apply hδ_subset
      rw [Set.mem_inter_iff, Metric.mem_ball, Set.mem_Ioi]
      constructor
      · rw [Real.dist_eq, abs_sub_lt_iff]
        simp only [mem_Ioo] at hσ
        constructor <;> linarith [hσ.1, hσ.2]
      · exact hσ.1
    -- Apply hS_holds to get the conjunction
    obtain ⟨h_stiff_neg, h_err_bound⟩ := hS_holds σ hσ_in_S
    -- From |cosSum - stiffness| < E and stiffness < -E - 1:
    -- cosSum < stiffness + E < (-E - 1) + E = -1 < 0
    have h_abs := abs_sub_lt_iff.mp h_err_bound
    linarith [h_abs.1, h_abs.2]

end ProofEngine.Residues

end
