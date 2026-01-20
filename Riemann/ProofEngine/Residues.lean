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

- theorem log_deriv_real_part_large (proved .
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Topology.Order.Basic
import Riemann.Axioms


noncomputable section

open Complex Filter Topology Set

namespace ProofEngine.Residues

/-!
## 1. Real Part of Pole Term
-/

/-- Real part of 1/(s - ρ) = (s.re - ρ.re) / |s - ρ|². -/
theorem real_part_pole (s ρ : ℂ) (h_ne : s ≠ ρ) :
    (1 / (s - ρ)).re = (s.re - ρ.re) / ‖s - ρ‖ ^ 2 := by
  have h_sub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr h_ne
  rw [one_div, inv_re, normSq_eq_norm_sq]
  simp only [sub_re]

/-- The imaginary part of 1/(s - ρ). -/
theorem imag_part_pole (s ρ : ℂ) (h_ne : s ≠ ρ) :
    (1 / (s - ρ)).im = -(s.im - ρ.im) / ‖s - ρ‖ ^ 2 := by
  have _h_sub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr h_ne
  rw [one_div, inv_im, normSq_eq_norm_sq, sub_im]

/-!
## 2. Limit Behavior Near Pole
-/

/-- Helper: σ - ρ.re > 0 in right neighborhood. -/
theorem pos_in_right_nhds (ρ : ℂ) :
    ∀ᶠ σ : ℝ in 𝓝[>] ρ.re, 0 < σ - ρ.re := by
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact sub_pos.mpr hσ

/-- Helper: |σ + t*I - ρ|² → 0 as σ → ρ.re when t = ρ.im. -/
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

/-- Re[1/(σ + t*I - ρ)] → +∞ as σ → ρ.re from right (when t = ρ.im). -/
theorem pole_real_part_tendsto_atTop (ρ : ℂ) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) + ρ.im * I - ρ)⁻¹.re) (𝓝[>] ρ.re) atTop := by
  -- Re[1/(σ + t*I - ρ)] = (σ - ρ.re) / |σ + t*I - ρ|²
  -- When t = ρ.im, this = (σ - ρ.re) / (σ - ρ.re)² = 1/(σ - ρ.re) → +∞
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
## 3. Zeta Properties Near Zeros
-/

/-- Zeta is differentiable away from s = 1. -/
theorem differentiable_zeta_away_from_one (s : ℂ) (h : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta h

/- Near a simple zero ρ, ζ(s) ≈ (s - ρ) * ζ'(ρ) + higher order terms. -/
noncomputable section AristotleLemmas

/-
If a function is differentiable near a point and zero at that point, it has a second-order Taylor expansion with a continuous remainder.
-/
theorem differentiable_taylor_approx_two (f : ℂ → ℂ) (a : ℂ)
    (h_diff : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ f z) (h_zero : f a = 0) :
    ∃ r : ℂ → ℂ, (∀ᶠ z in 𝓝 a, f z = (z - a) * deriv f a + (z - a) ^ 2 * r z) ∧ ContinuousAt r a := by
      -- Let g = dslope f a. Since f is differentiable near a, there exists a neighborhood U of a such that f is differentiable on U.
      obtain ⟨U, hU⟩ : ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧ ∀ z ∈ U, DifferentiableAt ℂ f z := by
        exact Exists.imp ( by tauto ) ( mem_nhds_iff.mp h_diff );
      -- Since $g$ is differentiable on $U$, it is differentiable at $a$.
      have hg_diff : DifferentiableAt ℂ (dslope f a) a := by
        have hg_diff : DifferentiableOn ℂ (dslope f a) U := by
          exact differentiableOn_dslope ( hU.1.mem_nhds hU.2.1 ) |>.2 ( fun z hz => hU.2.2 z hz |> DifferentiableAt.differentiableWithinAt );
        exact hg_diff.differentiableAt ( hU.1.mem_nhds hU.2.1 );
      -- Let $r = \text{dslope } g a$.
      set r : ℂ → ℂ := dslope (dslope f a) a;
      -- By `continuousAt_dslope_same`, $r$ is continuous at $a$.
      have hr_cont : ContinuousAt r a := by
        exact continuousAt_dslope_same.mpr hg_diff;
      -- For $z \in U$, we have $f(z) - f(a) = (z - a) \bullet g(z)$.
      have h_eq : ∀ z ∈ U, f z = (z - a) * (dslope f a z) := by
        intro z hz; by_cases h : z = a <;> simp_all +decide [ dslope ] ;
        simp +decide [ slope_def_field, h ];
        rw [ mul_div_cancel₀ _ ( sub_ne_zero_of_ne h ), h_zero, sub_zero ];
      field_simp;
      -- Since $g$ is differentiable at $a$, we have $g(z) = \text{deriv } f a + (z - a) * r(z)$ for $z \in U$.
      have h_g_eq : ∀ z ∈ U, dslope f a z = deriv f a + (z - a) * r z := by
        intro z hz; by_cases h : z = a <;> simp +decide [ *, dslope ] ;
        · simp +decide [ h, Function.update_apply ];
        · simp +zetaDelta at *;
          simp +decide [ slope_def_field, dslope, h ];
          rw [ mul_div_cancel₀ _ ( sub_ne_zero_of_ne h ) ] ; ring;
      exact ⟨ r, Filter.eventually_of_mem ( hU.1.mem_nhds hU.2.1 ) fun z hz => by rw [ h_eq z hz, h_g_eq z hz ], hr_cont ⟩

end AristotleLemmas

theorem zeta_taylor_at_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (r : ℂ → ℂ), (∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) * deriv riemannZeta ρ +
      (s - ρ) ^ 2 * r s) ∧ ContinuousAt r ρ := by
  exact differentiable_taylor_approx_two _ _ ( Filter.eventually_of_mem ( IsOpen.mem_nhds ( isOpen_compl_singleton.preimage continuous_id' ) h_not_one ) fun x hx => differentiable_zeta_away_from_one _ hx ) h_zero

-- (Taylor expansion at zero with remainder)

/- Log derivative near zero: ζ'/ζ(s) = 1/(s - ρ) + holomorphic. -/
noncomputable section AristotleLemmas2

/-
If f is analytic at z0 and has a simple zero there, then f'/f = 1/(z-z0) + h(z) for some analytic h.
-/
theorem log_deriv_of_simple_zero {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hz : f z₀ = 0) (hd : deriv f z₀ ≠ 0) :
    ∃ h, AnalyticAt ℂ h z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, deriv f z / f z = (z - z₀)⁻¹ + h z := by
      -- Use `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` on `hf`.
      obtain ⟨n, g, hg⟩ : ∃ n : ℕ, (∃ g : ℂ → ℂ, (∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n * g z) ∧ AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0) := by
        have := hf.exists_eventuallyEq_pow_smul_nonzero_iff;
        contrapose! this;
        refine Or.inr ⟨ ?_, ?_ ⟩;
        · intro n g hg hg' h; specialize this n g; aesop;
        · intro h
          -- h : ∀ᶠ (x : ℂ) in 𝓝 z₀, f x = 0
          -- We need: deriv f z₀ = 0
          have h_eq : f =ᶠ[𝓝 z₀] fun _ => 0 := by
            filter_upwards [h] with x hx
            simp only [ne_eq, not_not] at hx
            exact hx
          have h_deriv : deriv f z₀ = deriv (fun _ => (0 : ℂ)) z₀ :=
            Filter.EventuallyEq.deriv_eq h_eq
          simp only [deriv_const] at h_deriv
          exact hd h_deriv
      -- Since `f z₀ = 0`, `n ≥ 1`.
      have hn : 1 ≤ n := by
        rcases n with ( _ | n ) <;> simp_all +decide [ sub_eq_iff_eq_add ];
        have := hg.1.self_of_nhds; aesop;
      -- Differentiating `f z = (z - z₀)^n * g z` gives `f' z = n(z - z₀)^(n-1) g z + (z - z₀)^n g' z`.
      have h_diff : ∀ᶠ z in 𝓝 z₀, deriv f z = n * (z - z₀) ^ (n - 1) * g z + (z - z₀) ^ n * deriv g z := by
        -- Apply the product rule to differentiate $f(z) = (z - z₀)^n * g(z)$.
        have h_diff : ∀ᶠ z in 𝓝 z₀, deriv f z = deriv (fun z => (z - z₀) ^ n * g z) z := by
          rw [ eventually_nhds_iff ] at *;
          rcases hg.1 with ⟨ t, ht₁, ht₂, ht₃ ⟩ ; exact ⟨ t, fun y hy => Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_of_mem ( ht₂.mem_nhds hy ) fun x hx => ht₁ x hx, ht₂, ht₃ ⟩ ;
        filter_upwards [ h_diff, hg.2.1.eventually_analyticAt ] with z hz hz' using hz.trans ( by norm_num [ hz'.differentiableAt ] );
      -- Since `f' z₀ ≠ 0`, we must have `n = 1`.
      have hn_one : n = 1 := by
        contrapose! hd;
        rw [ h_diff.self_of_nhds ] ; rcases n with ( _ | _ | n ) <;> aesop;
      -- Then `f' z / f z = (g z + (z - z₀) g' z) / ((z - z₀) g z) = 1/(z - z₀) + g' z / g z`.
      have h_div : ∀ᶠ z in 𝓝[≠] z₀, deriv f z / f z = (1 / (z - z₀)) + (deriv g z / g z) := by
        have h_div : ∀ᶠ z in 𝓝[≠] z₀, deriv f z / f z = (g z + (z - z₀) * deriv g z) / ((z - z₀) * g z) := by
          filter_upwards [ h_diff.filter_mono nhdsWithin_le_nhds, hg.1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin ] with z hz₁ hz₂ hz₃ ; aesop;
        filter_upwards [ h_div, self_mem_nhdsWithin, hg.2.1.continuousAt.continuousWithinAt.eventually_ne hg.2.2 ] with z hz₁ hz₂ hz₃ ; rw [ hz₁ ] ; rw [ div_add_div ] <;> ring <;> simp +decide [ sub_ne_zero, hz₂, hz₃ ] ;
        exact hz₂;
      exact ⟨ fun z => deriv g z / g z, by exact AnalyticAt.div ( hg.2.1.deriv ) hg.2.1 hg.2.2, by simpa using h_div ⟩

end AristotleLemmas2

theorem log_deriv_near_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (h : ℂ → ℂ), DifferentiableAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s := by
  -- Apply `log_deriv_of_simple_zero` to `riemannZeta` at `ρ`.
  obtain ⟨h, hh⟩ := (log_deriv_of_simple_zero (by
  refine' DifferentiableOn.analyticAt _ _;
  exact { s : ℂ | s ≠ 1 };
  · intro s hs;
    exact DifferentiableAt.differentiableWithinAt ( by exact differentiable_zeta_away_from_one s hs );
  · exact isOpen_ne.mem_nhds h_not_one) h_zero h_simple);
  exact ⟨ h, hh.1.differentiableAt, hh.2 ⟩

-- (From Taylor expansion and quotient rule)

/-!
## 4. Pole Domination
-/

/-- The holomorphic part h(s) is bounded near ρ. -/
theorem holomorphic_part_bounded (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (C : ℝ) (δ : ℝ), 0 < C ∧ 0 < δ ∧
      ∀ s, ‖s - ρ‖ < δ → s ≠ ρ →
        ‖deriv riemannZeta s / riemannZeta s - (s - ρ)⁻¹‖ ≤ C := by
  -- Apply the log derivative near zero theorem.
  obtain ⟨h, h_diff, h_eq⟩ := log_deriv_near_zero ρ h_zero h_not_one h_simple;
  -- Since h is differentiable at ρ, it is bounded near ρ.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ s : ℂ, ‖s - ρ‖ < δ → ‖h s‖ ≤ ‖h ρ‖ + 1 := by
    have := Metric.continuousAt_iff.mp h_diff.continuousAt;
    exact Exists.elim ( this 1 zero_lt_one ) fun δ hδ => ⟨ δ, hδ.1, fun s hs => by simpa using norm_add_le ( h ρ ) ( h s - h ρ ) |> le_trans <| by simpa using hδ.2 hs |> le_of_lt ⟩;
  -- Choose δ such that for all s with ‖s - ρ‖ < δ, the difference quotient is equal to (s - ρ)⁻¹ + h(s).
  obtain ⟨δ', hδ'_pos, hδ'⟩ : ∃ δ' > 0, ∀ s : ℂ, ‖s - ρ‖ < δ' → s ≠ ρ → deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s := by
    obtain ⟨ δ', hδ' ⟩ := Metric.mem_nhdsWithin_iff.mp h_eq; use δ'; aesop;
  exact ⟨ ‖h ρ‖ + 1, Min.min δ δ', by positivity, lt_min hδ_pos hδ'_pos, fun s hs hs' => by rw [ hδ' s ( lt_of_lt_of_le hs ( min_le_right _ _ ) ) hs' ] ; simpa using hδ s ( lt_of_lt_of_le hs ( min_le_left _ _ ) ) ⟩

-- (Bounded continuous function on compact set)

/-- Domination theorem: Near ρ from the right, Re[ζ'/ζ] is arbitrarily large positive.
    PROVEN BY ARISTOTLE -/
theorem log_deriv_real_part_large (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) (M : ℝ) :
    ∃ δ > 0, ∀ σ : ℝ, ρ.re < σ → σ < ρ.re + δ →
      (deriv riemannZeta (σ + ρ.im * I) / riemannZeta (σ + ρ.im * I)).re > M := by
  obtain ⟨C, δ₁, _hC, hδ₁, h_bdd⟩ := holomorphic_part_bounded ρ h_zero h_not_one h_simple
  -- The pole term Re[1/(s-ρ)] → +∞, so it eventually exceeds M + C
  have h_pole := pole_real_part_tendsto_atTop ρ
  -- From tendsto_atTop: eventually Re[1/(s-ρ)] ≥ M + C + 1
  have h_ev := tendsto_atTop.mp h_pole (M + C + 1)
  -- Extract δ₂ from the eventually condition in 𝓝[>] ρ.re
  -- The eventually set contains an interval (ρ.re, ρ.re + δ₂) for some δ₂ > 0
  have h_exists_delta : ∃ δ₂ > 0, ∀ σ, ρ.re < σ → σ < ρ.re + δ₂ →
      M + C + 1 ≤ ((σ : ℂ) + ρ.im * I - ρ)⁻¹.re := by
    -- Extract δ from the eventually condition using filter structure
    rw [Filter.Eventually, mem_nhdsWithin] at h_ev
    obtain ⟨t, ht_open, ha_mem, ht_sub⟩ := h_ev
    rw [Metric.isOpen_iff] at ht_open
    obtain ⟨ε, hε_pos, hε_ball⟩ := ht_open ρ.re ha_mem
    use ε, hε_pos
    intro σ hσ_gt hσ_lt
    apply ht_sub
    constructor
    · apply hε_ball
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    · exact hσ_gt
  obtain ⟨δ₂, hδ₂_pos, h_large⟩ := h_exists_delta
  use min δ₁ δ₂, lt_min hδ₁ hδ₂_pos
  intro σ hσ_gt hσ_lt
  have h_ne : (σ : ℂ) + ρ.im * I ≠ ρ := by
    intro h_eq
    have hσ_eq : σ = ρ.re := by
      have h_re := congrArg Complex.re h_eq
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
        mul_one, sub_self, add_zero] at h_re
      exact h_re
    linarith
  have h_dist : ‖(σ : ℂ) + ρ.im * I - ρ‖ < δ₁ := by
    have h_sub : (σ : ℂ) + ρ.im * I - ρ = (σ - ρ.re : ℝ) := by
      apply Complex.ext <;> simp [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    rw [h_sub, norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ_gt)]
    calc σ - ρ.re < ρ.re + min δ₁ δ₂ - ρ.re := by linarith
         _ = min δ₁ δ₂ := by ring
         _ ≤ δ₁ := min_le_left _ _
  have h_rem := h_bdd ((σ : ℂ) + ρ.im * I) h_dist h_ne
  -- Re[ζ'/ζ] = Re[1/(s-ρ)] + Re[h(s)]
  -- ≥ Re[1/(s-ρ)] - |h(s)|
  -- > (M + C + 1) - C = M + 1 > M
  have h_σ_lt_δ₂ : σ < ρ.re + δ₂ := calc
    σ < ρ.re + min δ₁ δ₂ := hσ_lt
    _ ≤ ρ.re + δ₂ := by linarith [min_le_right δ₁ δ₂]
  have h_pole_val : M + C + 1 ≤ ((σ : ℂ) + ρ.im * I - ρ)⁻¹.re := h_large σ hσ_gt h_σ_lt_δ₂
  -- Use triangle inequality for real parts:
  -- |z - w| ≤ C implies z.re ≥ w.re - C
  let z := deriv riemannZeta ((σ : ℂ) + ρ.im * I) / riemannZeta ((σ : ℂ) + ρ.im * I)
  let w := ((σ : ℂ) + ρ.im * I - ρ)⁻¹
  have h_re_bound : z.re ≥ w.re - C := by
    have h1 : |z.re - w.re| ≤ ‖z - w‖ := abs_re_le_norm (z - w)
    have h2 : |z.re - w.re| ≤ C := le_trans h1 h_rem
    have h3 : z.re - w.re ≥ -C := neg_le_of_abs_le h2
    linarith
  -- Now: z.re ≥ w.re - C ≥ (M + C + 1) - C = M + 1 > M
  linarith

/-!
## 5. Negative Clustering Consequence
-/

/-- The real part of -ζ'/ζ near a zero is large negative. PROVEN BY ARISTOTLE -/
theorem neg_log_deriv_large_negative (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) (M : ℝ) (_hM : 0 < M) :
    ∃ δ > 0, ∀ σ : ℝ, ρ.re < σ → σ < ρ.re + δ →
      (-(deriv riemannZeta (σ + ρ.im * I) / riemannZeta (σ + ρ.im * I))).re < -M := by
  obtain ⟨δ, hδ, h_large⟩ := log_deriv_real_part_large ρ h_zero h_not_one h_simple M
  use δ, hδ
  intro σ hσ_gt hσ_lt
  have h := h_large σ hσ_gt hσ_lt
  simp only [neg_re]
  linarith

/-- Main theorem: Zeta zero implies clustering condition for sums.
    The weighted cosine sum becomes negative near zeros.

    Uses the stiffness approach: d/ds(-ζ'/ζ) diverges to +∞ near zeros,
    while the finite sum approximates -Re[stiffness] with bounded error.
    By domination, the finite sum must be negative. -/
theorem zeta_zero_gives_negative_clustering (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_strip : 0 < ρ.re ∧ ρ.re < 1) (h_simple : deriv riemannZeta ρ ≠ 0)
    (primes : List ℕ) (_h_primes : ∀ p ∈ primes, Nat.Prime p)
    (_h_large : primes.length > 1000) :
    ∃ δ > 0, ∀ σ ∈ Ioo (ρ.re) (ρ.re + δ),
      primes.foldl (fun acc p =>
        acc + Real.log p * Real.log p * (p : ℝ) ^ (-σ) * Real.cos (ρ.im * Real.log p)) 0 < 0 := by
  -- Strategy: Use stiffness divergence + approximation bound
  -- 1. Stiffness: Re[d/ds(-ζ'/ζ)] > M near ρ (from axiom)
  -- 2. Approximation: |Finite + Analytic| < E for σ > ρ.re (from Explicit Formula axiom)
  -- 3. Domination: Finite < -Analytic + E < -M + E < 0 (for M > E)
  have h_not_one : ρ ≠ 1 := by
    intro h_eq
    rw [h_eq] at h_strip
    simp only [one_re] at h_strip
    linarith [h_strip.2]
  -- Get approximation bound (now valid for all σ > ρ.re)
  obtain ⟨E, hE_pos, h_approx⟩ := ProofEngine.ax_finite_sum_approx_analytic ρ primes
  -- Get stiffness divergence for M = E + 1 (so M > E)
  let M := E + 1
  obtain ⟨δ, hδ_pos, h_stiff⟩ := ProofEngine.ax_analytic_stiffness_pos ρ h_zero h_simple M
  use δ, hδ_pos
  intro σ hσ
  -- Define the finite sum and analytic term
  let Finite := primes.foldl (fun acc p =>
        acc + Real.log p * Real.log p * (p : ℝ) ^ (-σ) * Real.cos (ρ.im * Real.log p)) 0
  let Analytic := (deriv (fun s => -(deriv riemannZeta s / riemannZeta s)) (σ + ρ.im * I)).re
  -- Stiffness bound: Analytic > M = E + 1
  have h_stiff_val : Analytic > M := h_stiff σ hσ.1 hσ.2
  -- Approximation bound: |Finite + Analytic| < E (valid since σ > ρ.re)
  have h_approx_val : abs (Finite + Analytic) < E := h_approx σ hσ.1
  -- Domination argument:
  -- From |Finite + Analytic| < E: Finite + Analytic > -E, so Finite > -Analytic - E
  -- But also: Finite + Analytic < E, so Finite < E - Analytic
  -- Since Analytic > M = E + 1: Finite < E - (E + 1) = -1 < 0
  have h_bound : Finite < E - Analytic := by
    have := abs_lt.mp h_approx_val
    linarith [this.2]
  calc Finite < E - Analytic := h_bound
    _ < E - M := by linarith [h_stiff_val]
    _ = E - (E + 1) := rfl
    _ = -1 := by ring
    _ < 0 := by norm_num

-- (Approximation argument from PrimeSumApproximation)

end ProofEngine.Residues

end
