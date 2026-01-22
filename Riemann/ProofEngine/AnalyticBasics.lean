/-
# ProofEngine.AnalyticBasics: Rigorous Proofs of Analytic Facts

This file contains fully proven theorems that replace the former axioms
`ax_zeta_taylor_at_zero` and `ax_log_deriv_near_zero` from Axioms.lean.

The proofs use Mathlib's `dslope` (difference slope) machinery:
- `dslope f z₀ z = (f z - f z₀) / (z - z₀)` for z ≠ z₀
- `dslope f z₀ z₀ = deriv f z₀`

Key insight: If f is analytic at z₀, then `dslope f z₀` is also analytic at z₀.
This follows from `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`.
-/

import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
open Complex Filter Topology

namespace ProofEngine.AnalyticBasics

/-!
## Core Lemma: Analyticity of dslope
-/

/-- If f is analytic at z₀, then `dslope f z₀` is also analytic at z₀. -/
theorem analyticAt_dslope {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    AnalyticAt ℂ (dslope f z₀) z₀ := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- riemannZeta is analytic at all points except s = 1. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [compl_singleton_mem_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

/-!
## Theorem 1: Taylor Expansion at Simple Zero (Replaces ax_zeta_taylor_at_zero)

If f(ρ) = 0 and f'(ρ) ≠ 0, then f(s) = (s-ρ)f'(ρ) + (s-ρ)²r(s) where r is continuous at ρ.
-/

/-- Generic Taylor expansion for an analytic function at a simple zero. -/
theorem taylor_at_simple_zero {f : ℂ → ℂ} {ρ : ℂ}
    (hf_analytic : AnalyticAt ℂ f ρ)
    (hf_zero : f ρ = 0)
    (_hf_simple : deriv f ρ ≠ 0) :
    ∃ (r : ℂ → ℂ), (∀ᶠ s in 𝓝 ρ, f s = (s - ρ) * deriv f ρ + (s - ρ)^2 * r s) ∧
      ContinuousAt r ρ := by
  -- f(s) = (s - ρ) * g(s) where g = dslope f ρ
  let g := dslope f ρ
  have h_g_rho : g ρ = deriv f ρ := dslope_same f ρ
  have h_g_analytic : AnalyticAt ℂ g ρ := analyticAt_dslope hf_analytic

  -- Define r = dslope g ρ
  let r := dslope g ρ
  have h_r_analytic : AnalyticAt ℂ r ρ := analyticAt_dslope h_g_analytic

  use r
  constructor
  · filter_upwards with s
    have h1 : f s - f ρ = (s - ρ) • g s := by rw [← sub_smul_dslope]
    have h2 : g s - g ρ = (s - ρ) • r s := by rw [← sub_smul_dslope]
    simp only [smul_eq_mul] at h1 h2
    rw [hf_zero, sub_zero] at h1
    have h3 : g s = g ρ + (s - ρ) * r s := by
      calc g s = g s - g ρ + g ρ := by ring
        _ = (s - ρ) * r s + g ρ := by rw [h2]
        _ = g ρ + (s - ρ) * r s := by ring
    rw [h_g_rho] at h3
    calc f s = (s - ρ) * g s := h1
      _ = (s - ρ) * (deriv f ρ + (s - ρ) * r s) := by rw [h3]
      _ = (s - ρ) * deriv f ρ + (s - ρ)^2 * r s := by ring
  · exact h_r_analytic.continuousAt

/-- Taylor expansion for Riemann zeta at a simple zero. -/
theorem zeta_taylor_at_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (r : ℂ → ℂ), (∀ᶠ s in 𝓝 ρ, riemannZeta s = (s - ρ) * deriv riemannZeta ρ +
      (s - ρ) ^ 2 * r s) ∧ ContinuousAt r ρ :=
  taylor_at_simple_zero (analyticAt_riemannZeta h_not_one) h_zero h_simple

/-!
## Theorem 2: Log Derivative Pole Structure (Replaces ax_log_deriv_near_zero)

If f(ρ) = 0 and f'(ρ) ≠ 0, then f'/f = 1/(s-ρ) + h(s) where h is differentiable at ρ.
-/

/-- Generic log derivative pole structure for an analytic function at a simple zero. -/
theorem log_deriv_of_simple_zero {f : ℂ → ℂ} {ρ : ℂ}
    (hf_analytic : AnalyticAt ℂ f ρ)
    (hf_zero : f ρ = 0)
    (hf_simple : deriv f ρ ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv f s / f s = (s - ρ)⁻¹ + h s := by
  let g := dslope f ρ
  have h_g_rho : g ρ = deriv f ρ := dslope_same f ρ
  have h_g_ne : g ρ ≠ 0 := by rwa [h_g_rho]
  have h_g_analytic : AnalyticAt ℂ g ρ := analyticAt_dslope hf_analytic
  have _h_g_diff : DifferentiableAt ℂ g ρ := h_g_analytic.differentiableAt

  let h := fun s => deriv g s / g s

  use h
  constructor
  · have h_deriv_g_analytic : AnalyticAt ℂ (deriv g) ρ := h_g_analytic.deriv
    exact h_deriv_g_analytic.div h_g_analytic h_g_ne

  · have h_g_cont : ContinuousAt g ρ := h_g_analytic.continuousAt
    have h_g_ne_near : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := h_g_cont.eventually_ne h_g_ne

    have h_factor : ∀ s, f s = (s - ρ) * g s := fun s => by
      have : f s - f ρ = (s - ρ) • g s := by rw [← sub_smul_dslope]
      simp only [hf_zero, sub_zero, smul_eq_mul] at this
      exact this

    have h_g_diff_near : ∀ᶠ s in 𝓝 ρ, DifferentiableAt ℂ g s :=
      h_g_analytic.eventually_analyticAt.mono fun s hs => hs.differentiableAt

    filter_upwards [h_g_ne_near.filter_mono nhdsWithin_le_nhds,
                    h_g_diff_near.filter_mono nhdsWithin_le_nhds,
                    self_mem_nhdsWithin] with s h_g_s_ne h_g_s_diff h_s_ne

    have h_sub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr h_s_ne

    have h1 : DifferentiableAt ℂ (fun z => z - ρ) s := differentiableAt_id.sub_const ρ
    have _h_f_diff : DifferentiableAt ℂ f s := by
      have h_eq : f =ᶠ[𝓝 s] fun z => (z - ρ) * g z := by
        filter_upwards with z using h_factor z
      exact h_eq.differentiableAt_iff.mpr (h1.mul h_g_s_diff)

    have h_deriv_f : deriv f s = g s + (s - ρ) * deriv g s := by
      have h_eq : f =ᶠ[𝓝 s] fun z => (z - ρ) * g z := by
        filter_upwards with z using h_factor z
      have h_deriv_eq := Filter.EventuallyEq.deriv_eq h_eq
      rw [h_deriv_eq]
      have h_prod := deriv_mul h1 h_g_s_diff
      convert h_prod using 1
      simp only [deriv_sub_const, deriv_id'', one_mul]

    calc deriv f s / f s
        = (g s + (s - ρ) * deriv g s) / ((s - ρ) * g s) := by rw [h_deriv_f, h_factor]
      _ = g s / ((s - ρ) * g s) + (s - ρ) * deriv g s / ((s - ρ) * g s) := by
          rw [add_div]
      _ = 1 / (s - ρ) + deriv g s / g s := by
          field_simp [h_sub_ne, h_g_s_ne]
      _ = (s - ρ)⁻¹ + h s := by
          rw [one_div]

/-- Log derivative pole structure for Riemann zeta at a simple zero. -/
theorem log_deriv_zeta_near_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta s / riemannZeta s = (s - ρ)⁻¹ + h s :=
  log_deriv_of_simple_zero (analyticAt_riemannZeta h_not_one) h_zero h_simple

end ProofEngine.AnalyticBasics
