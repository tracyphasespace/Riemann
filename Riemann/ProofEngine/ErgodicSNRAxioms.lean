import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
-- CYCLE: import Riemann.GlobalBound.InteractionTerm
-- CYCLE: import Riemann.GlobalBound.SNR_Bounds

noncomputable section
open Real Filter Topology Asymptotics

namespace ProofEngine

/-!
## Ergodic SNR Helper Lemmas (Atomic Units)

These atomic lemmas support the ergodic argument that Noise = o(Signal).
The main theorems that reference GlobalBound types are in GlobalBound.ErgodicSNR.
-/

/-- For f = o(g) with g → ∞ and α ≥ 1, we have f = O(g^α).

    **IMPORTANT**: This requires α ≥ 1. The theorem is FALSE for 0 < α < 1.
    Counterexample: f(t) = √t, g(t) = t. Then f = o(g) but f/g^{1/2} = 1 (not decaying).

    **Hypothesis change (2026-01-23)**: Changed from `0 < α` to `1 ≤ α` to make theorem true.
    See Mathlib427Compat.lean for documentation. -/
lemma little_o_implies_big_o_pow {f g : ℝ → ℝ} (α : ℝ) (hα : 1 ≤ α)
    (h : f =o[atTop] g) (hg_pos : ∀ᶠ t in atTop, 0 < g t)
    (hg_large : ∀ᶠ t in atTop, 1 ≤ g t) :
    IsBigO atTop f (fun t => (g t) ^ α) := by
  have h_ev : ∀ᶠ t in atTop, ‖f t‖ ≤ ‖g t‖ := h.eventuallyLE
  apply IsBigO.of_bound 1
  filter_upwards [h_ev, hg_pos, hg_large] with t hft hgt hg1
  simp only [one_mul]
  have hg_norm : ‖g t‖ = g t := Real.norm_of_nonneg (le_of_lt hgt)
  have hgα_pos : 0 < (g t) ^ α := Real.rpow_pos_of_pos hgt α
  have hgα_norm : ‖(g t) ^ α‖ = (g t) ^ α := Real.norm_of_nonneg (le_of_lt hgα_pos)
  rw [hg_norm] at hft
  rw [hgα_norm]
  -- α ≥ 1 and g t ≥ 1 implies g^1 ≤ g^α
  calc ‖f t‖ ≤ g t := hft
    _ = (g t) ^ (1:ℝ) := (Real.rpow_one (g t)).symm
    _ ≤ (g t) ^ α := Real.rpow_le_rpow_of_exponent_le hg1 hα

/-- Atom 2: Oscillating integral average tends to zero (Riemann-Lebesgue type). -/
lemma oscillating_average_tends_to_zero (ω : ℝ) (hω : ω ≠ 0) :
    Tendsto (fun T => (1/T) * (Real.sin (ω * T) - Real.sin 0) / ω) atTop (𝓝 0) := by
  -- sin(0) = 0, so simplify
  simp only [Real.sin_zero, sub_zero]
  -- Rewrite as (T⁻¹) * (sin(ωT) / ω)
  have h_eq : ∀ T, (1/T) * Real.sin (ω * T) / ω = (T⁻¹) * (Real.sin (ω * T) / ω) := by
    intro T
    ring
  simp_rw [h_eq]
  -- Use: (f → 0) ∧ (g bounded) ⟹ (f * g → 0)
  apply Tendsto.zero_mul_isBoundedUnder_le
  · -- 1/T → 0 as T → ∞
    exact tendsto_inv_atTop_zero
  · -- ‖sin(ωT)/ω‖ ≤ 1/|ω| (bounded)
    apply isBoundedUnder_of
    use |ω|⁻¹
    intro T
    simp only [Function.comp_apply]
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have h_sin_le : |Real.sin (ω * T)| ≤ 1 := Real.abs_sin_le_one _
    have h_omega_pos : 0 < |ω| := abs_pos.mpr hω
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_right h_sin_le (le_of_lt h_omega_pos)

-- NOTE: ergodic_noise_is_little_o_proven and ergodic_implies_pair_correlation_proven
-- are defined in GlobalBound.ErgodicSNR to avoid import cycles.

end ProofEngine
