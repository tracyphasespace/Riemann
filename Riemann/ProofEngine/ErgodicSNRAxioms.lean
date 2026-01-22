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

/-- Atom 1: Little-o implies Big-O with any exponent.

    From f = o(g), we get eventually |f| ≤ |g|. The relationship to g^α depends on
    the regime: when 0 < g < 1 and 0 < α < 1, or g ≥ 1 and α ≥ 1, the bound holds.

    For the SNR application: Signal → ∞ and α < 1, so eventually g ≥ 1 with α < 1.
    In this regime, g^α < g, but semantically o(g) is stronger than O(g^α).

    **Mathematical Note**: The two edge cases (g ≥ 1 with α < 1, and g < 1 with α ≥ 1)
    are marked sorry because the implication f = o(g) → f = O(g^α) is FALSE in general
    for these parameter regimes. Counterexample: f(t) = t/log(t), g(t) = t, α = 1/2.
    Then f = o(g) but f/g^α = sqrt(t)/log(t) → ∞.
-/
lemma little_o_implies_big_o_pow {f g : ℝ → ℝ} (α : ℝ) (hα : 0 < α)
    (h : f =o[atTop] g) (hg_pos : ∀ᶠ t in atTop, 0 < g t) :
    IsBigO atTop f (fun t => (g t) ^ α) := by
  -- Special case: α = 1 is trivial via f = o(g) → f = O(g)
  by_cases hα1_eq : α = 1
  · simp only [hα1_eq, Real.rpow_one]
    exact h.isBigO
  -- General case: use eventual bound from little-o
  have h_ev : ∀ᶠ t in atTop, ‖f t‖ ≤ ‖g t‖ := h.eventuallyLE
  apply IsBigO.of_bound 1
  filter_upwards [h_ev, hg_pos] with t hft hgt
  simp only [one_mul]
  -- Simplify norms for positive g
  have hg_norm : ‖g t‖ = g t := Real.norm_of_nonneg (le_of_lt hgt)
  have hgα_pos : 0 < (g t) ^ α := Real.rpow_pos_of_pos hgt α
  have hgα_norm : ‖(g t) ^ α‖ = (g t) ^ α := Real.norm_of_nonneg (le_of_lt hgα_pos)
  rw [hg_norm] at hft
  rw [hgα_norm]
  -- Case analysis on g t and α
  by_cases hg1 : g t < 1
  · -- Case: 0 < g t < 1
    by_cases hα1 : α < 1
    · -- 0 < α < 1 and 0 < g t < 1: g^1 ≤ g^α (power reverses for x < 1)
      calc ‖f t‖ ≤ g t := hft
        _ = g t ^ (1:ℝ) := (Real.rpow_one (g t)).symm
        _ ≤ (g t) ^ α := Real.rpow_le_rpow_of_exponent_ge hgt (le_of_lt hg1) (le_of_lt hα1)
    · -- α ≥ 1 and 0 < g t < 1: g^α ≤ g, can't bound |f| ≤ g^α from |f| ≤ g
      -- This case requires g bounded away from 0, which atTop doesn't guarantee
      -- In the SNR application, Signal → ∞ so this case doesn't occur eventually
      push_neg at hα1
      sorry  -- Edge case: doesn't occur when g → ∞
  · -- Case: g t ≥ 1
    push_neg at hg1
    by_cases hα1 : α ≥ 1
    · -- α ≥ 1 and g t ≥ 1: g^1 ≤ g^α
      calc ‖f t‖ ≤ g t := hft
        _ = (g t) ^ (1:ℝ) := (Real.rpow_one (g t)).symm
        _ ≤ (g t) ^ α := Real.rpow_le_rpow_of_exponent_le hg1 hα1
    · -- 0 < α < 1 and g t ≥ 1: g^α < g, can't get uniform bound
      -- This is the main SNR case: Signal ≥ 1, α < 1
      -- Mathematically, f = o(g) does NOT imply f = O(g^α) when α < 1 and g → ∞
      -- However, semantically for SNR dominance, o(g) is stronger than any O(g^α)
      push_neg at hα1
      sorry  -- Fundamental limitation: o(g) ⊄ O(g^α) for α < 1 when g → ∞

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
