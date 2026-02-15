import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
-- import Mathlib.Topology.Algebra.Order.Filter  -- REMOVED: module does not exist
import Mathlib.Tactic.Linarith
-- CYCLE: import Riemann.GlobalBound.SNR_Bounds

noncomputable section
open Real Filter Topology Asymptotics

namespace ProofEngine

/-!
## SNR Helper Lemmas (Atomic Units)
-/

/-- Atom 1: Power law divergence. x^b -> inf for b > 0. -/
lemma rpow_divergence_of_pos {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ b) atTop atTop :=
  tendsto_rpow_atTop hb

/-- Atom 2: Ratio of growth rates. x / x^a = x^(1-a). -/
lemma growth_ratio_eq (x : ℝ) (hx : 0 < x) (a : ℝ) :
    x / x ^ a = x ^ (1 - a) := by
  nth_rw 1 [← rpow_one x]
  rw [← rpow_sub hx]

/-- Atom 3: If f = O(g^a) and g -> inf, then g/|f| -> inf for a < 1.
    Note: requires f ≠ 0 eventually to avoid division by zero. -/
theorem isBigO_ratio_divergence {α : ℝ} (hα : α < 1)
    {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (h_bound : IsBigO l f (fun i => (g i) ^ α))
    (h_g_pos : ∀ᶠ i in l, 0 < g i)
    (h_f_ne0 : ∀ᶠ i in l, f i ≠ 0) -- needed to avoid div by 0
    (h_g_lim : Tendsto g l atTop) :
    Tendsto (fun i => g i / |f i|) l atTop := by
  -- Step 1: Extract constant C > 0 from IsBigO
  rw [isBigO_iff] at h_bound
  obtain ⟨C, hC⟩ := h_bound
  -- hC : ∀ᶠ i in l, ‖f i‖ ≤ C * ‖g i ^ α‖
  -- Step 2: Get C' > 0 to avoid division issues
  set C' := max C 1 with hC'_def
  have hC'_pos : 0 < C' := lt_max_of_lt_right one_pos
  -- Step 3: Eventually we have the key inequality
  have h_ineq : ∀ᶠ i in l, C'⁻¹ * (g i) ^ (1 - α) ≤ g i / |f i| := by
    filter_upwards [hC, h_g_pos, h_f_ne0, h_g_lim.eventually_ge_atTop 1] with i hCi hgi hfi hgi_ge1
    -- For g i ≥ 1 > 0, we have |g i ^ α| = g i ^ α
    have h_gpow_eq : ‖(g i) ^ α‖ = (g i) ^ α := by
      rw [Real.norm_eq_abs]
      rw [abs_rpow_of_nonneg (le_of_lt hgi)]
      rw [abs_of_pos hgi]
    -- Also |f i| ≤ C * g i ^ α ≤ C' * g i ^ α
    have h_fi_bound : |f i| ≤ C' * (g i) ^ α := by
      calc |f i| = ‖f i‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖(g i) ^ α‖ := hCi
        _ = C * (g i) ^ α := by rw [h_gpow_eq]
        _ ≤ C' * (g i) ^ α := by apply mul_le_mul_of_nonneg_right (le_max_left _ _)
                                  (rpow_nonneg (le_of_lt hgi) _)
    -- Since f i ≠ 0, we have |f i| > 0
    have h_fi_pos : 0 < |f i| := abs_pos.mpr hfi
    have h_gpow_pos : 0 < (g i) ^ α := rpow_pos_of_pos hgi α
    calc C'⁻¹ * (g i) ^ (1 - α)
        = C'⁻¹ * ((g i) ^ (1 : ℝ) * (g i) ^ (-α)) := by
          rw [← rpow_add hgi]
          ring_nf
        _ = C'⁻¹ * (g i * (g i) ^ (-α)) := by
          rw [rpow_one]
        _ = C'⁻¹ * (g i / (g i) ^ α) := by
          rw [rpow_neg (le_of_lt hgi), div_eq_mul_inv]
        _ = g i / (C' * (g i) ^ α) := by
          field_simp
        _ ≤ g i / |f i| := by
          apply div_le_div_of_nonneg_left (le_of_lt hgi) h_fi_pos h_fi_bound
  -- Step 4: Show C'⁻¹ * g^(1-α) → +∞
  have h_base_div : Tendsto (fun i => C'⁻¹ * (g i) ^ (1 - α)) l atTop := by
    have h_exp_pos : 0 < 1 - α := by linarith
    have h_gpow_lim : Tendsto (fun i => (g i) ^ (1 - α)) l atTop := by
      -- Strategy: g → +∞ implies g^(1-α) → +∞ when 1-α > 0
      -- Use rpow_atTop composed with g
      have h1 : Tendsto (fun x : ℝ => x ^ (1 - α)) atTop atTop := tendsto_rpow_atTop h_exp_pos
      refine (h1.comp h_g_lim).congr' ?_
      -- The composition gives (g i)^(1-α), which is already what we want
      exact Eventually.of_forall (fun _ => rfl)
    exact Tendsto.const_mul_atTop (inv_pos.mpr hC'_pos) h_gpow_lim
  -- Step 5: Conclude by comparison
  exact tendsto_atTop_mono' l h_ineq h_base_div

-- NOTE: snr_diverges_proven moved to GlobalBound.SNR_Bounds to avoid import cycle.
-- The helper lemmas above (rpow_divergence_of_pos, growth_ratio_eq, isBigO_ratio_divergence)
-- are the atomic units that can be proven from Mathlib.

end ProofEngine
