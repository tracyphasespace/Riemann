import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Filter
import Mathlib.Tactic.Linarith
-- CYCLE: import Riemann.GlobalBound.InteractionTerm
import Riemann.ProofEngine.SNRAxioms

noncomputable section
open Real Filter Topology Asymptotics GlobalBound

namespace ProofEngine

/-!
## Interaction Helper Lemmas (Atomic Units)
-/

/-- Atom 1: If SNR > 1 and Signal > 0, then Analytic Energy (Signal + Interaction) > 0. -/
lemma analytic_pos_of_snr_gt_one {S : Finset ℕ} {t : ℝ} 
    (h_sig : IdealEnergy S t > 0)
    (h_snr : IdealEnergy S t / |InteractionEnergy S t| > 1) :
    AnalyticEnergy S t > 0 := by
  -- Analytic = Ideal + Interaction
  rw [AnalyticEnergy, InteractionEnergy] at *
  -- (Ideal / |Inter|) > 1 => Ideal > |Inter|
  have h_inter_nz : InteractionEnergy S t ≠ 0 := by
    intro h_zero
    rw [h_zero, abs_zero] at h_snr
    -- Lean's x / 0 = 0
    simp at h_snr
  
  have h_abs_pos : |InteractionEnergy S t| > 0 := abs_pos.mpr h_inter_nz
  have h_dom : IdealEnergy S t > |InteractionEnergy S t| := (lt_div_iff₀ h_abs_pos).mp h_snr
  
  -- Ideal + Interaction >= Ideal - |Inter| > 0
  have h_bound : IdealEnergy S t + InteractionEnergy S t ≥ IdealEnergy S t - |InteractionEnergy S t| := by
    linarith [le_abs_self (InteractionEnergy S t)]
  
  linarith

/-- 
Replacement for `GlobalBound.snr_diverges_to_infinity`.
Logic reused from SNRAxioms.
-/
theorem snr_diverges_to_infinity_proven (primes : List ℕ)
    (h_corr : PairCorrelationBound primes)
    (h_signal_grows : Tendsto (fun t => IdealEnergy primes.toFinset t) atTop atTop) :
    Tendsto (fun t => IdealEnergy primes.toFinset t / |InteractionEnergy primes.toFinset t|)
            atTop atTop := by
  -- Reuse general big-O ratio divergence logic
  apply isBigO_ratio_divergence h_corr.h_alpha
  · exact h_corr.noise_is_subdominant
  · exact h_signal_grows (Ioi_mem_atTop 0)
  · exact h_signal_grows

/--
Replacement for `GlobalBound.geometry_dominates_noise_asymptotic`.
-/
theorem geometry_dominates_noise_proven (primes : List ℕ)
    (h_corr : PairCorrelationBound primes)
    (h_signal_grows : Tendsto (fun t => IdealEnergy primes.toFinset t) atTop atTop) :
    ∀ᶠ t in atTop, AnalyticEnergy primes.toFinset t > 0 := by
  -- 1. SNR -> infinity
  have h_snr_lim := snr_diverges_to_infinity_proven primes h_corr h_signal_grows
  -- 2. SNR > 1 eventually
  have h_snr_gt_one := h_snr_lim (Ioi_mem_atTop 1)
  -- 3. Ideal > 0 eventually
  have h_sig_pos := h_signal_grows (Ioi_mem_atTop 0)
  
  filter_upwards [h_snr_gt_one, h_sig_pos] with t h_snr h_sig
  exact analytic_pos_of_snr_gt_one h_sig h_snr

end ProofEngine
