import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Riemann.ProofEngine.SNRAxioms
-- CYCLE: import Riemann.GlobalBound.InteractionTerm

noncomputable section
open Real Filter Topology Asymptotics

namespace ProofEngine

/-!
## Interaction Helper Lemmas (Atomic Units)

These atomic lemmas support the Signal vs Noise analysis.
The main theorems that reference GlobalBound types are in GlobalBound.InteractionTerm.
-/

/-- Atom 1: If Signal > |Noise| and Signal > 0, then Signal + Noise > 0. -/
lemma sum_pos_of_dominance {Signal Noise : ℝ}
    (h_sig : Signal > 0)
    (h_dom : Signal > |Noise|) :
    Signal + Noise > 0 := by
  have h_bound : Signal + Noise ≥ Signal - |Noise| := by
    linarith [neg_abs_le Noise]
  linarith

/-- Atom 2: If SNR > 1, then Signal > |Noise|. -/
lemma snr_implies_dominance {Signal Noise : ℝ}
    (h_sig : Signal > 0)
    (h_snr : Signal / |Noise| > 1)
    (h_noise_ne : Noise ≠ 0) :
    Signal > |Noise| := by
  have h_abs_pos : |Noise| > 0 := abs_pos.mpr h_noise_ne
  have h := (lt_div_iff₀ h_abs_pos).mp h_snr
  linarith

-- NOTE: snr_diverges_to_infinity_proven and geometry_dominates_noise_proven
-- are defined in GlobalBound.InteractionTerm to avoid import cycles.

end ProofEngine
