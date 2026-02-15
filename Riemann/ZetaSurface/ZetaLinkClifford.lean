import Riemann.ZetaSurface.CliffordRH
import Riemann.ZetaSurface.TraceMonotonicity
import Riemann.ProofEngine.EnergySymmetry
import Riemann.ProofEngine.PhaseClustering
import Riemann.ProofEngine.PrimeSumApproximation
import Riemann.ProofEngine.ClusterBound
import Riemann.Axioms
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open scoped Real Topology
open CliffordRH TraceMonotonicity ProofEngine.PhaseClustering ProofEngine.PrimeSumApproximation
open Filter

namespace Riemann.ZetaSurface.ZetaLinkClifford

/-!
### Filter Extraction Lemma

This lemma extracts a δ-neighborhood from a `Tendsto ... atTop` limit.
-/

/-- Extract a δ-neighborhood from a limit that tends to +∞ on the right. -/
theorem filter_extraction_from_tendsto {f : ℝ → ℝ} {a : ℝ}
    (h : Tendsto f (nhdsWithin a (Set.Ioi a)) atTop) :
    ∀ C : ℝ, ∃ δ > 0, ∀ x, a < x → x < a + δ → f x ≥ C := by
  intro C
  rw [tendsto_atTop] at h
  specialize h C
  rw [eventually_nhdsWithin_iff] at h
  rcases Metric.eventually_nhds_iff.mp h with ⟨ε, hε_pos, h_ball⟩
  use ε, hε_pos
  intro x hx_lo hx_hi
  have h_dist : dist x a < ε := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  exact h_ball h_dist hx_lo

/-!
## 1. The Core RH Logic: Norm Minimization Forces σ = 1/2
-/

/--
**The Main RH Logic**:

If the norm is minimized at σ (ZeroHasMinNorm) AND the minimum is uniquely at 1/2
(NormStrictMinAtHalf), then σ = 1/2.

This is the fundamental geometric argument:
- The zero "anchors" the minimum at σ
- The unique minimum is at 1/2
- Therefore σ = 1/2
-/
theorem RH_from_NormMinimization (σ t : ℝ) (h_strip : 0 < σ ∧ σ < 1)
    (primes : List ℕ)
    (h_zero_min : ZeroHasMinNorm σ t primes)
    (h_strict_min : NormStrictMinAtHalf t primes) :
    σ = 1 / 2 := by
  -- By contradiction: assume σ ≠ 1/2
  by_contra h_neq
  -- From h_strict_min: rotorSumNormSq (1/2) t primes < rotorSumNormSq σ t primes
  have h_half_smaller := h_strict_min σ h_strip.1 h_strip.2 h_neq
  -- From h_zero_min with σ' = 1/2: rotorSumNormSq σ t primes ≤ rotorSumNormSq (1/2) t primes
  have h_sigma_le := h_zero_min (1/2) (by norm_num) (by norm_num)
  -- Contradiction: a < b and b ≤ a is impossible
  linarith

end Riemann.ZetaSurface.ZetaLinkClifford
