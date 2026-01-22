import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Linarith

noncomputable section
open Real Filter Topology Set

namespace ProofEngine

/-!
## Calculus Helper Lemmas (Atomic Units)
-/

/--
Atom 1: Taylor's theorem with second-order remainder (Lagrange form).
For C² functions, f(x) = f(x₀) + f'(x₀)(x-x₀) + f''(c)(x-x₀)²/2 for some c between x₀ and x.
-/
lemma taylor_second_order {f : ℝ → ℝ} {x₀ x : ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ c ∈ Icc (min x₀ x) (max x₀ x),
      f x = f x₀ + (deriv f x₀) * (x - x₀) + (deriv (deriv f) c) * (x - x₀)^2 / 2 := by
  -- AI2 ATTEMPTED: 3-case proof with reflection
  -- FAILED: API mismatches (deriv_comp_sub_const doesn't exist, etc.)
  -- NEEDS: Rework with correct Mathlib 4.27 derivative composition lemmas
  sorry

/-- 
Replacement for `ax_effective_critical_convex_implies_near_min`.
Effective convexity at the critical line forces a strict trace minimum.
-/
theorem effective_convex_implies_min_proven
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (f'' : ℝ → ℝ)
    (σ t δ ε : ℝ)
    (hσ : 0 < σ ∧ σ < 1 ∧ σ ≠ 1 / 2)
    (hδ : 0 < δ)
    (hε : 0 < ε)
    (hε_small : ε < δ * |σ - 1 / 2| / 2)
    (hf_diff : ∀ ξ ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)), HasDerivAt f (f' ξ) ξ)
    (hf'_diff : ∀ ξ ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)), HasDerivAt f' (f'' ξ) ξ)
    (h_f'_bound : |f' (1 / 2)| ≤ ε)
    (h_f''_convex : ∀ ξ ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)), f'' ξ ≥ δ) :
    f σ > f (1 / 2) := by
  -- Use Taylor expansion at 1/2:
  -- f(σ) = f(1/2) + f'(1/2)(σ - 1/2) + f''(c)(σ - 1/2)^2 / 2 for some c in the interval
  -- f(σ) - f(1/2) = f'(1/2)(σ - 1/2) + f''(c)(σ - 1/2)^2 / 2
  -- Key bounds:
  --   |f'(1/2)(σ - 1/2)| ≤ ε |σ - 1/2|
  --   f''(c)(σ - 1/2)^2 / 2 ≥ δ (σ - 1/2)^2 / 2
  -- Since ε < δ |σ - 1/2| / 2, second order term dominates first order term.

  -- Let d = σ - 1/2
  set d := σ - 1 / 2 with hd_def

  -- d ≠ 0 since σ ≠ 1/2
  have hd_ne : d ≠ 0 := sub_ne_zero.mpr hσ.2.2

  -- d² > 0
  have hd_sq_pos : d ^ 2 > 0 := sq_pos_of_ne_zero hd_ne

  -- |d| > 0
  have hd_abs_pos : |d| > 0 := abs_pos.mpr hd_ne

  -- 1/2 is in the interval
  have h_half_mem : (1 : ℝ) / 2 ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)) := by
    simp only [Set.mem_Icc, min_le_iff, le_max_iff]
    constructor <;> right <;> linarith

  -- The key inequality: from ε < δ |d| / 2, we get ε |d| < δ d² / 2
  have h_dom : ε * |d| < δ * d ^ 2 / 2 := by
    have h1 : ε < δ * |d| / 2 := hε_small
    have h2 : ε * |d| < δ * |d| / 2 * |d| := mul_lt_mul_of_pos_right h1 hd_abs_pos
    have h3 : δ * |d| / 2 * |d| = δ * |d| ^ 2 / 2 := by ring
    rw [h3, sq_abs] at h2
    exact h2

  -- Need Taylor expansion to get c such that:
  -- f(σ) - f(1/2) = f'(1/2) * d + f''(c) * d² / 2
  -- This requires ContDiff ℝ 2 or equivalent differentiability.

  -- From the HasDerivAt hypotheses, we can show f is C² on the interval.
  -- For now, we construct the Taylor bound directly using the hypotheses.

  -- First order contribution: f'(1/2) * d is bounded by ε |d|
  have h_first_bound : |f' (1 / 2) * d| ≤ ε * |d| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right h_f'_bound (abs_nonneg d)

  -- Lower bound on first order term
  have h_first_lower : f' (1 / 2) * d ≥ -(ε * |d|) := by
    have := neg_abs_le (f' (1 / 2) * d)
    linarith [h_first_bound]

  -- The argument requires Taylor's theorem to get c with f''(c) ≥ δ
  -- such that f(σ) - f(1/2) = f'(1/2)*d + f''(c)*d²/2.
  -- Then: f(σ) - f(1/2) ≥ -ε|d| + δd²/2 > 0 (since ε|d| < δd²/2)

  -- To complete this proof rigorously, we need taylor_second_order applied to f.
  -- The HasDerivAt hypotheses give us the required differentiability locally.
  -- For now, we note this follows from standard Taylor expansion arguments.

  -- PROOF SKETCH:
  -- 1. Construct ContDiff ℝ 2 f locally from hf_diff and hf'_diff
  -- 2. Apply taylor_second_order to get c ∈ Icc with Taylor expansion
  -- 3. Use h_f''_convex: f''(c) ≥ δ since c is in the interval
  -- 4. Combine: f(σ) - f(1/2) = f'(1/2)*d + f''(c)*d²/2 ≥ -ε|d| + δd²/2 > 0

  sorry -- Needs: local ContDiff construction from HasDerivAt, then apply taylor_second_order

end ProofEngine
