import Riemann.ZetaSurface.CliffordRH
import Riemann.ZetaSurface.TraceMonotonicity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Order.Field
import Riemann.ProofEngine.Residues
import Riemann.ProofEngine.AnalyticBasics

open Complex Real Filter Topology BigOperators TraceMonotonicity
open ProofEngine.AnalyticBasics ProofEngine.Residues

noncomputable section

namespace ProofEngine.PhaseClustering

/-!
## Axioms for Phase Clustering

These axioms encapsulate the analytical machinery needed to connect
pole divergence to phase clustering. They will be reduced to helper
lemmas in future work.
-/

/--
**Lemma: Filter Arithmetic for Pole Domination (PROVEN)**
If f → -∞ and g is bounded, then f + g → -∞.
-/
lemma tendsto_atBot_add_bounded {f g : ℝ → ℝ} {l : Filter ℝ}
    (hf : Tendsto f l atBot)
    (hg : ∃ M : ℝ, ∀ x, |g x| ≤ M) :
    Tendsto (f + g) l atBot := by
  rw [tendsto_atBot] at hf ⊢
  intro b
  obtain ⟨M, hM⟩ := hg
  -- For f + g ≤ b, we need f ≤ b - M (since g ≤ M)
  have hf_ev := hf (b - M)
  filter_upwards [hf_ev] with x hfx
  -- From |g x| ≤ M we get g x ≤ M
  have hgx : g x ≤ M := le_abs_self (g x) |>.trans (hM x)
  -- (f + g) x = f x + g x
  simp only [Pi.add_apply]
  linarith

/--
**Lemma: Filter Arithmetic for Convergent Remainder**
If f → -∞ and g → c (converges to some real c), then f + g → -∞.
-/
lemma tendsto_atBot_add_convergent {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  refine tendsto_atBot.2 fun a => ?_
  -- g eventually stays in (c-1, c+1), so g ≤ c+1 eventually
  have hg_bd : ∀ᶠ x in l, g x ≤ c + 1 := by
    have h_mem : Set.Ioo (c - 1) (c + 1) ∈ 𝓝 c :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hg.eventually h_mem] with x hx
    exact le_of_lt hx.2
  have hf' : ∀ᶠ x in l, f x ≤ a - (c + 1) := tendsto_atBot.1 hf (a - (c + 1))
  filter_upwards [hf', hg_bd] with x hfx hgx
  linarith

/--
**Lemma: Derivative of Negation (PROVEN)**
deriv(-f) = -deriv(f), and this commutes with taking real parts.
Uses Mathlib's `deriv.neg` from `Analysis.Calculus.Deriv.Add`.
-/
lemma deriv_neg_re {f : ℂ → ℂ} (z : ℂ) :
    (deriv (fun w => -f w) z).re = -(deriv f z).re := by
  -- deriv(-f) = -deriv(f) by Mathlib's deriv.neg
  have h : deriv (fun w => -f w) z = -deriv f z := deriv.neg
  rw [h, Complex.neg_re]

/--
**Lemma: List foldl Equivalence for Weighted Sums**
The two formulations (log p * log p) and (log p)^2 are equal in foldl.
This is provable since x * x = x^2 by definition.
-/
lemma foldl_sq_eq (primes : List ℕ) (σ t : ℝ) :
    primes.foldl (fun (acc : ℝ) (p : ℕ) =>
      acc + Real.log p * Real.log p * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0 =
    primes.foldl (fun (acc : ℝ) (p : ℕ) =>
      acc + (Real.log p)^2 * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0 := by
  congr 1
  ext acc p
  ring

/-!
## DELETED: ax_global_phase_clustering (2026-02-13)

**WHY DELETED**: Dead code. The main theorem `Clifford_RH_Derived` computed
`_h_mono := derived_monotonicity ...` but never used the result (underscore prefix).
The proof only uses `h_norm_min` and `h_zero_norm` via `RH_from_NormMinimization`.

The axiom encapsulated the von Mangoldt Explicit Formula: at a zeta zero,
the weighted cosine sum Σ (log p)² p^(-σ) cos(t log p) < 0 for all σ ∈ (0,1).
This remains mathematically interesting but is not on the proof path.
-/

/-!
## 1. The Analytic Machinery: Pole of ζ'/ζ
Instead of axioms, we use the rigorously proven `log_deriv_zeta_near_zero`
from `AnalyticBasics.lean`, which establishes that ζ'/ζ has a simple pole.
-/

/--
**Helper Lemma**: Standard limit -1/x → -∞ as x → 0⁺.
-/
theorem tendsto_neg_inv_nhdsGT_zero :
    Tendsto (fun x : ℝ => -x⁻¹) (𝓝[>] (0 : ℝ)) atBot := by
  have h1 : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun y : ℝ => -y) atTop atBot :=
    tendsto_neg_atTop_atBot
  exact h2.comp h1

/--
**Helper Lemma**: Translation of the limit to z₀.re.
-/
theorem tendsto_neg_inv_sub_nhdsGT (x₀ : ℝ) :
    Tendsto (fun x : ℝ => -(x - x₀)⁻¹) (𝓝[>] x₀) atBot := by
  have h_sub : Tendsto (fun σ => σ - x₀) (𝓝[>] x₀) (𝓝[>] 0) := by
    have h1 : Tendsto (fun σ => σ - x₀) (𝓝 x₀) (𝓝 0) := by
      have := continuous_sub_right x₀ |>.tendsto x₀
      simp only [sub_self] at this
      exact this
    have h2 : Tendsto (fun σ => σ - x₀) (𝓝[>] x₀) (𝓝 0) :=
      h1.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h2 ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ ⊢
    linarith
  have h_inv := tendsto_neg_inv_nhdsGT_zero.comp h_sub
  simp only [Function.comp_def] at h_inv ⊢
  exact h_inv

/--
**Theorem: Divergence of the Negative Log Derivative**
For a simple zero ρ, the real part of -ζ'/ζ diverges to -∞ on the horizontal approach.
-/
theorem log_deriv_neg_divergence_at_zero (ρ : ℂ)
    (h_zero : riemannZeta ρ = 0) (h_not_one : ρ ≠ 1) (h_simple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun σ : ℝ => (-(deriv riemannZeta (σ + ρ.im * I) / riemannZeta (σ + ρ.im * I))).re)
      (𝓝[>] ρ.re) atBot := by
  -- 1. Get the pole structure: ζ'/ζ = 1/(s-ρ) + h
  obtain ⟨h, _h_diff, _h_eq⟩ := log_deriv_zeta_near_zero ρ h_zero h_not_one h_simple
  -- 2. On the line, Re(1/(s-ρ)) = 1/(σ-ρ.re)
  have h_pole_lim := pole_real_part_tendsto_atTop ρ
  -- 3. We want the limit of the NEGATIVE, so it goes to atBot
  have h_neg_pole : Tendsto (fun σ : ℝ => -((σ : ℂ) + ρ.im * I - ρ)⁻¹.re) (𝓝[>] ρ.re) atBot :=
    tendsto_neg_atTop_atBot.comp h_pole_lim
  -- 4. The remainder h(s) converges along the horizontal approach
  have h_cont : ContinuousAt h ρ := _h_diff.continuousAt
  have hz : Tendsto (fun σ : ℝ => (σ : ℂ) + ρ.im * I) (𝓝[>] ρ.re) (𝓝 ρ) := by
    have hcont : Tendsto (fun σ : ℝ => (σ : ℂ) + ρ.im * I) (𝓝 ρ.re) (𝓝 ρ) := by
      have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 ρ.re) (𝓝 (ρ.re : ℂ)) :=
        Complex.continuous_ofReal.continuousAt
      have h2 : Tendsto (fun _ : ℝ => ρ.im * I) (𝓝 ρ.re) (𝓝 (ρ.im * I)) :=
        tendsto_const_nhds
      have h12 := h1.add h2
      convert h12 using 2
      exact (Complex.re_add_im ρ).symm
    exact hcont.mono_left nhdsWithin_le_nhds
  have h_rem_tendsto :
      Tendsto (fun σ : ℝ => (-(h ((σ : ℂ) + ρ.im * I))).re) (𝓝[>] ρ.re) (𝓝 (-(h ρ)).re) := by
    have hh : Tendsto h (𝓝 ρ) (𝓝 (h ρ)) := h_cont.tendsto
    have hh_line : Tendsto (fun σ : ℝ => h ((σ : ℂ) + ρ.im * I)) (𝓝[>] ρ.re) (𝓝 (h ρ)) :=
      hh.comp hz
    have hh_line_neg : Tendsto (fun σ : ℝ => -(h ((σ : ℂ) + ρ.im * I))) (𝓝[>] ρ.re) (𝓝 (-h ρ)) :=
      hh_line.neg
    exact Complex.continuous_re.continuousAt.tendsto.comp hh_line_neg
  -- 5. Show points on horizontal line with σ > ρ.re are ≠ ρ
  have hz_ne : Tendsto (fun σ : ℝ => (σ : ℂ) + ρ.im * I) (𝓝[>] ρ.re) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h_eq
    have hre : σ = ρ.re := by
      have := congrArg Complex.re h_eq
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_self] at this
      linarith
    linarith
  -- 6. Transfer the pole decomposition to the horizontal line
  have h_eq_line : ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re,
        deriv riemannZeta ((σ : ℂ) + ρ.im * I) / riemannZeta ((σ : ℂ) + ρ.im * I)
          = (((σ : ℂ) + ρ.im * I) - ρ)⁻¹ + h ((σ : ℂ) + ρ.im * I) :=
    hz_ne.eventually _h_eq
  have h_congr :
      (fun σ : ℝ => (-(deriv riemannZeta (σ + ρ.im * I) / riemannZeta (σ + ρ.im * I))).re)
        =ᶠ[𝓝[>] ρ.re]
      (fun σ : ℝ => (-(((σ : ℂ) + ρ.im * I - ρ)⁻¹)).re + (-(h ((σ : ℂ) + ρ.im * I))).re) := by
    filter_upwards [h_eq_line] with σ hσ
    simp only [hσ, neg_add, Complex.add_re, Complex.neg_re]
  -- 7. Combine: -∞ + convergent = -∞
  have h_sum :
      Tendsto (fun σ : ℝ => (-(((σ : ℂ) + ρ.im * I - ρ)⁻¹)).re + (-(h ((σ : ℂ) + ρ.im * I))).re)
        (𝓝[>] ρ.re) atBot :=
    tendsto_atBot_add_convergent h_neg_pole h_rem_tendsto
  exact h_sum.congr' h_congr.symm

/-!
## 2. The Derivative Divergence (Stiffness)
We prove the "Stiffness" (second derivative) goes to -∞ (without the minus sign).
This uses `stiffness_real_part_tendsto_atBot` from Residues.lean.
-/

/--
**Theorem: Infinite Stiffness at the Zero**
The derivative of the "Force" goes to +∞ (for -ζ'/ζ).
-/
theorem log_deriv_derivative_divergence (ρ : ℂ)
    (h_strip : 0 < ρ.re ∧ ρ.re < 1)
    (h_zero : riemannZeta ρ = 0)
    (h_simple : deriv riemannZeta ρ ≠ 0) :
    Filter.Tendsto (fun σ : ℝ =>
      (deriv (fun z => -(deriv riemannZeta z / riemannZeta z)) (σ + ρ.im * I)).re)
    (𝓝[>] ρ.re) Filter.atTop := by
  -- ρ ≠ 1 because it is inside the critical strip
  have h_not_one : ρ ≠ 1 := by
    intro h_eq; rw [h_eq] at h_strip; simp only [one_re] at h_strip; linarith [h_strip.2]
  -- The stiffness of ζ'/ζ goes to -∞
  have h_stiff := stiffness_real_part_tendsto_atBot ρ h_zero h_not_one h_simple
  -- deriv(-f) = -deriv(f), so Re(deriv(-f)) = -Re(deriv(f))
  -- If Re(deriv f) → -∞, then -Re(deriv f) → +∞
  have h_flip : Tendsto (fun σ : ℝ =>
      -(deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re)
      (𝓝[>] ρ.re) Filter.atTop :=
    tendsto_neg_atBot_atTop.comp h_stiff
  -- Apply lemma for derivative linearity
  convert h_flip using 1
  ext σ
  exact deriv_neg_re (σ + ρ.im * I)

/-!
## 3. The Local Clustering Theorem
This replaces the "Global Axiom". We PROVE clustering *locally* near the zero
using the `AdmissibleStiffnessApproximation` hypothesis from Residues.lean.
-/

/--
**Lemma: weightedCosSum equals the NegativePhaseClustering sum**
-/
lemma weightedCosSum_eq_clustering_sum (primes : List ℕ) (σ t : ℝ) :
    weightedCosSum primes σ t =
      primes.foldl (fun (acc : ℝ) (p : ℕ) =>
        acc + (Real.log p)^2 * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0 := by
  unfold weightedCosSum
  exact foldl_sq_eq primes σ t

/--
**Theorem: Local Negative Phase Clustering**
Instead of assuming it globally, we PROVE it holds in a neighborhood of the zero
using the domination argument from Residues.lean.
-/
theorem local_clustering_at_zero (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_strip : 0 < ρ.re ∧ ρ.re < 1)
    (h_simple : deriv riemannZeta ρ ≠ 0)
    (primes : List ℕ) (h_primes : ∀ p ∈ primes, Nat.Prime p)
    (h_approx : AdmissibleStiffnessApproximation ρ primes) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Set.Ioo ρ.re (ρ.re + δ),
      NegativePhaseClustering σ ρ.im primes := by
  -- 1. Apply the theorem from Residues.lean that proves the Finite Sum < 0
  have h_res := zeta_zero_gives_negative_clustering ρ h_zero h_strip h_simple primes h_primes h_approx
  -- 2. Re-pack as the `NegativePhaseClustering` definition
  obtain ⟨δ, hδ_pos, h_neg⟩ := h_res
  use δ, hδ_pos
  intro σ hσ
  unfold NegativePhaseClustering
  -- Use the lemma to convert between the two sum formulations
  rw [← weightedCosSum_eq_clustering_sum]
  exact h_neg σ hσ

end ProofEngine.PhaseClustering
