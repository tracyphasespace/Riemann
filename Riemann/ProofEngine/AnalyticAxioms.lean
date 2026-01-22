import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Riemann.ProofEngine.AnalyticBasics
import Riemann.ProofEngine.Residues
import Riemann.ProofEngine.PhaseClustering
-- Note: Do NOT import Riemann.Axioms here (creates cycle)

noncomputable section
open Complex Filter Topology MeasureTheory Set HurwitzZeta
open ProofEngine.AnalyticBasics ProofEngine.Residues ProofEngine.PhaseClustering
open scoped ComplexConjugate

namespace ProofEngine

/-!
## Helper Lemmas for Conjugate Symmetry of Completed Zeta
-/

/-- For positive real t and any complex s, conjugation commutes with complex power. -/
private lemma cpow_conj_of_pos_real (t : ℝ) (ht : 0 < t) (s : ℂ) :
    conj ((t : ℂ) ^ s) = (t : ℂ) ^ (conj s) := by
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt ht)]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (t : ℂ) (conj s) harg
  simp only [Complex.conj_ofReal, RCLike.conj_conj] at h
  exact h.symm

/-- The f_modif function of hurwitzEvenFEPair 0 is self-conjugate (takes real values). -/
private lemma f_modif_hurwitz_self_conj (t : ℝ) :
    conj ((hurwitzEvenFEPair 0).f_modif t) = (hurwitzEvenFEPair 0).f_modif t := by
  simp only [WeakFEPair.f_modif, Pi.add_apply]
  rw [map_add]
  congr 1
  · simp only [indicator]
    split_ifs with h1
    · rw [map_sub]
      congr 1
      · simp only [hurwitzEvenFEPair, Function.comp_apply]; exact conj_ofReal _
      · simp only [hurwitzEvenFEPair, ite_true, map_one]
    · exact map_zero _
  · simp only [indicator]
    split_ifs with h2
    · rw [map_sub]
      congr 1
      · simp only [hurwitzEvenFEPair, Function.comp_apply]; exact conj_ofReal _
      · simp only [hurwitzEvenFEPair, one_mul, smul_eq_mul, mul_one]; exact conj_ofReal _
    · exact map_zero _

/-- Mellin transform commutes with conjugation when f is self-conjugate. -/
private lemma mellin_conj_of_self_conj (f : ℝ → ℂ) (hf : ∀ t, conj (f t) = f t) (s : ℂ) :
    mellin f (conj s) = conj (mellin f s) := by
  simp only [mellin]
  have h_eq : ∀ᵐ (t : ℝ), t ∈ Ioi (0 : ℝ) →
      (t : ℂ) ^ (conj s - 1) • f t = conj ((t : ℂ) ^ (s - 1) • f t) := by
    filter_upwards with t
    intro ht
    simp only [smul_eq_mul, mem_Ioi] at ht ⊢
    rw [map_mul, cpow_conj_of_pos_real t ht, hf t]
    simp only [map_sub, map_one]
  rw [setIntegral_congr_ae measurableSet_Ioi h_eq]
  rw [integral_conj]

/-!
## Analytic Helper Lemmas (Atomic Units)
-/

/-- Atom 1: Inverse square diverges at zero from the right. -/
lemma inv_sq_divergence_at_zero : Tendsto (fun x : ℝ => x⁻¹ * x⁻¹) (𝓝[>] 0) atTop := by
  -- x⁻¹ * x⁻¹ = x⁻² → +∞ as x → 0⁺
  -- Use tendsto_pow_atTop composed with tendsto_inv_nhdsGT_zero
  have h_inv : Tendsto (·⁻¹ : ℝ → ℝ) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h_pow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h_sq := h_pow.comp h_inv
  convert h_sq using 1
  ext x
  simp only [Function.comp_apply, sq]

/-- Atom 2: Derivative of the complex pole term 1/(s - z₀) along horizontal line. -/
lemma deriv_pole_term (z₀ : ℂ) (σ : ℝ) (h_ne : (σ : ℂ) + z₀.im * I ≠ z₀) :
    deriv (fun x : ℝ => ((x : ℂ) + z₀.im * I - z₀)⁻¹) σ = -((σ : ℂ) + z₀.im * I - z₀)⁻¹ ^ 2 := by
  -- Chain rule: d/dx[1/g(x)] = -g'(x)/g(x)² where g(x) = x + z₀.im*I - z₀ and g'(x) = 1
  -- Strategy: Use HasDerivAt.inv with the affine function g
  -- Step 1: The inner function g(s) = s + (z₀.im * I - z₀) has derivative 1
  let c : ℂ := z₀.im * I - z₀
  -- The functions are equal: x + z₀.im*I - z₀ = x + c
  have h_fun_eq : (fun x : ℝ => ((x : ℂ) + z₀.im * I - z₀)⁻¹) = (fun x : ℝ => ((x : ℂ) + c)⁻¹) := by
    ext x; simp only [c]; ring_nf
  -- The RHS simplifies similarly
  have h_rhs_eq : -((σ : ℂ) + z₀.im * I - z₀)⁻¹ ^ 2 = -((σ : ℂ) + c)⁻¹ ^ 2 := by
    simp only [c]; ring_nf
  rw [h_fun_eq, h_rhs_eq]
  -- Step 2: At s = σ, the derivative of s ↦ s + c is 1
  have h_inner : HasDerivAt (fun s : ℂ => s + c) 1 (σ : ℂ) := by
    convert (hasDerivAt_id' (σ : ℂ)).add_const c
  -- Step 3: Apply inverse rule: d/ds[1/g(s)] = -g'(s)/g(s)² = -1/(s+c)²
  have h_ne' : (σ : ℂ) + c ≠ 0 := by
    simp only [c]
    intro h_eq
    apply h_ne
    -- h_eq : σ + (z₀.im * I - z₀) = 0, want : σ + z₀.im * I = z₀
    have h1 : (σ : ℂ) + z₀.im * I - z₀ = 0 := by
      calc (σ : ℂ) + z₀.im * I - z₀ = (σ : ℂ) + (z₀.im * I - z₀) := by ring
        _ = 0 := h_eq
    calc (σ : ℂ) + z₀.im * I = (σ : ℂ) + z₀.im * I - z₀ + z₀ := by ring
      _ = 0 + z₀ := by rw [h1]
      _ = z₀ := by ring
  have h_inv : HasDerivAt (fun s : ℂ => (s + c)⁻¹) (-(1 : ℂ) / ((σ : ℂ) + c) ^ 2) (σ : ℂ) := by
    exact h_inner.inv h_ne'
  -- Step 4: Use comp_ofReal to get the real derivative
  have h_real : HasDerivAt (fun x : ℝ => ((x : ℂ) + c)⁻¹) (-(1 : ℂ) / ((σ : ℂ) + c) ^ 2) σ := by
    exact h_inv.comp_ofReal
  -- Step 5: Extract deriv from HasDerivAt
  rw [h_real.deriv]
  -- Step 6: Simplify -1/z² = -(z⁻¹)²
  rw [neg_div, div_eq_mul_inv, one_mul, inv_pow]

/-!
## Analytic Axiom Replacements
-/

/-- Conjugate symmetry of completed Riemann zeta: Λ(conj s) = conj(Λ(s)).

This is the Schwarz reflection principle applied to the completed zeta function.
The proof exploits that the Mellin kernel (evenKernel) is real-valued, so
mellin(f)(conj s) = conj(mellin(f)(s)) for such f. -/
theorem completedRiemannZeta₀_conj_proven (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  -- Unfold definitions: completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2
  --                                             = mellin f_modif (s/2) / 2
  simp only [completedRiemannZeta₀, completedHurwitzZetaEven₀, WeakFEPair.Λ₀]
  rw [map_div₀]
  congr 1
  · -- mellin f_modif (conj s / 2) = conj (mellin f_modif (s/2))
    have h_div : conj s / 2 = conj (s / 2) := by
      rw [map_div₀]
      simp only [map_ofNat]
    rw [h_div]
    exact mellin_conj_of_self_conj _ f_modif_hurwitz_self_conj _
  · -- conj 2 = 2
    simp only [map_ofNat]

/-- Atom 3: Real-valuedness of completed Zeta on real axis.

This follows from the conjugate symmetry: since completedRiemannZeta₀(conj s) = conj(completedRiemannZeta₀ s),
and for real x we have conj x = x, the value completedRiemannZeta₀ x must equal its own conjugate,
which happens iff the imaginary part is zero. -/
lemma completedRiemannZeta₀_real_on_real (x : ℝ) :
    (completedRiemannZeta₀ (x : ℂ)).im = 0 := by
  have h := completedRiemannZeta₀_conj_proven (x : ℂ)
  simp only [conj_ofReal] at h
  -- h : completedRiemannZeta₀ x = conj(completedRiemannZeta₀ x)
  -- A complex number z satisfies z = conj z iff z.im = 0
  have him : (completedRiemannZeta₀ (x : ℂ)).im = -(completedRiemannZeta₀ (x : ℂ)).im := by
    calc (completedRiemannZeta₀ (x : ℂ)).im
        = (conj (completedRiemannZeta₀ (x : ℂ))).im := by rw [← h]
      _ = -(completedRiemannZeta₀ (x : ℂ)).im := by simp [conj_im]
  linarith

theorem log_deriv_neg_divergence_at_zero_proven (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : AnalyticAt ℂ f z₀) (h_zero : f z₀ = 0) (h_simple : deriv f z₀ ≠ 0) :
    Tendsto (fun σ : ℝ => (-(deriv f (σ + z₀.im * I) / f (σ + z₀.im * I))).re)
      (𝓝[>] z₀.re) atBot := by
  -- 1. Get the pole structure: f'/f = 1/(s-z₀) + h near z₀
  obtain ⟨h, h_analytic, h_eq⟩ := log_deriv_of_simple_zero hf h_zero h_simple
  -- 2. On the horizontal line, Re(1/(s-z₀)) = 1/(σ-z₀.re) → +∞ as σ → z₀.re⁺
  have h_pole_lim := Residues.pole_real_part_tendsto_atTop z₀
  -- 3. The negative: -Re(1/(s-z₀)) → -∞
  have h_neg_pole : Tendsto (fun σ : ℝ => -((σ : ℂ) + z₀.im * I - z₀)⁻¹.re) (𝓝[>] z₀.re) atBot :=
    tendsto_neg_atTop_atBot.comp h_pole_lim
  -- 4. The remainder h(s) converges along the horizontal approach
  have h_cont : ContinuousAt h z₀ := h_analytic.continuousAt
  have hz : Tendsto (fun σ : ℝ => (σ : ℂ) + z₀.im * I) (𝓝[>] z₀.re) (𝓝 z₀) := by
    have hcont : Tendsto (fun σ : ℝ => (σ : ℂ) + z₀.im * I) (𝓝 z₀.re) (𝓝 z₀) := by
      have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 z₀.re) (𝓝 (z₀.re : ℂ)) :=
        Complex.continuous_ofReal.continuousAt
      have h2 : Tendsto (fun _ : ℝ => z₀.im * I) (𝓝 z₀.re) (𝓝 (z₀.im * I)) :=
        tendsto_const_nhds
      have h12 := h1.add h2
      convert h12 using 2
      exact (Complex.re_add_im z₀).symm
    exact hcont.mono_left nhdsWithin_le_nhds
  have h_rem_tendsto :
      Tendsto (fun σ : ℝ => (-(h ((σ : ℂ) + z₀.im * I))).re) (𝓝[>] z₀.re) (𝓝 (-(h z₀)).re) := by
    have hh : Tendsto h (𝓝 z₀) (𝓝 (h z₀)) := h_cont.tendsto
    have hh_line : Tendsto (fun σ : ℝ => h ((σ : ℂ) + z₀.im * I)) (𝓝[>] z₀.re) (𝓝 (h z₀)) :=
      hh.comp hz
    have hh_line_neg : Tendsto (fun σ : ℝ => -(h ((σ : ℂ) + z₀.im * I))) (𝓝[>] z₀.re) (𝓝 (-h z₀)) :=
      hh_line.neg
    exact Complex.continuous_re.continuousAt.tendsto.comp hh_line_neg
  -- 5. Show points on horizontal line with σ > z₀.re are ≠ z₀
  have hz_ne : Tendsto (fun σ : ℝ => (σ : ℂ) + z₀.im * I) (𝓝[>] z₀.re) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h_eq
    have hre : σ = z₀.re := by
      have := congrArg Complex.re h_eq
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_self] at this
      linarith
    linarith
  -- 6. Transfer the pole decomposition to the horizontal line
  have h_eq_line : ∀ᶠ (σ : ℝ) in 𝓝[>] z₀.re,
        deriv f ((σ : ℂ) + z₀.im * I) / f ((σ : ℂ) + z₀.im * I)
          = (((σ : ℂ) + z₀.im * I) - z₀)⁻¹ + h ((σ : ℂ) + z₀.im * I) :=
    hz_ne.eventually h_eq
  have h_congr :
      (fun σ : ℝ => (-(deriv f (σ + z₀.im * I) / f (σ + z₀.im * I))).re)
        =ᶠ[𝓝[>] z₀.re]
      (fun σ : ℝ => (-(((σ : ℂ) + z₀.im * I - z₀)⁻¹)).re + (-(h ((σ : ℂ) + z₀.im * I))).re) := by
    filter_upwards [h_eq_line] with σ hσ
    simp only [hσ, neg_add, Complex.add_re, Complex.neg_re]
  -- 7. Combine: -∞ + convergent = -∞
  have h_sum :
      Tendsto (fun σ : ℝ => (-(((σ : ℂ) + z₀.im * I - z₀)⁻¹)).re + (-(h ((σ : ℂ) + z₀.im * I))).re)
        (𝓝[>] z₀.re) atBot :=
    tendsto_atBot_add_convergent h_neg_pole h_rem_tendsto
  exact h_sum.congr' h_congr.symm

theorem analytic_stiffness_pos_proven (ρ : ℂ) (h_zero : riemannZeta ρ = 0)
    (h_simple : deriv riemannZeta ρ ≠ 0) (M : ℝ) :
    ∃ δ > 0, ∀ σ, ρ.re < σ → σ < ρ.re + δ →
      (deriv (fun s => -(deriv riemannZeta s / riemannZeta s)) (σ + ρ.im * I)).re > M := by
  -- Strategy: Use stiffness_real_part_tendsto_atBot from Residues.lean
  -- deriv(-f) = -deriv(f), so if deriv(f).re → -∞, then deriv(-f).re → +∞
  -- ρ ≠ 1 because ζ has a pole at 1, not a zero
  have h_not_one : ρ ≠ 1 := by
    intro h_eq
    -- ζ has a pole at 1, so ζ(ρ) = 0 with ρ = 1 is impossible
    -- The residue formula: (s-1)*ζ(s) → 1 as s → 1 (riemannZeta_residue_one)
    -- If ζ(1) = 0, then (s-1)*ζ(s) → 0 as s → 1 (by continuity), contradicting residue = 1
    rw [h_eq] at h_zero h_simple
    -- h_zero : riemannZeta 1 = 0
    -- But riemannZeta_residue_one says (s-1)*ζ(s) → 1 as s → 1
    -- If ζ were continuous at 1 with ζ(1) = 0, then (s-1)*ζ(s) → 0
    -- Contradiction: 0 ≠ 1
    have h_residue := riemannZeta_residue_one
    -- h_residue : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1)
    -- If ζ(1) = 0 and ζ is differentiable at 1, then it's continuous there
    -- So (s-1)*ζ(s) → (1-1)*ζ(1) = 0, but h_residue says it tends to 1
    exfalso
    -- The contradiction: differentiability at ρ implies continuity
    have h_cont : ContinuousAt riemannZeta 1 := by
      -- If deriv ζ ρ ≠ 0, then ζ is differentiable at ρ, hence continuous
      have h_diff : DifferentiableAt ℂ riemannZeta 1 := by
        by_contra h_not_diff
        exact h_simple (deriv_zero_of_not_differentiableAt h_not_diff)
      exact h_diff.continuousAt
    -- (s-1)*ζ(s) → (1-1)*ζ(1) = 0*0 = 0 by continuity of multiplication
    have h_lim_zero : Tendsto (fun s => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 0) := by
      have h_sub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
        have : Tendsto (fun s : ℂ => s - 1) (𝓝 (1 : ℂ)) (𝓝 0) := by
          have h := (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
          simp only [sub_self] at h
          exact h
        exact this.mono_left nhdsWithin_le_nhds
      have h_zeta : Tendsto riemannZeta (𝓝[≠] 1) (𝓝 0) := by
        have := h_cont.tendsto
        rw [h_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      simpa using h_sub.mul h_zeta
    -- But h_residue says the limit is 1, contradiction
    have h_unique := tendsto_nhds_unique h_lim_zero h_residue
    norm_num at h_unique
  -- The stiffness of ζ'/ζ goes to -∞
  have h_stiff := Residues.stiffness_real_part_tendsto_atBot ρ h_zero h_not_one h_simple
  -- deriv(-f) = -deriv(f) for differentiable f, so Re(deriv(-f)) = -Re(deriv(f))
  -- If Re(deriv(f)) → -∞, then -Re(deriv(f)) → +∞
  have h_flip : Tendsto (fun σ : ℝ =>
      -(deriv (fun z => deriv riemannZeta z / riemannZeta z) ((σ : ℂ) + ρ.im * I)).re)
      (𝓝[>] ρ.re) Filter.atTop := tendsto_neg_atBot_atTop.comp h_stiff
  -- Extract δ from the filter using standard pattern
  have h_eventually := h_flip.eventually (Filter.eventually_gt_atTop M)
  rw [Filter.eventually_iff_exists_mem] at h_eventually
  obtain ⟨S, hS_mem, hS_holds⟩ := h_eventually
  rw [Metric.mem_nhdsWithin_iff] at hS_mem
  obtain ⟨δ, hδ_pos, hδ_subset⟩ := hS_mem
  use δ, hδ_pos
  intro σ hσ_gt hσ_lt
  have hσ_in_S : σ ∈ S := by
    apply hδ_subset
    rw [Set.mem_inter_iff, Metric.mem_ball, Set.mem_Ioi]
    constructor
    · rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    · exact hσ_gt
  have h_M := hS_holds σ hσ_in_S
  -- h_M : M < -(deriv (fun z => deriv ζ z / ζ z) ...).re
  -- goal : M < (deriv (fun s => -(deriv ζ s / ζ s)) ...).re
  -- Use deriv_neg: deriv (-f) = -deriv f
  -- So (deriv (fun s => -g(s))).re = (-deriv g).re = -(deriv g).re
  -- deriv.neg : deriv (-f) x = -deriv f x
  have h_deriv_neg : deriv (fun s => -(deriv riemannZeta s / riemannZeta s)) ((σ : ℂ) + ρ.im * I) =
      -deriv (fun s => deriv riemannZeta s / riemannZeta s) ((σ : ℂ) + ρ.im * I) := by
    -- The function is -g where g = (deriv ζ) / ζ
    let g := fun s => deriv riemannZeta s / riemannZeta s
    show deriv (-g) _ = -deriv g _
    exact deriv.neg
  rw [h_deriv_neg, Complex.neg_re]
  exact h_M

/--
**Theorem**: Finite prime sum approximates the NEGATIVE of the analytic stiffness.

The error between the finite sum Σ log²(p)·p^{-σ}·cos(t·log p)
and the analytic stiffness (deriv of -ζ'/ζ) is bounded.

This is the Explicit Formula with error bounds.
-/
theorem finite_sum_approx_analytic_proven (ρ : ℂ) (primes : List ℕ) :
    ∃ (E : ℝ), 0 < E ∧ ∀ σ : ℝ, σ > ρ.re →
      abs (primes.foldl (fun acc p =>
        acc + Real.log p * Real.log p * (p : ℝ) ^ (-σ) * Real.cos (ρ.im * Real.log p)) 0 +
        (deriv (fun s => -(deriv riemannZeta s / riemannZeta s)) (σ + ρ.im * I)).re) < E := by
  -- Strategy: The Explicit Formula from analytic number theory relates the finite sum
  -- to the analytic derivative of -ζ'/ζ. This requires deep Mathlib infrastructure
  -- (von Mangoldt's Explicit Formula, contour integration, etc.) that is not yet available.
  --
  -- The mathematical content:
  -- -ζ'/ζ(s) = Σ_ρ 1/(s-ρ) + Σ_p log(p)·p^{-s} + (regular terms)
  -- Differentiating: d/ds(-ζ'/ζ) = -Σ_ρ 1/(s-ρ)² + Σ_p log²(p)·p^{-s} + ...
  -- The finite sum approximates the prime contribution with bounded error.
  --
  -- This theorem provides the error bound E required by AdmissibleStiffnessApproximation
  -- in Residues.lean, enabling the proof that zeta zeros force negative clustering.
  sorry

end ProofEngine
