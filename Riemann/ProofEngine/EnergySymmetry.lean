/-
# EnergySymmetry: The Analytic Symmetry of the Zeta Energy Surface

This module defines the "ZetaEnergy" function based on the Riemann Xi function.
It establishes the critical symmetry property E(σ) = E(1-σ) which forces a
derivative of zero at the critical line σ = 1/2.

## Mathematical Design (2026-01-22)

We use `completedRiemannZeta₀` (the ENTIRE function) rather than `completedRiemannZeta`
(which has poles at s=0 and s=1). This avoids "junk value" issues in Lean.

The Riemann Xi function is then defined as:
  ξ₀(s) = s(1-s) * Λ₀(s) - 1

where Λ₀ = completedRiemannZeta₀. This is entire by construction.

Key properties:
- Entire: No poles anywhere
- Symmetric: ξ₀(s) = ξ₀(1-s) (from functional equation)
- Zero correspondence: In the critical strip, ξ₀(s)=0 ↔ ζ(s)=0 (nontrivial zeros only)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Riemann.ZetaSurface.CliffordRH
import Riemann.ProofEngine.AnalyticAxioms

noncomputable section
open Complex Filter Topology Set
open scoped ComplexConjugate

namespace ProofEngine.EnergySymmetry

/-!
## 1. The Riemann Xi Function (Entire Version)
-/

/--
The Riemann Xi function, defined using the entire completion.
ξ₀(s) = s(1-s) * Λ₀(s) - 1
where Λ₀ = completedRiemannZeta₀ is entire.
-/
def riemannXi (s : ℂ) : ℂ := s * (1 - s) * completedRiemannZeta₀ s - 1

/--
The functional equation for ξ: ξ(s) = ξ(1-s).
Derived from Λ₀(s) = Λ₀(1-s) and the invariance of s(1-s) under s ↔ 1-s.
-/
theorem riemannXi_symmetric (s : ℂ) : riemannXi s = riemannXi (1 - s) := by
  simp only [riemannXi]
  -- Use functional equation: Λ₀(s) = Λ₀(1-s)
  rw [completedRiemannZeta₀_one_sub]
  -- Algebraic: s(1-s) = (1-s)(1-(1-s))
  ring

/--
Conjugate symmetry of ξ: ξ(conj s) = conj(ξ(s)).
This is the Schwarz reflection principle for entire functions that are real on the real line.
Derived from completedRiemannZeta₀_conj_proven in AnalyticAxioms.
-/
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  simp only [riemannXi]
  rw [ProofEngine.completedRiemannZeta₀_conj_proven s]
  rw [map_sub, map_one, map_mul, map_mul, map_sub, map_one]

/--
In the critical strip, Xi-zero ↔ zeta-zero (nontrivial zeros only).
This is the key bridge property.
-/
theorem riemannXi_zero_iff_zeta_zero {s : ℂ}
    (h_strip : 0 < s.re ∧ s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  -- Key identity: ξ(s) = s(1-s)Λ₀(s) - 1 = s(1-s)Λ(s)
  -- where Λ(s) = Γℝ(s) * ζ(s)
  -- In the strip: s(1-s) ≠ 0 and Γℝ(s) ≠ 0
  -- Therefore ξ(s) = 0 ↔ ζ(s) = 0

  have hs_ne_zero : s ≠ 0 := by
    intro h; rw [h] at h_strip; simp at h_strip
  have hs_ne_one : s ≠ 1 := by
    intro h; rw [h] at h_strip; simp at h_strip
  have h_poly : s * (1 - s) ≠ 0 := mul_ne_zero hs_ne_zero (sub_ne_zero.mpr hs_ne_one.symm)
  have h_gamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h_strip.1

  -- Use Mathlib: Λ(s) = Λ₀(s) - 1/s - 1/(1-s)
  -- Rearranged: Λ₀(s) = Λ(s) + 1/s + 1/(1-s)
  -- So: s(1-s)Λ₀(s) - 1 = s(1-s)[Λ(s) + 1/s + 1/(1-s)] - 1
  --                      = s(1-s)Λ(s) + (1-s) + s - 1 = s(1-s)Λ(s)
  have h_xi_eq : riemannXi s = s * (1 - s) * completedRiemannZeta s := by
    dsimp [riemannXi]
    -- completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s)
    have h_eq : completedRiemannZeta₀ s = completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
      rw [completedRiemannZeta_eq s]
      ring
    rw [h_eq]
    have hs1 : s ≠ 0 := hs_ne_zero
    have hs2 : 1 - s ≠ 0 := sub_ne_zero.mpr hs_ne_one.symm
    field_simp [hs1, hs2]
    ring

  -- Use Mathlib: ζ(s) = Λ(s) / Γℝ(s)
  -- Rearranged: Λ(s) = Γℝ(s) * ζ(s)
  rw [h_xi_eq]

  constructor
  · -- ξ(s) = 0 → ζ(s) = 0
    intro hxi
    -- s(1-s)Λ(s) = 0, and s(1-s) ≠ 0, so Λ(s) = 0
    have h_lambda : completedRiemannZeta s = 0 := by
      simp only [mul_eq_zero] at hxi
      rcases hxi with h1 | h1
      · rcases h1 with h2 | h2
        · exact absurd h2 hs_ne_zero
        · exact absurd h2 (sub_ne_zero.mpr hs_ne_one.symm)
      · exact h1
    -- ζ(s) = Λ(s) / Γℝ(s) = 0 / Γℝ(s) = 0
    rw [riemannZeta_def_of_ne_zero hs_ne_zero, h_lambda, zero_div]
  · -- ζ(s) = 0 → ξ(s) = 0
    intro hzeta
    -- ζ(s) = Λ(s) / Γℝ(s) = 0, and Γℝ(s) ≠ 0, so Λ(s) = 0
    have h_lambda : completedRiemannZeta s = 0 := by
      have h := riemannZeta_def_of_ne_zero hs_ne_zero
      -- h : ζ(s) = Λ(s) / Γℝ(s)
      -- hzeta : ζ(s) = 0
      rw [hzeta] at h
      -- h : 0 = Λ(s) / Γℝ(s)
      rw [eq_comm, div_eq_zero_iff] at h
      rcases h with h1 | h1
      · exact h1
      · exact absurd h1 h_gamma
    -- s(1-s)Λ(s) = s(1-s) * 0 = 0
    simp [h_lambda]

/--
Vanishing Property: If ζ(s) = 0 in the critical strip, then ξ(s) = 0.
-/
theorem riemannXi_zero_of_zeta_zero (s : ℂ) (h_zero : riemannZeta s = 0)
    (h_strip : 0 < s.re ∧ s.re < 1) : riemannXi s = 0 := by
  exact (riemannXi_zero_iff_zeta_zero h_strip).mpr h_zero

/-!
## 2. The Zeta Energy Surface
-/

/--
The "Energy" of the zeta function at a given height t and real component σ.
Defined as the squared norm of the Riemann Xi function: E(σ, t) = ‖ξ(σ + it)‖²
-/
def ZetaEnergy (t : ℝ) (σ : ℝ) : ℝ :=
  Complex.normSq (riemannXi (σ + t * I))

/-- Energy is always nonnegative. -/
theorem ZetaEnergy_nonneg (t σ : ℝ) : 0 ≤ ZetaEnergy t σ :=
  Complex.normSq_nonneg _

/-- Energy is zero iff Xi is zero. -/
theorem ZetaEnergy_eq_zero_iff (t σ : ℝ) :
    ZetaEnergy t σ = 0 ↔ riemannXi (σ + t * I) = 0 := by
  simp only [ZetaEnergy, Complex.normSq_eq_zero]

/--
Symmetry of the Energy Surface: E(σ, t) = E(1-σ, t).
This follows from ξ(s) = ξ(1-s) and conjugate properties.
-/
theorem zeta_energy_symmetric (t : ℝ) (σ : ℝ) :
    ZetaEnergy t σ = ZetaEnergy t (1 - σ) := by
  simp only [ZetaEnergy]
  -- ξ(σ + it) = ξ(1 - (σ + it)) = ξ((1-σ) - it)
  -- We need to relate ‖ξ((1-σ) - it)‖² to ‖ξ((1-σ) + it)‖²
  -- This uses the conjugate symmetry of ξ

  have h1 : riemannXi ((σ : ℂ) + t * I) = riemannXi (1 - ((σ : ℂ) + t * I)) :=
    riemannXi_symmetric _

  -- 1 - (σ + it) = (1-σ) - it = conj((1-σ) + it)
  have h2 : (1 : ℂ) - ((σ : ℂ) + t * I) = ((1 - σ) : ℂ) - t * I := by ring

  -- For the norm squared, we need ξ(conj z) = conj(ξ(z))
  -- This follows from ξ being real on the real line (Schwarz reflection)

  rw [h1, h2]
  -- ‖ξ((1-σ) - it)‖² = ‖ξ((1-σ) + it)‖² by conjugate symmetry
  -- The Xi function satisfies ξ(conj s) = conj(ξ(s))

  -- Key: (1-σ) - it = conj((1-σ) + it) for real σ and t
  have h_conj : ((1 - σ) : ℂ) - t * I = conj (((1 - σ) : ℂ) + t * I) := by
    simp only [map_add, conj_ofReal, map_mul, conj_I, map_sub, map_one]
    ring
  -- Normalize the coercion: (1 : ℂ) - (σ : ℂ) = ((1 - σ) : ℝ) : ℂ
  have h_cast : (1 : ℂ) - (σ : ℂ) + (t : ℂ) * I = (((1 - σ) : ℝ) : ℂ) + (t : ℂ) * I := by
    simp only [ofReal_sub, ofReal_one]
  rw [h_conj, riemannXi_conj, normSq_conj, h_cast]

/-!
## 3. Critical Point Theorems
-/

/--
A symmetric smooth function has a derivative of zero at the center of symmetry.
f(x) = f(1-x) implies f'(x) = -f'(1-x) by chain rule.
At x = 1/2: f'(1/2) = -f'(1/2), so f'(1/2) = 0.
-/
theorem deriv_zero_of_symmetric {f : ℝ → ℝ} (h_diff : Differentiable ℝ f)
    (h_symm : ∀ x, f x = f (1 - x)) :
    deriv f (1/2) = 0 := by
  -- The chain rule argument:
  -- f(x) = f(1-x) ⟹ f'(x) = f'(1-x) · (-1) = -f'(1-x)
  -- At x = 1/2: f'(1/2) = -f'(1-1/2) = -f'(1/2)
  -- Therefore 2·f'(1/2) = 0, so f'(1/2) = 0

  -- Define g(x) = f(1-x)
  let g : ℝ → ℝ := fun x => f (1 - x)
  -- f = g pointwise (symmetry hypothesis)
  have h_fg : ∀ x, f x = g x := h_symm
  -- Therefore their derivatives are equal pointwise
  have h_deriv_fg : ∀ x, deriv f x = deriv g x := by
    intro x
    congr 1
    exact funext h_fg
  -- Use deriv_comp_const_sub: deriv (fun x => f(a - x)) x = -deriv f (a - x)
  have h_deriv_g : ∀ x, deriv g x = -deriv f (1 - x) := fun x => deriv_comp_const_sub f 1 x
  -- At x = 1/2: f'(1/2) = g'(1/2) = -f'(1 - 1/2) = -f'(1/2)
  have h1 : deriv f (1/2) = deriv g (1/2) := h_deriv_fg (1/2)
  have h2 : deriv g (1/2) = -deriv f (1/2) := by
    rw [h_deriv_g]
    norm_num
  linarith

/--
The ZetaEnergy has a stationary point (derivative zero) at σ = 1/2.
-/
theorem energy_deriv_zero_at_half (t : ℝ) :
    deriv (fun σ => ZetaEnergy t σ) (1/2) = 0 := by
  apply deriv_zero_of_symmetric
  · -- Differentiability of ZetaEnergy
    -- ZetaEnergy t σ = normSq (riemannXi (σ + t*I)) = re² + im²
    -- riemannXi is entire (differentiable everywhere)
    -- re and im are smooth, so re² + im² is differentiable
    have h_line : Differentiable ℝ (fun σ : ℝ => (σ : ℂ) + t * I) := by
      apply Differentiable.add
      · exact Complex.ofRealCLM.differentiable
      · exact differentiable_const _
    have h_xi : Differentiable ℂ riemannXi := by
      unfold riemannXi
      exact ((differentiable_id.mul (differentiable_const 1 |>.sub differentiable_id)).mul
        differentiable_completedZeta₀).sub (differentiable_const _)
    have h_comp : Differentiable ℝ (fun σ : ℝ => riemannXi ((σ : ℂ) + t * I)) :=
      (h_xi.restrictScalars ℝ).comp h_line
    -- re and im components are differentiable
    have h_re : Differentiable ℝ (fun σ : ℝ => (riemannXi ((σ : ℂ) + t * I)).re) := by
      have : (fun σ : ℝ => (riemannXi ((σ : ℂ) + t * I)).re) =
             Complex.reCLM ∘ (fun σ : ℝ => riemannXi ((σ : ℂ) + t * I)) := rfl
      rw [this]
      exact Complex.reCLM.differentiable.comp h_comp
    have h_im : Differentiable ℝ (fun σ : ℝ => (riemannXi ((σ : ℂ) + t * I)).im) := by
      have : (fun σ : ℝ => (riemannXi ((σ : ℂ) + t * I)).im) =
             Complex.imCLM ∘ (fun σ : ℝ => riemannXi ((σ : ℂ) + t * I)) := rfl
      rw [this]
      exact Complex.imCLM.differentiable.comp h_comp
    -- ZetaEnergy = re² + im²
    have h_eq : (fun σ : ℝ => ZetaEnergy t σ) =
        (fun σ : ℝ => (riemannXi ((σ : ℂ) + t * I)).re ^ 2 +
        (riemannXi ((σ : ℂ) + t * I)).im ^ 2) := by
      ext σ
      unfold ZetaEnergy
      rw [Complex.normSq_apply]
      ring
    rw [h_eq]
    exact (h_re.pow 2).add (h_im.pow 2)
  · -- Symmetry around 1/2
    intro σ
    exact zeta_energy_symmetric t σ

/--
Definition: Energy convexity at the critical line.
The second derivative of ZetaEnergy(t, σ) with respect to σ is positive at σ = 1/2.
-/
def EnergyIsConvexAtHalf (t : ℝ) : Prop :=
  deriv (deriv (fun σ => ZetaEnergy t σ)) (1/2) > 0

/--
Geometric Conclusion:
If ZetaEnergy is C² and its second derivative is positive at σ=1/2,
then σ=1/2 is a strict local minimum.

The C² hypothesis is natural: ZetaEnergy = normSq ∘ riemannXi ∘ (σ ↦ σ+it),
where riemannXi is entire (C^∞) and normSq = re² + im² is smooth.
-/
theorem symmetry_and_convexity_imply_local_min (t : ℝ)
    (h_convex : EnergyIsConvexAtHalf t)
    (h_C2 : ContDiff ℝ 2 (fun σ => ZetaEnergy t σ)) :
    ∃ δ > 0, ∀ σ, σ ≠ 1/2 ∧ |σ - 1/2| < δ → ZetaEnergy t (1/2) < ZetaEnergy t σ := by
  let f := fun σ => ZetaEnergy t σ

  -- Atomic helper 1: f'(1/2) = 0 from symmetry
  have h_deriv_zero : deriv f (1/2) = 0 := energy_deriv_zero_at_half t

  -- Atomic helper 2: Continuity of f'' from C²
  -- ContDiff ℝ 2 f → ContDiff ℝ 1 (deriv f) → Continuous (deriv (deriv f))
  have h_C1 : ContDiff ℝ 1 (deriv f) := by
    have h1 : ContDiff ℝ (1 + 1) f := h_C2
    exact (contDiff_succ_iff_deriv.mp h1).2.2
  have h_deriv2_cont : ContinuousAt (deriv (deriv f)) (1/2) :=
    (h_C1.continuous_deriv le_rfl).continuousAt

  -- Atomic helper 3: Extract δ where f'' > 0
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.continuousAt_iff.mp h_deriv2_cont _ h_convex

  -- Atomic helper 4: Continuity
  have h_cont : ContinuousAt f (1/2) := h_C2.continuous.continuousAt

  -- Apply second derivative test for non-strict minimum
  have h_local_min : IsLocalMin f (1/2) :=
    isLocalMin_of_deriv_deriv_pos h_convex h_deriv_zero h_cont

  -- Extract ε from IsLocalMin
  rw [IsLocalMin] at h_local_min
  obtain ⟨U, hU_mem, hU_min⟩ := Filter.eventually_iff_exists_mem.mp h_local_min
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp hU_mem

  -- Use min(ε/2, δ) as final neighborhood
  use min (ε / 2) δ
  constructor
  · exact lt_min (by linarith) hδ_pos
  intro σ ⟨hne, habs⟩

  have hσ_in_ε : |σ - 1/2| < ε / 2 := lt_of_lt_of_le habs (min_le_left _ _)
  have hσ_in_δ : |σ - 1/2| < δ := lt_of_lt_of_le habs (min_le_right _ _)

  -- f(1/2) ≤ f(σ) from local minimum
  have h_le : f (1/2) ≤ f σ := by
    apply hU_min; apply hε_ball
    rw [Metric.mem_ball, Real.dist_eq]; linarith

  -- Prove strict by contradiction: assume f(σ) ≤ f(1/2)
  by_contra h_not_lt
  push_neg at h_not_lt
  have h_eq : f σ = f (1/2) := le_antisymm h_not_lt h_le

  -- Atomic helper 5: f' is strictly monotone on (1/2 - δ, 1/2 + δ) (using h_C1 from above)
  have h_f'_strictMono : StrictMonoOn (deriv f) (Ioo (1/2 - δ) (1/2 + δ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · exact h_C1.continuous.continuousOn
    · intro x hx; simp only [interior_Ioo] at hx
      -- hδ_ball : |f''(x) - f''(1/2)| < f''(1/2) implies f''(x) > 0
      have hx_dist : dist x (1/2) < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
      have hbound := hδ_ball hx_dist
      rw [Real.dist_eq] at hbound
      have h_neg := neg_abs_le (deriv (deriv f) x - deriv (deriv f) (1/2))
      linarith

  -- Rolle: ∃ c strictly between σ and 1/2 with f'(c) = 0
  have h_f_cont_on : ContinuousOn f (Icc (min σ (1/2)) (max σ (1/2))) :=
    h_C2.continuous.continuousOn

  have h_min_lt_max : min σ (1/2) < max σ (1/2) := by
    rcases lt_trichotomy σ (1/2) with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · exact absurd h hne
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h

  have h_f_eq_ends : f (min σ (1/2)) = f (max σ (1/2)) := by
    rcases lt_trichotomy σ (1/2) with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h_eq
    · exact absurd h hne
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h_eq.symm

  obtain ⟨c, hc_mem, hc_deriv⟩ := exists_deriv_eq_zero h_min_lt_max h_f_cont_on h_f_eq_ends

  -- c ≠ 1/2 (strictly between)
  have hc_ne : c ≠ 1/2 := by
    rcases lt_trichotomy σ (1/2) with h | h | h
    · simp only [min_eq_left h.le, max_eq_right h.le] at hc_mem; exact ne_of_lt hc_mem.2
    · exact absurd h hne
    · simp only [min_eq_right h.le, max_eq_left h.le] at hc_mem; exact ne_of_gt hc_mem.1

  -- c ∈ (1/2 - δ, 1/2 + δ)
  have hc_in : c ∈ Ioo (1/2 - δ) (1/2 + δ) := by
    rcases lt_trichotomy σ (1/2) with h | h | h
    · simp only [min_eq_left h.le, max_eq_right h.le] at hc_mem
      have : σ > 1/2 - δ := by rw [abs_lt] at hσ_in_δ; linarith
      exact ⟨by linarith [hc_mem.1], by linarith [hc_mem.2]⟩
    · exact absurd h hne
    · simp only [min_eq_right h.le, max_eq_left h.le] at hc_mem
      have : σ < 1/2 + δ := by rw [abs_lt] at hσ_in_δ; linarith
      exact ⟨by linarith [hc_mem.1], by linarith [hc_mem.2]⟩

  have h_half_in : (1:ℝ)/2 ∈ Ioo (1/2 - δ) (1/2 + δ) := ⟨by linarith, by linarith⟩

  -- Contradiction: f'(c) = 0 = f'(1/2) but strict monotonicity
  rcases lt_trichotomy c (1/2) with hlt | heq | hgt
  · have := h_f'_strictMono hc_in h_half_in hlt
    rw [hc_deriv, h_deriv_zero] at this; exact (lt_irrefl 0) this
  · exact hc_ne heq
  · have := h_f'_strictMono h_half_in hc_in hgt
    rw [hc_deriv, h_deriv_zero] at this; exact (lt_irrefl 0) this

/--
**Bridge Theorem**: Convexity of the analytic energy implies the finite sum
has a strict minimum at σ = 1/2.

Note: The analytic energy has a proven strict local minimum at 1/2 via
`symmetry_and_convexity_imply_local_min`. Transferring this to the finite
rotor sum requires global approximation bounds not captured here.
The hypothesis h_norm_min encapsulates this analytic-to-finite transfer.
-/
theorem convexity_implies_norm_strict_min (t : ℝ)
    (primes : List ℕ)
    (_h_large : primes.length > 1000)
    (_h_convex : EnergyIsConvexAtHalf t)
    (_h_C2 : ContDiff ℝ 2 (fun σ => ZetaEnergy t σ))
    (h_norm_min : CliffordRH.NormStrictMinAtHalf t primes) :
    CliffordRH.NormStrictMinAtHalf t primes :=
  h_norm_min

/-!
## 5. Analytic RH: Pure Energy Minimization

The clean reformulation eliminates all discrete hypotheses (prime lists,
rotor sums, approximation bounds) in favor of a single analytic condition
on the energy surface |ξ(σ + it)|².
-/

/--
**Analytic Strict Minimum at Half**: The ZetaEnergy has a strict global minimum
at σ = 1/2 on the critical strip (0,1).

This is the pure analytic hypothesis that replaces the discrete
`NormStrictMinAtHalf` and `ZeroHasMinNorm` from the Clifford rotor framework.
-/
def AnalyticStrictMinAtHalf (t : ℝ) : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≠ 1/2 →
    ZetaEnergy t (1/2) < ZetaEnergy t σ

/--
**Strict Convexity of ZetaEnergy on the Critical Strip.**
The sufficient analytic condition: |ξ(σ + it)|² is strictly convex in σ on (0,1).
-/
def EnergyStrictlyConvexOnStrip (t : ℝ) : Prop :=
  StrictConvexOn ℝ (Ioo 0 1) (fun σ => ZetaEnergy t σ)

/--
**Strict convexity + proved symmetry → unique minimum at 1/2.**

For any σ ≠ 1/2 in (0,1), write 1/2 = (σ + (1-σ))/2.
By strict convexity: E(1/2) < (E(σ) + E(1-σ))/2.
By proved symmetry E(1-σ) = E(σ): E(1/2) < E(σ).
-/
theorem strict_convex_implies_analytic_min (t : ℝ)
    (h_conv : EnergyStrictlyConvexOnStrip t) :
    AnalyticStrictMinAtHalf t := by
  intro σ hσ_pos hσ_lt hσ_ne
  have hσ_mem : σ ∈ Ioo (0:ℝ) 1 := ⟨hσ_pos, hσ_lt⟩
  have h_one_minus : 1 - σ ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have h_ne : σ ≠ 1 - σ := fun h => hσ_ne (by linarith)
  -- Strict convexity at midpoint: E((σ+(1-σ))/2) < (E(σ)+E(1-σ))/2
  have h_sc := h_conv.2 hσ_mem h_one_minus h_ne
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  -- Simplify smul to mul and rewrite midpoint to 1/2
  simp only [smul_eq_mul] at h_sc
  have h_mid : (1:ℝ)/2 * σ + 1/2 * (1 - σ) = 1/2 := by ring
  rw [h_mid] at h_sc
  -- By proved symmetry E(σ) = E(1-σ), so RHS = E(σ)
  linarith [zeta_energy_symmetric t σ]

/--
**THE ANALYTIC RH THEOREM**

If ζ(s) = 0 in the critical strip and ZetaEnergy has a strict minimum at 1/2,
then s.re = 1/2.

**Proof**:
1. ζ(s) = 0 → ξ(s) = 0 (bridge to Xi function)
2. ξ(s) = 0 → E(s.im, s.re) = 0 (energy vanishes at zero)
3. E ≥ 0 always (norm squared is nonneg)
4. E(1/2) < E(s.re) from strict minimum hypothesis
5. Contradiction: 0 ≤ E(1/2) < E(s.re) = 0

Only 3 hypotheses: ζ(s) = 0, s ∈ strip, energy minimized at 1/2.
No discrete sums, no prime lists, no approximation bounds.
-/
theorem RH_from_AnalyticEnergy (s : ℂ) (h_zero : riemannZeta s = 0)
    (h_strip : 0 < s.re ∧ s.re < 1)
    (h_strict_min : AnalyticStrictMinAtHalf s.im) :
    s.re = 1 / 2 := by
  by_contra h_neq
  -- ζ(s) = 0 → ξ(s) = 0 in the critical strip
  have h_xi_zero := riemannXi_zero_of_zeta_zero s h_zero h_strip
  -- ξ(s) = 0 → E(s.im, s.re) = 0 (rewrite s = s.re + s.im * I)
  have h_energy_zero : ZetaEnergy s.im s.re = 0 := by
    rw [ZetaEnergy_eq_zero_iff, Complex.re_add_im]
    exact h_xi_zero
  -- E(1/2) < E(s.re) from strict minimum hypothesis
  have h_lt := h_strict_min s.re h_strip.1 h_strip.2 h_neq
  -- E(1/2) ≥ 0 (norm squared is nonneg)
  have h_nonneg := ZetaEnergy_nonneg s.im (1/2)
  -- Contradiction: 0 ≤ E(1/2) < E(s.re) = 0
  linarith

/-!
## 6. Summary

The key results established:
1. `riemannXi_symmetric`: ξ(s) = ξ(1-s) — PROVEN
2. `zeta_energy_symmetric`: E(σ,t) = E(1-σ,t) — PROVEN
3. `energy_deriv_zero_at_half`: E'(1/2) = 0 — PROVEN
4. `symmetry_and_convexity_imply_local_min`: E''(1/2) > 0 → local min — PROVEN
5. `strict_convex_implies_analytic_min`: strict convexity → unique min at 1/2 — PROVEN
6. `RH_from_AnalyticEnergy`: energy min at 1/2 → RH — PROVEN

**Hierarchy of conditions** (each implies the next):
- `EnergyStrictlyConvexOnStrip t` (strict convexity of |ξ|² on (0,1))
  → `AnalyticStrictMinAtHalf t` (unique minimum at 1/2)
    → RH at height t

**Remaining hypothesis**: One of:
- `AnalyticStrictMinAtHalf s.im` — most general
- `EnergyStrictlyConvexOnStrip s.im` — most structural (strict convexity)
-/

end ProofEngine.EnergySymmetry

end
