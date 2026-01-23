import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

noncomputable section
open Real Filter Topology Set

namespace ProofEngine

/-!
## Calculus Helper Lemmas (Atomic Units)
-/

/-- Atom 1: Taylor's theorem with remainder for second derivative. -/
lemma taylor_second_order {f : ℝ → ℝ} {x₀ x : ℝ} (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) :
    ∃ c ∈ Icc (min x₀ x) (max x₀ x), f x = f x₀ + (deriv f x₀) * (x - x₀) + (deriv (deriv f) c) * (x - x₀)^2 / 2 := by
  -- Case split: x = x₀, x₀ < x, or x < x₀
  rcases lt_trichotomy x₀ x with hlt | heq | hgt
  · -- Case: x₀ < x, use taylor_mean_remainder_lagrange directly
    -- Need: ContDiffOn ℝ 1 f (Icc x₀ x) and DifferentiableOn for iteratedDerivWithin 1
    have hf_on : ContDiffOn ℝ 1 f (Icc x₀ x) := by
      have : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr ⟨hf, hf'.continuous⟩
      exact this.contDiffOn
    have hf'_on : DifferentiableOn ℝ (iteratedDerivWithin 1 f (Icc x₀ x)) (Ioo x₀ x) := by
      -- iteratedDerivWithin 1 f s = derivWithin f s, and for globally diff f, this equals deriv f
      have hu : UniqueDiffOn ℝ (Icc x₀ x) := uniqueDiffOn_Icc hlt
      have : ∀ y ∈ Icc x₀ x, iteratedDerivWithin 1 f (Icc x₀ x) y = deriv f y := by
        intro y hy
        rw [iteratedDerivWithin_one, (hf y).derivWithin (hu y hy)]
      -- Now DifferentiableOn follows from hf' being Differentiable
      exact (hf'.differentiableOn.mono (Ioo_subset_Icc_self)).congr (fun y hy => this y (Ioo_subset_Icc_self hy))
    obtain ⟨c, hc_mem, hc_eq⟩ := taylor_mean_remainder_lagrange hlt hf_on hf'_on
    use c
    constructor
    · simp only [min_eq_left hlt.le, max_eq_right hlt.le]
      exact ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩
    · -- Simplify Taylor polynomial and remainder
      rw [taylor_within_apply] at hc_eq
      -- Simplify the sum to: f x₀ + (x - x₀) * iteratedDerivWithin 1 f (Icc x₀ x) x₀
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
                 Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul,
                 Nat.factorial_one, pow_one, smul_eq_mul, iteratedDerivWithin_zero,
                 show One.one = (1 : ℕ) from rfl] at hc_eq
      have h1 : iteratedDerivWithin 1 f (Icc x₀ x) x₀ = deriv f x₀ := by
        rw [iteratedDerivWithin_one]
        exact (hf x₀).derivWithin (uniqueDiffOn_Icc hlt x₀ (left_mem_Icc.mpr hlt.le))
      simp only [h1] at hc_eq
      -- iteratedDerivWithin 2 at c = deriv (deriv f) c (using unique diff)
      have h2 : iteratedDerivWithin 2 f (Icc x₀ x) c = deriv (deriv f) c := by
        have hc_in : c ∈ Icc x₀ x := ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩
        have hu : UniqueDiffOn ℝ (Icc x₀ x) := uniqueDiffOn_Icc hlt
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
        -- Goal: derivWithin (derivWithin f s) s c = deriv (deriv f) c
        -- First: derivWithin f s c = deriv f c (since f is globally diff)
        have h_inner : derivWithin f (Icc x₀ x) c = deriv f c := (hf c).derivWithin (hu c hc_in)
        -- Need: derivWithin (derivWithin f s) s c = derivWithin (deriv f) s c
        have h_func_eq : EqOn (derivWithin f (Icc x₀ x)) (deriv f) (Icc x₀ x) :=
          fun y hy => (hf y).derivWithin (hu y hy)
        rw [derivWithin_congr h_func_eq h_inner, (hf' c).derivWithin (hu c hc_in)]
      rw [h2] at hc_eq
      simp only [Nat.factorial] at hc_eq
      linarith
  · -- Case: x = x₀, trivial
    use x₀
    simp only [heq, min_self, max_self, left_mem_Icc, le_refl, and_self, sub_self,
               mul_zero, pow_two, add_zero, true_and, zero_div]
  · -- Case: x < x₀, use reflection g(t) = f(x₀ + x - t)
    let g : ℝ → ℝ := fun t => f (x₀ + x - t)
    have hg : Differentiable ℝ g := hf.comp ((differentiable_const (x₀ + x)).sub differentiable_id)
    have hg' : Differentiable ℝ (deriv g) := by
      have : deriv g = fun t => -deriv f (x₀ + x - t) := by
        ext t
        simp only [g]
        rw [deriv_comp_const_sub]
      rw [this]
      exact (hf'.comp ((differentiable_const (x₀ + x)).sub differentiable_id)).neg
    have hg_on : ContDiffOn ℝ 1 g (Icc x x₀) := by
      have : ContDiff ℝ 1 g := contDiff_one_iff_deriv.mpr ⟨hg, hg'.continuous⟩
      exact this.contDiffOn
    have hg'_on : DifferentiableOn ℝ (iteratedDerivWithin 1 g (Icc x x₀)) (Ioo x x₀) := by
      have hu : UniqueDiffOn ℝ (Icc x x₀) := uniqueDiffOn_Icc hgt
      have key : ∀ y ∈ Icc x x₀, iteratedDerivWithin 1 g (Icc x x₀) y = deriv g y := by
        intro y hy
        rw [iteratedDerivWithin_one, (hg y).derivWithin (hu y hy)]
      exact (hg'.differentiableOn.mono (Ioo_subset_Icc_self)).congr (fun y hy => key y (Ioo_subset_Icc_self hy))
    obtain ⟨c, hc_mem, hc_eq⟩ := taylor_mean_remainder_lagrange hgt hg_on hg'_on
    -- c ∈ Ioo x x₀, so c' = x₀ + x - c ∈ Ioo x x₀
    set c' := x₀ + x - c with hc'_def
    use c'
    constructor
    · simp only [min_eq_right hgt.le, max_eq_left hgt.le]
      exact ⟨by linarith [hc_mem.2], by linarith [hc_mem.1]⟩
    · -- g(x) = f(x₀), g(x₀) = f(x), g'(x) = -f'(x₀)
      have hg_x : g x = f x₀ := by simp only [g, add_sub_cancel_right]
      have hg_x0 : g x₀ = f x := by simp only [g, add_sub_cancel_left]
      have hg_deriv_x : deriv g x = -deriv f x₀ := by
        simp only [g]
        rw [deriv_comp_const_sub]
        simp
      -- Expand Taylor for g at x evaluated at x₀
      rw [taylor_within_apply] at hc_eq
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
                 Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul,
                 Nat.factorial_one, pow_one, smul_eq_mul, iteratedDerivWithin_zero,
                 show One.one = (1 : ℕ) from rfl] at hc_eq
      have h1 : iteratedDerivWithin 1 g (Icc x x₀) x = deriv g x := by
        rw [iteratedDerivWithin_one]
        exact (hg x).derivWithin (uniqueDiffOn_Icc hgt x (left_mem_Icc.mpr hgt.le))
      simp only [h1, hg_x, hg_x0, hg_deriv_x] at hc_eq
      -- iteratedDerivWithin 2 g c = deriv (deriv g) c = deriv (deriv f) c'
      have h2 : iteratedDerivWithin 2 g (Icc x x₀) c = deriv (deriv f) c' := by
        have hc_in : c ∈ Icc x x₀ := ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩
        have hu : UniqueDiffOn ℝ (Icc x x₀) := uniqueDiffOn_Icc hgt
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
        -- Goal: derivWithin (derivWithin g s) s c = deriv (deriv f) c'
        have h_inner : derivWithin g (Icc x x₀) c = deriv g c := (hg c).derivWithin (hu c hc_in)
        have h_func_eq : EqOn (derivWithin g (Icc x x₀)) (deriv g) (Icc x x₀) :=
          fun y hy => (hg y).derivWithin (hu y hy)
        rw [derivWithin_congr h_func_eq h_inner, (hg' c).derivWithin (hu c hc_in)]
        -- deriv (deriv g) c = deriv (deriv f) c'
        have hderiv_g : deriv g = fun t => -deriv f (x₀ + x - t) := by
          ext t; simp only [g]; rw [deriv_comp_const_sub]
        rw [hderiv_g]
        -- deriv (fun t => -deriv f (x₀ + x - t)) c = deriv (deriv f) c'
        have h1 : deriv (fun t => -deriv f (x₀ + x - t)) c = -deriv (fun t => deriv f (x₀ + x - t)) c := by
          exact deriv.neg
        rw [h1, deriv_comp_const_sub]
        simp only [neg_neg, hc'_def]
      rw [h2] at hc_eq
      simp only [Nat.factorial] at hc_eq
      -- hc_eq: f x - (f x₀ + (-deriv f x₀) * (x₀ - x)) = deriv (deriv f) c' * (x₀ - x)^2 / 2
      have hsq : (x₀ - x)^2 = (x - x₀)^2 := by ring
      linarith [hsq]

/-- 
Replacement for `ax_effective_critical_convex_implies_near_min`.
Effective convexity at the critical line forces a strict trace minimum.
-/
-- Helper: ε < (δ/2)|σ - 1/2| implies quadratic dominates linear term
private lemma quadratic_dominates_linear
    (σ δ ε : ℝ) (h_ne : σ ≠ 1 / 2) (hδ : 0 < δ)
    (hε_small : ε < δ * |σ - 1 / 2| / 2) :
    (δ / 2) * (σ - 1 / 2)^2 - ε * |σ - 1 / 2| > 0 := by
  have h_abs_pos : |σ - 1 / 2| > 0 := abs_pos.mpr (sub_ne_zero.mpr h_ne)
  have h_bound : (δ / 2) * |σ - 1 / 2| > ε := by linarith
  have h_sq_eq : (σ - 1 / 2)^2 = |σ - 1 / 2| * |σ - 1 / 2| := by
    rw [sq, ← abs_mul_abs_self]
  calc (δ / 2) * (σ - 1 / 2)^2 - ε * |σ - 1 / 2|
      = (δ / 2) * (|σ - 1 / 2| * |σ - 1 / 2|) - ε * |σ - 1 / 2| := by rw [h_sq_eq]
    _ = ((δ / 2) * |σ - 1 / 2| - ε) * |σ - 1 / 2| := by ring
    _ > 0 := mul_pos (by linarith) h_abs_pos

-- Helper: Lower bound using positive second derivative
private lemma second_deriv_lower_bound
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (f'' : ℝ → ℝ)
    (a b δ : ℝ) (hab : a < b)
    (hf_diff : ∀ ξ ∈ Icc a b, HasDerivAt f (f' ξ) ξ)
    (hf'_diff : ∀ ξ ∈ Icc a b, HasDerivAt f' (f'' ξ) ξ)
    (h_f''_pos : ∀ ξ ∈ Icc a b, f'' ξ ≥ δ) (hδ : 0 < δ) :
    f b - f a ≥ f' a * (b - a) + (δ / 2) * (b - a)^2 := by
  -- Step 1: From HasDerivAt, get continuity and integrability
  have hf_cont : ContinuousOn f (Icc a b) :=
    fun x hx => (hf_diff x hx).continuousAt.continuousWithinAt
  have hf'_cont : ContinuousOn f' (Icc a b) :=
    fun x hx => (hf'_diff x hx).continuousAt.continuousWithinAt
  -- Note: f'' continuity not directly needed for this proof

  -- Interval integrability from continuity
  have hf'_int : IntervalIntegrable f' MeasureTheory.volume a b :=
    hf'_cont.intervalIntegrable_of_Icc hab.le

  -- Step 2: FTC for f: f(b) - f(a) = ∫_a^b f'(x) dx
  have h_uIcc_eq : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hf_diff_uIcc : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x := by
    intro x hx
    rw [h_uIcc_eq] at hx
    exact hf_diff x hx

  have h_ftc : ∫ x in a..b, f' x = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf_diff_uIcc hf'_int

  -- Step 3: Lower bound on f' using MVT: f'(x) ≥ f'(a) + δ(x - a)
  have h_f'_lower : ∀ x ∈ Icc a b, f' x ≥ f' a + δ * (x - a) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · simp  -- x = a case
    · -- x > a: Use MVT on f' over [a, x]
      have h_f'_cont_ax : ContinuousOn f' (Icc a x) :=
        hf'_cont.mono (Icc_subset_Icc le_rfl hx.2)
      have hf'_diff_ax : ∀ ξ ∈ Ioo a x, HasDerivAt f' (f'' ξ) ξ := by
        intro ξ hξ
        have hξ_mem : ξ ∈ Icc a b := ⟨hξ.1.le, hξ.2.le.trans hx.2⟩
        exact hf'_diff ξ hξ_mem
      -- Apply MVT: ∃ c ∈ (a, x), f'(x) - f'(a) = f''(c) * (x - a)
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f' f'' hax h_f'_cont_ax hf'_diff_ax
      have h_c_in_ab : c ∈ Icc a b := ⟨hc_mem.1.le, hc_mem.2.le.trans hx.2⟩
      have h_f''_c : f'' c ≥ δ := h_f''_pos c h_c_in_ab
      have h_pos : x - a > 0 := sub_pos.mpr hax
      have h_rewrite : f'' c * (x - a) = f' x - f' a := by
        have hne : x - a ≠ 0 := ne_of_gt h_pos
        field_simp [hne] at hc_eq ⊢
        linarith
      calc f' x = f' a + (f' x - f' a) := by ring
        _ = f' a + f'' c * (x - a) := by rw [← h_rewrite]
        _ ≥ f' a + δ * (x - a) := by
             have h1 : δ * (x - a) ≤ f'' c * (x - a) :=
               mul_le_mul_of_nonneg_right h_f''_c h_pos.le
             linarith

  -- Step 4: Integrate the lower bound
  have h_lower_int : IntervalIntegrable (fun x => f' a + δ * (x - a)) MeasureTheory.volume a b := by
    apply IntervalIntegrable.add
    · exact intervalIntegrable_const
    · apply IntervalIntegrable.const_mul
      exact (continuous_id.sub continuous_const).intervalIntegrable a b

  have h_integral_lower : ∫ x in a..b, (f' a + δ * (x - a)) = f' a * (b - a) + (δ / 2) * (b - a)^2 := by
    -- Split integral of sum
    have h_split : ∫ x in a..b, (f' a + δ * (x - a)) =
        (∫ x in a..b, f' a) + ∫ x in a..b, δ * (x - a) := by
      apply intervalIntegral.integral_add intervalIntegrable_const
      apply IntervalIntegrable.const_mul
      exact (continuous_id.sub continuous_const).intervalIntegrable a b
    rw [h_split]
    rw [intervalIntegral.integral_const]
    rw [intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    -- ∫_a^b (x - a) dx = (b - a)² / 2
    -- Use FTC: antiderivative of (x - a) is (x - a)² / 2
    have h_integral_linear : ∫ x in a..b, (x - a) = (b - a)^2 / 2 := by
      -- Define F(x) = (x - a)² / 2, then F'(x) = x - a
      let F : ℝ → ℝ := fun x => (x - a)^2 / 2
      have hF_deriv : ∀ x, HasDerivAt F (x - a) x := by
        intro x
        have h1 : HasDerivAt (fun y => y - a) 1 x := hasDerivAt_id x |>.sub_const a
        have h2 : HasDerivAt (fun y => (y - a)^2) (2 * (x - a)) x := by
          have := h1.pow 2
          simp only [pow_one, Nat.add_one_sub_one, Nat.succ_eq_add_one] at this
          convert this using 1
          ring
        have h3 : HasDerivAt (fun y => (y - a)^2 / 2) ((2 * (x - a)) / 2) x := h2.div_const 2
        convert h3 using 1
        ring
      have hF_uIcc : ∀ x ∈ uIcc a b, HasDerivAt F (x - a) x := fun x _ => hF_deriv x
      have hF_int : IntervalIntegrable (fun x => x - a) MeasureTheory.volume a b :=
        (continuous_id.sub continuous_const).intervalIntegrable a b
      have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_uIcc hF_int
      simp only [F] at h_ftc
      rw [h_ftc]
      ring
    rw [h_integral_linear]
    ring

  -- Step 5: Apply monotonicity: ∫ (f'a + δ*(x-a)) ≤ ∫ f'
  have h_mono : ∫ x in a..b, (f' a + δ * (x - a)) ≤ ∫ x in a..b, f' x := by
    apply intervalIntegral.integral_mono_on hab.le h_lower_int hf'_int
    exact h_f'_lower

  -- Combine: f b - f a = ∫ f' ≥ ∫ (f'a + δ*(x-a)) = f'a*(b-a) + (δ/2)*(b-a)²
  rw [← h_ftc]
  linarith

-- Helper: Upper bound on linear term from derivative bound
private lemma linear_term_bound
    (f' : ℝ → ℝ) (σ ε : ℝ) (h_f'_bound : |f' (1 / 2)| ≤ ε) :
    |f' (1 / 2) * (σ - 1 / 2)| ≤ ε * |σ - 1 / 2| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right h_f'_bound (abs_nonneg _)

-- Helper: Handle σ > 1/2 case
private lemma convex_minimum_right
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (f'' : ℝ → ℝ)
    (σ δ ε : ℝ)
    (hσ_gt : σ > 1 / 2) (hδ : 0 < δ)
    (hε_small : ε < δ * |σ - 1 / 2| / 2)
    (hf_diff : ∀ ξ ∈ Icc (1 / 2) σ, HasDerivAt f (f' ξ) ξ)
    (hf'_diff : ∀ ξ ∈ Icc (1 / 2) σ, HasDerivAt f' (f'' ξ) ξ)
    (h_f'_bound : |f' (1 / 2)| ≤ ε)
    (h_f''_convex : ∀ ξ ∈ Icc (1 / 2) σ, f'' ξ ≥ δ) :
    f σ > f (1 / 2) := by
  -- f(σ) - f(1/2) ≥ f'(1/2)(σ - 1/2) + (δ/2)(σ - 1/2)²
  --               ≥ -ε|σ - 1/2| + (δ/2)(σ - 1/2)² > 0
  have h_ne : σ ≠ 1 / 2 := ne_of_gt hσ_gt
  have h_abs : |σ - 1 / 2| = σ - 1 / 2 := abs_of_pos (sub_pos.mpr hσ_gt)
  have h_dom := quadratic_dominates_linear σ δ ε h_ne hδ hε_small
  have h_lower := second_deriv_lower_bound f f' f'' (1/2) σ δ hσ_gt hf_diff hf'_diff h_f''_convex hδ
  have h_linear := linear_term_bound f' σ ε h_f'_bound
  rw [h_abs] at h_dom h_linear
  -- h_linear gives |f'(1/2)(σ - 1/2)| ≤ ε(σ - 1/2)
  -- This implies f'(1/2)(σ - 1/2) ≥ -ε(σ - 1/2)
  have h_lin_lower : f' (1 / 2) * (σ - 1 / 2) ≥ -ε * (σ - 1 / 2) := by
    have h1 := neg_abs_le (f' (1 / 2) * (σ - 1 / 2))
    linarith
  -- Now: f σ - f(1/2) ≥ f'(1/2)(σ-1/2) + (δ/2)(σ-1/2)²
  --                   ≥ -ε(σ-1/2) + (δ/2)(σ-1/2)²
  --                   > 0 (from h_dom)
  linarith

-- Helper: Reversed lower bound (for σ < 1/2 case)
-- Shows f(a) - f(b) ≥ f'(b)(a - b) + (δ/2)(a - b)²  (note: a-b < 0)
-- This is derived from Taylor expansion at b: f(a) = f(b) + f'(b)(a-b) + f''(c)(a-b)²/2
-- Since f'' ≥ δ, we get f(a) - f(b) ≥ f'(b)(a-b) + δ(a-b)²/2
private lemma second_deriv_lower_bound_rev
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (f'' : ℝ → ℝ)
    (a b δ : ℝ) (hab : a < b)
    (hf_diff : ∀ ξ ∈ Icc a b, HasDerivAt f (f' ξ) ξ)
    (hf'_diff : ∀ ξ ∈ Icc a b, HasDerivAt f' (f'' ξ) ξ)
    (h_f''_pos : ∀ ξ ∈ Icc a b, f'' ξ ≥ δ) (hδ : 0 < δ) :
    f a - f b ≥ f' b * (a - b) + (δ / 2) * (a - b)^2 := by
  -- Strategy: Define g(x) = f(x) - f(b) - f'(b)(x-b) - (δ/2)(x-b)²
  -- Show g(b) = 0 and g'(x) ≤ 0 for x ∈ [a,b], so g(a) ≥ g(b) = 0

  -- Key facts
  have h_pos : b - a > 0 := sub_pos.mpr hab
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab.le

  -- Continuity for later
  have hf_cont : ContinuousOn f (Icc a b) :=
    fun x hx => (hf_diff x hx).continuousAt.continuousWithinAt
  have hf'_cont : ContinuousOn f' (Icc a b) :=
    fun x hx => (hf'_diff x hx).continuousAt.continuousWithinAt

  -- Define g(x) = f(x) - f(b) - f'(b)(x-b) - (δ/2)(x-b)²
  let g : ℝ → ℝ := fun x => f x - f b - f' b * (x - b) - (δ / 2) * (x - b)^2

  -- g(b) = 0
  have hg_b : g b = 0 := by simp only [g, sub_self, mul_zero, sq, zero_mul]

  -- g'(x) = f'(x) - f'(b) - δ(x-b)
  have hg_deriv : ∀ x ∈ Icc a b, HasDerivAt g (f' x - f' b - δ * (x - b)) x := by
    intro x hx
    have hf_x : HasDerivAt f (f' x) x := hf_diff x hx
    have h1 : HasDerivAt (fun y => f y - f b) (f' x) x := hf_x.sub_const _
    have h2 : HasDerivAt (fun y => f' b * (y - b)) (f' b) x := by
      have hsub : HasDerivAt (fun y => y - b) 1 x := (hasDerivAt_id x).sub_const b
      have := hsub.const_mul (f' b)
      simp only [mul_one] at this
      convert this using 1
    have h3 : HasDerivAt (fun y => (δ / 2) * (y - b)^2) (δ * (x - b)) x := by
      have hsub : HasDerivAt (fun y => y - b) 1 x := (hasDerivAt_id x).sub_const b
      have hsq : HasDerivAt (fun y => (y - b)^2) (2 * (x - b)) x := by
        have := hsub.pow 2
        simp only [pow_one, Nat.add_one_sub_one] at this
        convert this using 1
        ring
      have := hsq.const_mul (δ / 2)
      convert this using 1
      ring
    have h12 : HasDerivAt (fun y => f y - f b - f' b * (y - b)) (f' x - f' b) x :=
      h1.sub h2
    have h123 : HasDerivAt g (f' x - f' b - δ * (x - b)) x := h12.sub h3
    exact h123

  -- Key: g'(x) ≤ 0 for x ∈ [a, b]
  -- Because f'(x) - f'(b) = f''(c)(x-b) for some c, and since x ≤ b, (x-b) ≤ 0
  -- and f''(c) ≥ δ, so f''(c)(x-b) ≤ δ(x-b), thus g'(x) = (f''(c) - δ)(x-b) ≤ 0
  have hg'_nonpos : ∀ x ∈ Icc a b, f' x - f' b - δ * (x - b) ≤ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · simp  -- x = b case
    · -- x < b: Use MVT on f' over [x, b]
      have h_f'_cont_xb : ContinuousOn f' (Icc x b) :=
        hf'_cont.mono (Icc_subset_Icc hx.1 le_rfl)
      have hf'_diff_xb : ∀ ξ ∈ Ioo x b, HasDerivAt f' (f'' ξ) ξ := by
        intro ξ hξ
        have hξ_mem : ξ ∈ Icc a b := ⟨hx.1.trans hξ.1.le, hξ.2.le⟩
        exact hf'_diff ξ hξ_mem
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f' f'' hxb h_f'_cont_xb hf'_diff_xb
      have h_c_in_ab : c ∈ Icc a b := ⟨hx.1.trans hc_mem.1.le, hc_mem.2.le⟩
      have h_f''_c : f'' c ≥ δ := h_f''_pos c h_c_in_ab
      have h_xb_neg : x - b < 0 := sub_neg.mpr hxb
      -- f'(b) - f'(x) = f''(c) * (b - x), so f'(x) - f'(b) = -f''(c) * (b - x) = f''(c) * (x - b)
      have h_f'_diff_eq : f' b - f' x = f'' c * (b - x) := by
        have hne : b - x ≠ 0 := ne_of_gt (sub_pos.mpr hxb)
        field_simp [hne] at hc_eq ⊢
        linarith
      have h_rewrite : f' x - f' b = f'' c * (x - b) := by
        have := h_f'_diff_eq
        linarith
      -- g'(x) = f''(c)(x-b) - δ(x-b) = (f''(c) - δ)(x-b) ≤ 0
      -- since f''(c) ≥ δ and (x-b) < 0
      calc f' x - f' b - δ * (x - b)
          = f'' c * (x - b) - δ * (x - b) := by rw [h_rewrite]
        _ = (f'' c - δ) * (x - b) := by ring
        _ ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos
            · linarith  -- f''(c) - δ ≥ 0
            · linarith  -- x - b ≤ 0

  -- g is decreasing on [a, b], so g(a) ≥ g(b)
  have hg_mono : ∀ x ∈ Icc a b, g x ≥ g b := by
    intro x hx
    -- Use Monotone.ge_of_le or apply FTC directly
    -- g(b) - g(x) = ∫_x^b g'(t) dt ≤ 0 (since g' ≤ 0), so g(x) ≥ g(b)
    have hg_cont : ContinuousOn g (Icc a b) := by
      apply ContinuousOn.sub
      apply ContinuousOn.sub
      apply ContinuousOn.sub hf_cont
      · exact continuousOn_const
      · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
      · exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · rfl  -- x = b
    · -- x < b
      have hg_cont_xb : ContinuousOn g (Icc x b) :=
        hg_cont.mono (Icc_subset_Icc hx.1 le_rfl)
      have hg_deriv_xb : ∀ ξ ∈ uIcc x b, HasDerivAt g (f' ξ - f' b - δ * (ξ - b)) ξ := by
        intro ξ hξ
        rw [uIcc_of_le hxb.le] at hξ
        have hξ_mem : ξ ∈ Icc a b := ⟨hx.1.trans hξ.1, hξ.2⟩
        exact hg_deriv ξ hξ_mem
      have hg'_int : IntervalIntegrable (fun ξ => f' ξ - f' b - δ * (ξ - b)) MeasureTheory.volume x b := by
        apply IntervalIntegrable.sub
        apply IntervalIntegrable.sub
        · exact hf'_cont.mono (Icc_subset_Icc hx.1 le_rfl) |>.intervalIntegrable_of_Icc hxb.le
        · exact intervalIntegrable_const
        · exact ((continuous_id.sub continuous_const).intervalIntegrable x b).const_mul δ
      have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv_xb hg'_int
      -- g(b) - g(x) = ∫_x^b g'(t) dt
      -- Since g' ≤ 0 on [x,b], the integral ≤ 0, so g(b) - g(x) ≤ 0, i.e., g(x) ≥ g(b)
      have h_int_nonpos : ∫ t in x..b, (f' t - f' b - δ * (t - b)) ≤ 0 := by
        have h_neg_nonneg : ∀ t ∈ Icc x b, 0 ≤ -(f' t - f' b - δ * (t - b)) := fun t ht => by
          have ht_mem : t ∈ Icc a b := ⟨hx.1.trans ht.1, ht.2⟩
          linarith [hg'_nonpos t ht_mem]
        have h_nonneg : 0 ≤ ∫ t in x..b, -(f' t - f' b - δ * (t - b)) :=
          intervalIntegral.integral_nonneg hxb.le h_neg_nonneg
        simp only [intervalIntegral.integral_neg] at h_nonneg
        linarith
      have h_sub : g b - g x = ∫ t in x..b, (f' t - f' b - δ * (t - b)) := h_ftc.symm
      linarith

  -- Conclude: g(a) ≥ g(b) = 0, which gives the result
  have hg_a := hg_mono a ha_mem
  rw [hg_b] at hg_a
  -- g(a) ≥ 0 means f(a) - f(b) - f'(b)(a-b) - (δ/2)(a-b)² ≥ 0
  simp only [g, ge_iff_le, sub_nonneg] at hg_a
  linarith

-- Helper: Handle σ < 1/2 case (symmetric)
private lemma convex_minimum_left
    (f : ℝ → ℝ) (f' : ℝ → ℝ) (f'' : ℝ → ℝ)
    (σ δ ε : ℝ)
    (hσ_lt : σ < 1 / 2) (hδ : 0 < δ)
    (hε_small : ε < δ * |σ - 1 / 2| / 2)
    (hf_diff : ∀ ξ ∈ Icc σ (1 / 2), HasDerivAt f (f' ξ) ξ)
    (hf'_diff : ∀ ξ ∈ Icc σ (1 / 2), HasDerivAt f' (f'' ξ) ξ)
    (h_f'_bound : |f' (1 / 2)| ≤ ε)
    (h_f''_convex : ∀ ξ ∈ Icc σ (1 / 2), f'' ξ ≥ δ) :
    f σ > f (1 / 2) := by
  -- f(σ) - f(1/2) ≥ f'(1/2)(σ - 1/2) + (δ/2)(σ - 1/2)²
  --               ≥ -ε|σ - 1/2| + (δ/2)(σ - 1/2)² > 0
  have h_ne : σ ≠ 1 / 2 := ne_of_lt hσ_lt
  have h_abs : |σ - 1 / 2| = 1 / 2 - σ := by
    rw [abs_of_neg (sub_neg.mpr hσ_lt)]
    ring
  have h_dom := quadratic_dominates_linear σ δ ε h_ne hδ hε_small
  have h_lower := second_deriv_lower_bound_rev f f' f'' σ (1/2) δ hσ_lt hf_diff hf'_diff h_f''_convex hδ
  have h_linear := linear_term_bound f' σ ε h_f'_bound
  -- h_lower: f σ - f (1/2) ≥ f' (1/2) * (σ - 1/2) + (δ/2)(σ - 1/2)²
  -- h_linear: |f' (1/2) * (σ - 1/2)| ≤ ε * |σ - 1/2|
  -- So f' (1/2) * (σ - 1/2) ≥ -ε * |σ - 1/2|
  -- h_dom: (δ/2)(σ - 1/2)² - ε|σ - 1/2| > 0
  have h_lin_lower : f' (1 / 2) * (σ - 1 / 2) ≥ -ε * |σ - 1 / 2| := by
    have := h_linear
    rw [abs_mul] at this
    -- neg_abs_le gives -|x| ≤ x, which is equivalent to x ≥ -|x|
    have h1 : f' (1 / 2) * (σ - 1 / 2) ≥ -|f' (1 / 2) * (σ - 1 / 2)| :=
      neg_abs_le (f' (1 / 2) * (σ - 1 / 2))
    have h2 : |f' (1 / 2) * (σ - 1 / 2)| = |f' (1 / 2)| * |σ - 1 / 2| := abs_mul _ _
    rw [h2] at h1
    linarith
  rw [h_abs] at h_dom h_lin_lower
  have h_sq_eq : (σ - 1 / 2)^2 = (1 / 2 - σ)^2 := by ring
  rw [h_sq_eq] at h_lower
  linarith

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
  -- Split into σ > 1/2 and σ < 1/2 cases
  rcases lt_trichotomy σ (1 / 2) with hσ_lt | hσ_eq | hσ_gt
  · -- Case: σ < 1/2
    simp only [min_eq_left hσ_lt.le, max_eq_right hσ_lt.le] at hf_diff hf'_diff h_f''_convex
    exact convex_minimum_left f f' f'' σ δ ε hσ_lt hδ hε_small hf_diff hf'_diff h_f'_bound h_f''_convex
  · -- Case: σ = 1/2 (contradicts hσ)
    exact absurd hσ_eq hσ.2.2
  · -- Case: σ > 1/2
    simp only [min_eq_right hσ_gt.le, max_eq_left hσ_gt.le] at hf_diff hf'_diff h_f''_convex
    exact convex_minimum_right f f' f'' σ δ ε hσ_gt hδ hε_small hf_diff hf'_diff h_f'_bound h_f''_convex

end ProofEngine
