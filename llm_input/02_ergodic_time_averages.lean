import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
open Real Filter Topology MeasureTheory Interval intervalIntegral BigOperators

namespace ErgodicTimeAverages

/-!
## 1. Helper Lemmas
-/

lemma log_pos_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 < Real.log p :=
  Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt)

lemma log_ne_zero_of_prime {p : ℕ} (hp : Nat.Prime p) : Real.log p ≠ 0 :=
  ne_of_gt (log_pos_of_prime hp)

/-- Distinct primes have distinct logs. -/
lemma log_ne_log_of_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Real.log p ≠ Real.log q := by
  intro hlog
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hcast : (p : ℝ) = (q : ℝ) := by
    have := congrArg Real.exp hlog
    simp only [Real.exp_log hp_pos, Real.exp_log hq_pos] at this
    exact this
  exact hne (Nat.cast_injective hcast)

/-!
## 2. Integrability
-/

lemma intervalIntegrable_sin_mul (w : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => sin (w * t)) volume a b := by
  apply Continuous.intervalIntegrable
  exact continuous_sin.comp (continuous_const.mul continuous_id)

lemma intervalIntegrable_cos_mul (w : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => cos (w * t)) volume a b := by
  apply Continuous.intervalIntegrable
  exact continuous_cos.comp (continuous_const.mul continuous_id)

/-!
## 3. Squeeze Theorem Limits
-/

/-- Helper: 1/T -> 0 as T -> ∞ -/
lemma tendsto_inv_atTop_zero' : Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero

/--
**SOLVED (Q1)**: Squeeze theorem for sin(wT)/T -> 0.
Proof: -1/T ≤ sin(wT)/T ≤ 1/T. Both bounds go to 0.
-/
lemma tendsto_sin_mul_div_atTop_zero (w : ℝ) :
    Tendsto (fun T => sin (w * T) / T) atTop (𝓝 0) := by
  -- Use squeeze: |sin(wT)/T| ≤ 1/T → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  use 2/ε  -- Use 2/ε to get strict inequality
  intro T hT
  rw [Real.dist_eq, sub_zero]
  have hε_inv_pos : 0 < 2/ε := by positivity
  have hT_pos : 0 < T := lt_of_lt_of_le hε_inv_pos hT
  rw [abs_div, abs_of_pos hT_pos]
  have h_bound : |sin (w * T)| / T < ε := by
    have h1 : |sin (w * T)| ≤ 1 := abs_sin_le_one _
    have h2 : 2/ε ≤ T := hT
    have h3 : 0 < ε := hε
    have h4 : 0 < T := hT_pos
    -- From 2/ε ≤ T we get 2 ≤ ε * T, hence 1 < ε * T
    have h5 : 1 < ε * T := by
      have : 2 ≤ ε * T := by
        calc ε * T ≥ ε * (2/ε) := by nlinarith
          _ = 2 := by field_simp
      linarith
    calc |sin (w * T)| / T ≤ 1 / T := by
           apply div_le_div_of_nonneg_right h1 (le_of_lt h4)
      _ < ε := by
           rw [div_lt_iff₀ h4]
           linarith
  exact h_bound

/-- Same logic for cos(wT)/T -> 0 -/
lemma tendsto_cos_mul_div_atTop_zero (w : ℝ) :
    Tendsto (fun T => cos (w * T) / T) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  use 2/ε  -- Use 2/ε to get strict inequality
  intro T hT
  rw [Real.dist_eq, sub_zero]
  have hε_inv_pos : 0 < 2/ε := by positivity
  have hT_pos : 0 < T := lt_of_lt_of_le hε_inv_pos hT
  rw [abs_div, abs_of_pos hT_pos]
  have h_bound : |cos (w * T)| / T < ε := by
    have h1 : |cos (w * T)| ≤ 1 := abs_cos_le_one _
    have h2 : 2/ε ≤ T := hT
    have h3 : 0 < ε := hε
    have h4 : 0 < T := hT_pos
    -- From 2/ε ≤ T we get 2 ≤ ε * T, hence 1 < ε * T
    have h5 : 1 < ε * T := by
      have : 2 ≤ ε * T := by
        calc ε * T ≥ ε * (2/ε) := by nlinarith
          _ = 2 := by field_simp
      linarith
    calc |cos (w * T)| / T ≤ 1 / T := by
           apply div_le_div_of_nonneg_right h1 (le_of_lt h4)
      _ < ε := by
           rw [div_lt_iff₀ h4]
           linarith
  exact h_bound

/-!
## 4. Oscillating Integrals Vanish
-/

/--
**SOLVED (Q2)**: Integral of cos(wt) vanishes in the average.
Uses Fundamental Theorem of Calculus directly.
-/
theorem oscillating_cos_limit (w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, cos (w * t)) atTop (𝓝 0) := by
  -- Step 1: Evaluate integral using FTC
  have h_int : ∀ T, ∫ t in (0:ℝ)..T, cos (w * t) = sin (w * T) / w := by
    intro T
    -- We show derivative of (sin(wt)/w) is cos(wt)
    have h_deriv : ∀ t, HasDerivAt (fun x => sin (w * x) / w) (cos (w * t)) t := by
      intro t
      have h1 : HasDerivAt (fun x => w * x) w t := by
        have := (hasDerivAt_id t).const_mul w
        simp only [mul_one] at this
        exact this
      have h2 := h1.sin
      convert h2.div_const w using 1
      field_simp [hw]
    rw [integral_eq_sub_of_hasDerivAt (fun t _ => h_deriv t) (intervalIntegrable_cos_mul w 0 T)]
    simp [mul_zero]

  simp_rw [h_int]
  -- Step 2: Use the limit lemma
  -- (1/T) * (sin/w) = (1/w) * (sin/T)
  have h_rewrite : ∀ T, (1 / T) * (sin (w * T) / w) = (1 / w) * (sin (w * T) / T) :=
    fun T => by ring
  simp_rw [h_rewrite]
  have h := tendsto_sin_mul_div_atTop_zero w
  have : Tendsto (fun k => 1 / w * (sin (w * k) / k)) atTop (𝓝 (1 / w * 0)) :=
    Tendsto.const_mul (1/w) h
  simp only [mul_zero] at this
  exact this

/--
**SOLVED (Q3)**: Integral of sin(wt) vanishes in the average.
-/
theorem oscillating_sin_limit (w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, sin (w * t)) atTop (𝓝 0) := by
  -- Step 1: Evaluate integral
  have h_int : ∀ T, ∫ t in (0:ℝ)..T, sin (w * t) = (1 - cos (w * T)) / w := by
    intro T
    have h_deriv : ∀ t, HasDerivAt (fun x => -cos (w * x) / w) (sin (w * t)) t := by
      intro t
      have h1 : HasDerivAt (fun x => w * x) w t := by
        have := (hasDerivAt_id t).const_mul w
        simp only [mul_one] at this
        exact this
      have h2 := (h1.cos.neg).div_const w
      -- h2 : HasDerivAt (fun x => -cos (w * x) / w) (-(- sin (w * t) * w) / w) t
      -- We need: HasDerivAt (fun x => -cos (w * x) / w) (sin (w * t)) t
      have h_eq : -(- sin (w * t) * w) / w = sin (w * t) := by field_simp [hw]
      rw [h_eq] at h2
      exact h2
    rw [integral_eq_sub_of_hasDerivAt (fun t _ => h_deriv t) (intervalIntegrable_sin_mul w 0 T)]
    simp [mul_zero, cos_zero]; ring

  simp_rw [h_int]
  -- Step 2: Rewrite as difference of limits
  have h_rewrite : ∀ T, (1/T) * ((1 - cos (w * T)) / w) = (1/w) * (1/T) - (1/w) * (cos (w * T) / T) :=
    fun T => by ring
  simp_rw [h_rewrite]

  have h1 : Tendsto (fun T => 1/w * (1/T)) atTop (𝓝 0) := by
    have := Tendsto.const_mul (1/w) tendsto_inv_atTop_zero'
    simp only [mul_zero] at this
    exact this
  have h2 : Tendsto (fun T => 1/w * (cos (w * T)/T)) atTop (𝓝 0) := by
    have := Tendsto.const_mul (1/w) (tendsto_cos_mul_div_atTop_zero w)
    simp only [mul_zero] at this
    exact this
  have h_sub := Tendsto.sub h1 h2
  simp only [sub_zero] at h_sub
  exact h_sub

/-!
## 5. Product-to-Sum & Orthogonality
-/

/-- **SOLVED (Q4)**: Trig identity -/
lemma sin_mul_sin_eq (a b : ℝ) :
    sin a * sin b = (1 / 2) * (cos (a - b) - cos (a + b)) := by
  rw [cos_sub, cos_add]; ring

/--
**Main Theorem**: Orthogonality of primes in time average.
-/
theorem time_average_orthogonality (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, sin (t * log p) * sin (t * log q)) atTop (𝓝 0) := by
  have hw₁ : log p - log q ≠ 0 := sub_ne_zero.mpr (log_ne_log_of_primes hp hq hne)
  have hw₂ : log p + log q ≠ 0 := ne_of_gt (add_pos (log_pos_of_prime hp) (log_pos_of_prime hq))

  -- 1. Apply product-to-sum identity: sin(a)*sin(b) = (1/2)*(cos(a-b) - cos(a+b))
  have h_transform : ∀ t, sin (t * log p) * sin (t * log q) =
      (1/2) * (cos ((log p - log q) * t) - cos ((log p + log q) * t)) := by
    intro t
    have := sin_mul_sin_eq (t * log p) (t * log q)
    convert this using 2 <;> ring

  have h_int_eq : ∀ T, ∫ t in (0:ℝ)..T, sin (t * log p) * sin (t * log q) =
      (1/2) * (∫ t in (0:ℝ)..T, cos ((log p - log q) * t)) -
      (1/2) * (∫ t in (0:ℝ)..T, cos ((log p + log q) * t)) := by
    intro T
    simp_rw [h_transform]
    -- First expand 1/2 * (a - b) = 1/2 * a - 1/2 * b inside the integral
    have h_expand : ∀ t, (1/2 : ℝ) * (cos ((log p - log q) * t) - cos ((log p + log q) * t)) =
        (1/2) * cos ((log p - log q) * t) - (1/2) * cos ((log p + log q) * t) :=
      fun t => by ring
    simp_rw [h_expand]
    -- Now split the integral of difference
    rw [intervalIntegral.integral_sub]
    -- And pull out the constants
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact (intervalIntegrable_cos_mul _ 0 T).const_mul _
    · exact (intervalIntegrable_cos_mul _ 0 T).const_mul _

  simp_rw [h_int_eq]

  -- 2. Distribute 1/T and take limits
  have h_limit_form : ∀ T, (1/T) * ((1/2) * (∫ t in (0:ℝ)..T, cos ((log p - log q) * t)) -
                                    (1/2) * (∫ t in (0:ℝ)..T, cos ((log p + log q) * t))) =
      (1/2) * ((1/T) * ∫ t in (0:ℝ)..T, cos ((log p - log q) * t)) -
      (1/2) * ((1/T) * ∫ t in (0:ℝ)..T, cos ((log p + log q) * t)) := fun T => by ring

  simp_rw [h_limit_form]

  have h1 : Tendsto (fun T => 1/2 * ((1/T) * ∫ t in (0:ℝ)..T, cos ((log p - log q) * t))) atTop (𝓝 0) := by
    have := Tendsto.const_mul (1/2) (oscillating_cos_limit _ hw₁)
    simp only [mul_zero] at this
    exact this
  have h2 : Tendsto (fun T => 1/2 * ((1/T) * ∫ t in (0:ℝ)..T, cos ((log p + log q) * t))) atTop (𝓝 0) := by
    have := Tendsto.const_mul (1/2) (oscillating_cos_limit _ hw₂)
    simp only [mul_zero] at this
    exact this
  have h_sub := Tendsto.sub h1 h2
  simp only [sub_zero] at h_sub
  exact h_sub

end ErgodicTimeAverages
