import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open Real Filter Topology MeasureTheory Interval intervalIntegral BigOperators

-- Dummy namespace to handle the missing external import for Atom 9
namespace GlobalBound

/-- Representation of noise as sum of phases, assuming structure from context. -/
def NoiseGrowth (S : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ S, sin (t * log p)

end GlobalBound

namespace ProofEngine

/-!
## Ergodicity Helper Lemmas (Atomic Units)

These lemmas establish that time averages of oscillating functions vanish,
which is key to the ergodic theory component of the Clifford RH proof.
-/

/-!
### Prime Frequency Helper Lemmas

These lemmas establish that log(p) is positive and nonzero for primes,
and that distinct primes have distinct logs.
-/

/-- For a prime `p`, `log p > 0` (as a real). -/
lemma log_pos_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 < Real.log (p : ℝ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  simpa using Real.log_pos hp1

/-- For a prime `p`, `log p ≠ 0`. -/
lemma log_ne_zero_of_prime {p : ℕ} (hp : Nat.Prime p) : Real.log (p : ℝ) ≠ 0 := by
  exact ne_of_gt (log_pos_of_prime hp)

/-- Distinct primes have distinct real logs. -/
lemma log_ne_log_of_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Real.log (p : ℝ) ≠ Real.log (q : ℝ) := by
  intro hlog
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hcast : (p : ℝ) = (q : ℝ) := by
    have := congrArg Real.exp hlog
    simpa [Real.exp_log hp_pos, Real.exp_log hq_pos] using this
  exact hne (by exact_mod_cast hcast)

/-!
### Helper: Integrals of sin(w*t) and cos(w*t)

These derive from the composition lemmas and basic trig integrals in Mathlib.
-/

/-- The integral of sin(w*t) from 0 to T equals (1 - cos(w*T))/w for w ≠ 0. -/
lemma integral_sin_mul_eq (w T : ℝ) (hw : w ≠ 0) :
    ∫ t in (0:ℝ)..T, sin (w * t) = (1 - cos (w * T)) / w := by
  -- Use composition: ∫ sin(w*t) dt = w⁻¹ * ∫ sin(x) dx from 0 to w*T
  rw [integral_comp_mul_left _ hw]
  simp only [mul_zero, integral_sin, cos_zero, smul_eq_mul]
  ring

/-- The integral of cos(w*t) from 0 to T equals sin(w*T)/w for w ≠ 0. -/
lemma integral_cos_mul_eq (w T : ℝ) (hw : w ≠ 0) :
    ∫ t in (0:ℝ)..T, cos (w * t) = sin (w * T) / w := by
  rw [integral_comp_mul_left _ hw]
  simp only [mul_zero, integral_cos, sin_zero, sub_zero, smul_eq_mul]
  ring

/-!
### Atom 1: Integral of sin(w*t) is bounded
-/

/-- Atom 1: Integral of sin(w*t) is bounded for non-zero w. -/
lemma integral_sin_bounded (w : ℝ) (hw : w ≠ 0) (T : ℝ) :
    |∫ t in (0:ℝ)..T, sin (w * t)| ≤ 2 / |w| := by
  rw [integral_sin_mul_eq w T hw]
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg w)
  -- |1 - cos(w*T)| ≤ |1| + |cos(w*T)| ≤ 1 + 1 = 2
  calc |1 - cos (w * T)|
      ≤ |1| + |cos (w * T)| := abs_sub _ _
    _ ≤ 1 + 1 := by simp [abs_cos_le_one]
    _ = 2 := by norm_num

/-!
### Atom 2: Bounded function divided by T → 0
-/

/-- Atom 2: A bounded function divided by T tends to zero as T -> infinity. -/
lemma tendsto_bounded_div_atTop {f : ℝ → ℝ} (M : ℝ) (_hM : 0 ≤ M) (h_bound : ∀ T, |f T| ≤ M) :
    Tendsto (fun T => f T / T) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  use max 1 (M / ε + 1)
  intro T hT
  have hT_pos : T > 0 := by
    calc T ≥ max 1 (M / ε + 1) := hT
      _ ≥ 1 := le_max_left _ _
      _ > 0 := by norm_num
  rw [dist_eq_norm, sub_zero, norm_eq_abs, abs_div, abs_of_pos hT_pos]
  -- |f T| / T ≤ M / T
  have h1 : |f T| / T ≤ M / T := div_le_div_of_nonneg_right (h_bound T) (le_of_lt hT_pos)
  -- M / T < ε when T > M / ε
  have h2 : M / T < ε := by
    have hT_large : T > M / ε := by
      calc T ≥ max 1 (M / ε + 1) := hT
        _ ≥ M / ε + 1 := le_max_right _ _
        _ > M / ε := by linarith
    rw [div_lt_iff₀ hT_pos, mul_comm]
    -- hT_large : T > M / ε  means T * ε > M  (when ε > 0)
    have h3 : T * ε > M := by
      calc T * ε > (M / ε) * ε := by nlinarith [hT_large, hε]
        _ = M := by field_simp
    exact h3
  linarith

/-!
### Atom 3: Time average of sin(w*t) vanishes
-/

/-- Atom 3: The time average of a single oscillating sine wave vanishes. -/
theorem oscillating_integral_vanishes_proven (w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, sin (w * t)) atTop (𝓝 0) := by
  have h_eq : ∀ T, (1 / T) * ∫ t in (0:ℝ)..T, sin (w * t) = (∫ t in (0:ℝ)..T, sin (w * t)) / T := by
    intro T; ring
  simp_rw [h_eq]
  apply tendsto_bounded_div_atTop (2 / |w|) (by positivity)
  intro T
  exact integral_sin_bounded w hw T

/-!
### Atom 4: Trig identity sin(a)sin(b)
-/

/-- Atom 4: Trig identity sin(a)sin(b) = 1/2(cos(a-b) - cos(a+b)). -/
lemma sin_mul_sin_id (a b : ℝ) : sin a * sin b = (1 / 2) * (cos (a - b) - cos (a + b)) := by
  rw [cos_sub, cos_add]
  ring

/-!
### Atom 5: Time average of cos(w*t) vanishes
-/

/-- Atom 5: The time average of cos(w*t) vanishes for non-zero w. -/
theorem oscillating_cos_limit_proven (w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, cos (w * t)) atTop (𝓝 0) := by
  have h_eq : ∀ T, (1 / T) * ∫ t in (0:ℝ)..T, cos (w * t) = (∫ t in (0:ℝ)..T, cos (w * t)) / T := by
    intro T; ring
  simp_rw [h_eq]
  -- Bound: |∫ cos(w*t)| = |sin(w*T)/w| ≤ 1/|w|
  have h_bound : ∀ T, |∫ t in (0:ℝ)..T, cos (w * t)| ≤ 1 / |w| := by
    intro T
    rw [integral_cos_mul_eq w T hw, abs_div]
    apply div_le_div_of_nonneg_right (abs_sin_le_one _) (abs_nonneg w)
  apply tendsto_bounded_div_atTop (1 / |w|) (by positivity) h_bound

/-!
### Atom 6: Time average orthogonality of sin(at) and sin(bt)

This requires the product-to-sum formula and showing both resulting cosine
averages vanish when the frequencies are distinct.

**POTENTIAL ISSUES**:
1. The original proposal used `Real.sin_mul_sin` which does NOT exist in Mathlib.
   Mathlib has `Real.two_mul_sin_mul_sin : 2 * sin x * sin y = cos (x - y) - cos (x + y)`
   We use the local `sin_mul_sin_id` instead (Atom 4 above).
2. The `simpa` line assumes `oscillating_cos_limit_proven` works with the frequency form.
   May need explicit `mul_comm` to convert `t * log p` to `(log p) * t`.
3. The final `simp`/`ring_nf` block depends on exact term ordering - may need adjustment.
-/

/-- Atom 6: Time average orthogonality of sin(at) and sin(bt). -/
theorem time_average_orthogonality_proven (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, sin (t * log p) * sin (t * log q))
      atTop (𝓝 0) := by
  -- Frequencies
  have hlog_ne : Real.log (p : ℝ) ≠ Real.log (q : ℝ) :=
    log_ne_log_of_primes hp hq hne
  have hw₁ : (Real.log (p : ℝ) - Real.log (q : ℝ)) ≠ 0 := sub_ne_zero.mpr hlog_ne
  have hw₂ : (Real.log (p : ℝ) + Real.log (q : ℝ)) ≠ 0 := by
    have : 0 < Real.log (p : ℝ) + Real.log (q : ℝ) :=
      add_pos (log_pos_of_prime hp) (log_pos_of_prime hq)
    exact ne_of_gt this

  -- The two cosine averages go to 0
  -- **POTENTIAL ISSUE**: The `simpa` may fail if the frequency form doesn't match.
  -- `oscillating_cos_limit_proven` expects `cos (w * t)` but we have `cos ((log p - log q) * t)`.
  have hcos₁ :
      Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, cos ((Real.log (p:ℝ) - Real.log (q:ℝ)) * t))
        atTop (𝓝 0) := by
    -- `oscillating_cos_limit_proven` is stated for `cos (w * t)`
    simpa using (oscillating_cos_limit_proven (w := (Real.log (p:ℝ) - Real.log (q:ℝ))) hw₁)

  have hcos₂ :
      Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, cos ((Real.log (p:ℝ) + Real.log (q:ℝ)) * t))
        atTop (𝓝 0) := by
    simpa using (oscillating_cos_limit_proven (w := (Real.log (p:ℝ) + Real.log (q:ℝ))) hw₂)

  -- Combine via product-to-sum under the integral
  -- Using local `sin_mul_sin_id` : sin a * sin b = (1/2) * (cos (a - b) - cos (a + b))
  -- **NOTE**: Original proposal used `Real.sin_mul_sin` which does NOT exist in Mathlib.
  have hmain :
      Tendsto (fun T =>
        (1 / 2) *
          ( (1 / T) * ∫ t in (0:ℝ)..T, cos ((Real.log (p:ℝ) - Real.log (q:ℝ)) * t)
            - (1 / T) * ∫ t in (0:ℝ)..T, cos ((Real.log (p:ℝ) + Real.log (q:ℝ)) * t) ))
        atTop (𝓝 0) := by
    -- difference tends to 0, then scale by 1/2
    simpa [sub_eq_add_neg, mul_add, add_mul] using (hcos₁.sub hcos₂).const_mul (1 / 2)

  -- Now show the target expression is definitionally equal to the product-to-sum version.
  -- **POTENTIAL ISSUE**: The `simp_rw` and final `simp` may fail due to term ordering.
  -- May need explicit `mul_comm` to convert `t * log p` to `(log p) * t` for the identity.
  refine (hmain.congr' ?_)
  filter_upwards with T
  -- pointwise rewrite under the integral + linearity
  -- (the `mul_comm`/`mul_assoc` normalizations are just to match `w * t` form)
  simp_rw [sin_mul_sin_id]  -- Uses local Atom 4, not nonexistent `Real.sin_mul_sin`
  -- normalize `(t*log p) ± (t*log q)` to `((log p ± log q) * t)`
  -- and push constants through the interval integral
  -- (these `simp` facts are in Mathlib for interval integrals)
  ring_nf
  simp [mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-!
### Atom 7: sin²(wt) = 1/2(1 - cos(2wt))
-/

/-- Atom 7: sin²(wt) = 1/2(1 - cos(2wt)). -/
lemma sin_sq_id (w t : ℝ) : (sin (w * t)) ^ 2 = (1 / 2) * (1 - cos (2 * w * t)) := by
  -- Use sin²θ + cos²θ = 1 and cos(2θ) = 2cos²θ - 1
  have h1 := sin_sq_add_cos_sq (w * t)  -- sin² + cos² = 1
  have h2 := cos_two_mul (w * t)        -- cos(2θ) = 2cos²θ - 1
  -- From h1: sin² = 1 - cos²
  -- From h2: cos² = (cos(2θ) + 1)/2
  -- So: sin² = 1 - (cos(2θ) + 1)/2 = (2 - cos(2θ) - 1)/2 = (1 - cos(2θ))/2
  have h3 : cos (w * t) ^ 2 = (1 + cos (2 * (w * t))) / 2 := by linarith
  calc sin (w * t) ^ 2 = 1 - cos (w * t) ^ 2 := by linarith
    _ = 1 - (1 + cos (2 * (w * t))) / 2 := by rw [h3]
    _ = (1 / 2) * (1 - cos (2 * w * t)) := by ring_nf

/-!
### Atom 8: Time average of sin²(wt) is 1/2

**POTENTIAL ISSUES**:
1. The original proposal referenced `Real.sin_sq` but the exact form may differ.
   We use the local `sin_sq_id` (Atom 7) which is proven above.
2. The `simpa` chain in `hmain` may not produce the exact algebraic form needed.
3. Integral linearity (`integral_sub`, `integral_const`) may need integrability witnesses.
-/

/-- Atom 8: Time average of sin²(wt) is 1/2. -/
theorem sin_squared_average_proven (w : ℝ) (hw : w ≠ 0) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, (sin (w * t)) ^ 2) atTop (𝓝 (1 / 2)) := by
  have h2w : (2 * w) ≠ 0 := by nlinarith
  have hcos :
      Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, cos ((2 * w) * t)) atTop (𝓝 0) := by
    simpa using (oscillating_cos_limit_proven (w := (2 * w)) h2w)

  -- Main rewrite: sin²(wt) = (1 - cos(2*(w*t)))/2, then linearity
  -- We prove the limit of the rewritten expression, then `congr'`.
  have hmain :
      Tendsto (fun T =>
        (1 / 2) - (1 / 2) * ((1 / T) * ∫ t in (0:ℝ)..T, cos ((2 * w) * t)))
        atTop (𝓝 (1 / 2)) := by
    -- since the cosine-average → 0
    have := hcos.const_mul (-(1 / 2))
    -- rewrite to the exact algebraic shape
    -- ( (1/2) - (1/2) * x ) = (1/2) + (-(1/2)) * x
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using
      (tendsto_const_nhds.add this)

  refine (hmain.congr' ?_)
  filter_upwards with T
  -- Rewrite under the integral using sin_sq_id (Atom 7)
  -- **POTENTIAL ISSUE**: May need explicit integrability witnesses for `integral_sub`
  have hs : ∀ t : ℝ, (sin (w * t)) ^ 2 = (1 - cos (2 * (w * t))) / 2 := by
    intro t
    -- Use local sin_sq_id and normalize
    have := sin_sq_id w t
    -- sin_sq_id gives: (1/2) * (1 - cos(2*w*t))
    -- We need: (1 - cos(2*(w*t))) / 2
    -- These are equal: (1/2) * x = x / 2
    linarith [this]
  -- Use `hs` pointwise
  simp_rw [hs]
  ring_nf
  -- normalize `cos (2*(w*t))` to `cos ((2*w)*t)`
  simp [mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-!
### Atom 9: Noise (sum of sines) averages to zero

This uses Finset induction with:
- linearity of interval integrals (`integral_add`)
- linearity of finite sums (`Finset.sum_insert`)
- Atom 3 for each sine term (`oscillating_integral_vanishes_proven`)
- `log_ne_zero_of_prime` to discharge the "frequency nonzero" goal

**POTENTIAL ISSUES**:
1. `intervalIntegral.integral_add` requires integrability of both functions.
   For continuous functions this should be automatic but may need explicit handling.
2. The `simp` at the end depends on exact `NoiseGrowth` unfolding and `Finset.sum_insert`.
3. `mul_comm` normalization between `sin (t * log a)` and `sin ((log a) * t)`.
-/

/-- Atom 9: Noise (sum of sines) averages to zero if frequencies are non-zero. -/
theorem noise_averages_to_zero_proven (S : Finset ℕ) (h_primes : ∀ p ∈ S, Nat.Prime p) :
    Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, GlobalBound.NoiseGrowth S t) atTop (𝓝 0) := by
  classical
  -- Strengthen the induction hypothesis to carry the primality witness along.
  revert h_primes
  refine Finset.induction_on S ?h0 ?hstep
  · intro h_primes
    -- empty sum = 0
    simp [GlobalBound.NoiseGrowth]
  · intro a S ha_notin ih h_primes
    -- Split primality hypotheses
    have ha_prime : Nat.Prime a := by
      exact h_primes a (by simp [ha_notin])
    have h_primes_S : ∀ p ∈ S, Nat.Prime p := by
      intro p hp
      exact h_primes p (by simp [hp, ha_notin])

    -- Apply IH to the tail
    have ihS :
        Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, GlobalBound.NoiseGrowth S t) atTop (𝓝 0) :=
      ih h_primes_S

    -- The head term tends to 0 (Atom 3), with w = log a (nonzero for primes)
    have hhead :
        Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, sin ((Real.log (a:ℝ)) * t)) atTop (𝓝 0) := by
      exact oscillating_integral_vanishes_proven (w := Real.log (a:ℝ)) (log_ne_zero_of_prime ha_prime)

    -- Convert `sin (t * log a)` to `sin ((log a) * t)` and combine with IH
    have hhead' :
        Tendsto (fun T => (1 / T) * ∫ t in (0:ℝ)..T, sin (t * log (a:ℝ))) atTop (𝓝 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hhead

    -- Now `NoiseGrowth (insert a S) = sin(t log a) + NoiseGrowth S` and use linearity
    -- **POTENTIAL ISSUE**: `intervalIntegral.integral_add` needs integrability
    have hadd : Tendsto
        (fun T =>
          (1 / T) * ∫ t in (0:ℝ)..T, (sin (t * log (a:ℝ)) + GlobalBound.NoiseGrowth S t))
        atTop (𝓝 0) := by
      -- integral is linear, and limits add
      simpa [mul_add, intervalIntegral.integral_add] using (hhead'.add ihS)

    -- Finish by rewriting `NoiseGrowth (insert a S)` as head + tail
    -- and simplifying the finset sum.
    refine (hadd.congr' ?_)
    filter_upwards with T
    unfold GlobalBound.NoiseGrowth
    -- `∑ p ∈ insert a S, ...` = head + tail (since `a ∉ S`)
    simp [Finset.sum_insert, ha_notin, add_assoc, add_comm, add_left_comm]

end ProofEngine
