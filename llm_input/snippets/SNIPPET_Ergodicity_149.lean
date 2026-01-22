/-!
# SNIPPET: Ergodicity.lean line 149
# Target: time_average_orthogonality
# Status: PROPOSED (from Agent 3)
# Confidence: HIGH
-/

-- Proposed proof for time_average_orthogonality:
-- Uses product-to-sum formula and oscillating_integral_vanishes

/-
theorem time_average_orthogonality (p q : ℕ) (_hp : Nat.Prime p) (_hq : Nat.Prime q)
    (_hne : p ≠ q) :
    Tendsto (fun T => (1 / T) * ∫ t in Icc 0 T,
      Real.sin (t * Real.log p) * Real.sin (t * Real.log q)) atTop (nhds 0) := by
-/

-- PROOF:
have h_product : ∀ T, 0 ≤ T →
    ∫ t in Icc 0 T, Real.sin (t * Real.log p) * Real.sin (t * Real.log q) =
      (1 / 2) * ∫ t in Icc 0 T, Real.cos (t * (Real.log p - Real.log q)) -
      (1 / 2) * ∫ t in Icc 0 T, Real.cos (t * (Real.log p + Real.log q)) := by
  intro T hT
  simp_rw [Real.sin_mul_sin]
  rw [integral_sub, integral_const_mul, integral_const_mul]
  · simp [mul_comm]
  all_goals { apply Continuous.intervalIntegrable; continuity }
have h_freq_diff : Real.log p - Real.log q ≠ 0 := by
  intro h_eq
  have : Real.log p = Real.log q := by linarith
  have hp_pos : 1 < p := Nat.Prime.one_lt _hp
  have hq_pos : 1 < q := Nat.Prime.one_lt _hq
  have : p = q := by
    apply Nat.cast_injective (α := ℝ)
    exact Real.log_injOn_pos (Nat.cast_pos.mpr (Nat.Prime.pos _hp))
      (Nat.cast_pos.mpr (Nat.Prime.pos _hq)) this
  exact _hne this
have h_freq_sum : Real.log p + Real.log q ≠ 0 := by
  have hp_pos : 0 < Real.log p := Real.log_pos (by omega : 1 < (p : ℝ))
  have hq_pos : 0 < Real.log q := Real.log_pos (by omega : 1 < (q : ℝ))
  linarith
have h_term1 : Tendsto (fun T => (1 / T) * ((1 / 2) * ∫ t in Icc 0 T,
    Real.cos (t * (Real.log p - Real.log q)))) atTop (nhds 0) := by
  have := oscillating_integral_vanishes (Real.log p - Real.log q) h_freq_diff
  simp_rw [mul_comm (Real.log p - Real.log q)]
  convert Tendsto.const_mul (1 / 2) this using 1
  ext T; ring
have h_term2 : Tendsto (fun T => (1 / T) * ((1 / 2) * ∫ t in Icc 0 T,
    Real.cos (t * (Real.log p + Real.log q)))) atTop (nhds 0) := by
  have := oscillating_integral_vanishes (Real.log p + Real.log q) h_freq_sum
  simp_rw [mul_comm (Real.log p + Real.log q)]
  convert Tendsto.const_mul (1 / 2) this using 1
  ext T; ring
have h_eventually : (fun T => (1 / T) * ∫ t in Icc 0 T,
    Real.sin (t * Real.log p) * Real.sin (t * Real.log q)) =ᶠ[atTop]
    fun T => (1 / T) * ((1 / 2) * ∫ t in Icc 0 T, Real.cos (t * (Real.log p - Real.log q))) -
      (1 / T) * ((1 / 2) * ∫ t in Icc 0 T, Real.cos (t * (Real.log p + Real.log q))) := by
  refine (eventually_atTop.2 ?_)
  refine ⟨0, ?_⟩
  intro T _
  rw [h_product T (by linarith)]
  ring
have h_limit : Tendsto (fun T => (1 / T) * ((1 / 2) * ∫ t in Icc 0 T,
    Real.cos (t * (Real.log p - Real.log q))) -
    (1 / T) * ((1 / 2) * ∫ t in Icc 0 T, Real.cos (t * (Real.log p + Real.log q))))
    atTop (nhds 0) := by
  simpa using h_term1.sub h_term2
exact Filter.Tendsto.congr' h_eventually.symm h_limit
