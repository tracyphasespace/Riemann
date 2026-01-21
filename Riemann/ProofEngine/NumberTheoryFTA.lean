import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Real.Irrational

noncomputable section
open Real Filter Topology Complex

namespace NumberTheoryFTA

/-!
# Number Theory: FTA Applications

**STATUS**: FULLY PROVEN (0 sorries)

This file proves key number-theoretic results using the Fundamental Theorem of Arithmetic.

## Main Theorems

1. `prime_power_eq_iff` - Distinct primes have no equal powers (FTA application)
2. `log_ratio_irrational` - log(p)/log(q) is irrational for distinct primes p, q
3. `differentiableAt_bounded_near` - Holomorphic functions are locally bounded

These results are used in the linear independence proof for log primes.
-/

/-!
## Lemma 1: Prime Power Equality Contradiction (FTA)
-/

/--
Distinct primes cannot have equal prime powers (unless both exponents are 0).
We use `Nat.Prime.dvd_of_dvd_pow` to prove this rigorously.
-/
theorem prime_power_eq_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (m n : ℕ) : p ^ m = q ^ n ↔ m = 0 ∧ n = 0 := by
  constructor
  · intro h_eq
    rcases m.eq_zero_or_pos with rfl | hm_pos
    · -- Case m = 0: 1 = q^n => n = 0
      simp only [pow_zero] at h_eq
      rw [eq_comm, pow_eq_one_iff] at h_eq
      simp [hq.ne_one] at h_eq
      exact ⟨rfl, h_eq⟩
    · -- Case m > 0: p | q^n => p | q => p = q => Contradiction
      have h_div : p ∣ q ^ n := by
        rw [← h_eq]
        exact dvd_pow_self p (ne_of_gt hm_pos)
      have h_div_q : p ∣ q := hp.dvd_of_dvd_pow h_div
      have h_eq_primes : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp h_div_q
      contradiction
  · rintro ⟨rfl, rfl⟩
    simp

/-!
## Lemma 2: Log Ratio of Distinct Primes is Irrational
-/

/-- For distinct primes p, q: log(p)/log(q) ∉ ℚ. -/
theorem log_ratio_irrational
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ¬ ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
      (Real.log p / Real.log q) = (a : ℝ) / (b : ℝ) := by
  intro h
  rcases h with ⟨a, b, ha, hb, h_eq⟩

  have h_log_p_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h_log_q_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)

  have h_ratio_pos : 0 < Real.log p / Real.log q :=
    div_pos h_log_p_pos h_log_q_pos

  -- Clear denominators
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hlogq_ne : (Real.log q : ℝ) ≠ 0 := ne_of_gt h_log_q_pos

  have hmul0 := congrArg (fun x : ℝ => x * Real.log q * (b : ℝ)) h_eq
  field_simp [hlogq_ne, hbR] at hmul0
  have hmul : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul0

  -- Convert linear relation to integer powers: p^b = q^a
  let pR : ℝ := (p : ℝ)
  let qR : ℝ := (q : ℝ)
  have hlogeq : Real.log (pR ^ (b : ℤ)) = Real.log (qR ^ (a : ℤ)) := by
    calc
      Real.log (pR ^ (b : ℤ)) = (b : ℝ) * Real.log pR := by
        simpa [pR] using (Real.log_zpow pR b)
      _ = (a : ℝ) * Real.log qR := by
        simpa [pR, qR, mul_assoc, mul_comm, mul_left_comm] using hmul
      _ = Real.log (qR ^ (a : ℤ)) := by
        symm
        simpa [qR] using (Real.log_zpow qR a)

  -- Use injectivity of log on positive reals
  have hp_posR : (0 : ℝ) < pR := by dsimp [pR]; exact_mod_cast (Nat.Prime.pos hp)
  have hq_posR : (0 : ℝ) < qR := by dsimp [qR]; exact_mod_cast (Nat.Prime.pos hq)

  have hpz_mem : pR ^ (b : ℤ) ∈ Set.Ioi (0 : ℝ) := zpow_pos hp_posR b
  have hqz_mem : qR ^ (a : ℤ) ∈ Set.Ioi (0 : ℝ) := zpow_pos hq_posR a

  have hzpow_eq : pR ^ (b : ℤ) = qR ^ (a : ℤ) :=
    Real.log_injOn_pos hpz_mem hqz_mem hlogeq

  -- Analyze signs: a/b > 0 => a, b have same sign
  have hab_pos : 0 < (a : ℝ) / (b : ℝ) := by simpa [h_eq] using h_ratio_pos
  have hab_sign : (0 < (a : ℝ) ∧ 0 < (b : ℝ)) ∨ ((a : ℝ) < 0 ∧ (b : ℝ) < 0) :=
    (div_pos_iff).1 hab_pos

  -- Case analysis on signs
  cases hab_sign with
  | inl hab =>
      have ha_posZ : (0 : ℤ) < a := by exact_mod_cast hab.1
      have hb_posZ : (0 : ℤ) < b := by exact_mod_cast hab.2

      cases a with
      | ofNat an =>
          cases b with
          | ofNat bn =>
              have hbn_pos : 0 < bn := by
                simp only [Int.ofNat_eq_coe] at hb_posZ
                omega
              have hpow_nat : p ^ bn = q ^ an := by
                simp only [zpow_natCast] at hzpow_eq
                have h : ((p : ℕ) : ℝ) ^ bn = ((q : ℕ) : ℝ) ^ an := hzpow_eq
                exact_mod_cast h

              -- Contradiction via FTA
              have hmn := (prime_power_eq_iff hp hq hne bn an).1 hpow_nat
              exact (Nat.ne_of_gt hbn_pos) hmn.1
          | negSucc bn => exact (not_lt_of_gt hb_posZ) (by simp)
      | negSucc an => exact (not_lt_of_gt ha_posZ) (by simp)

  | inr hab =>
      have ha_negZ : a < 0 := by exact_mod_cast hab.1
      have hb_negZ : b < 0 := by exact_mod_cast hab.2

      -- a and b are negative integers, so they are negSucc form
      cases a with
      | ofNat n =>
          -- ofNat n ≥ 0, contradiction with a < 0
          simp only [Int.ofNat_eq_coe, Nat.cast_nonneg] at ha_negZ
          exact absurd (Nat.cast_nonneg (α := ℤ) n) (not_le.mpr ha_negZ)
      | negSucc an =>
          cases b with
          | ofNat n =>
              simp only [Int.ofNat_eq_coe, Nat.cast_nonneg] at hb_negZ
              exact absurd (Nat.cast_nonneg (α := ℤ) n) (not_le.mpr hb_negZ)
          | negSucc bn =>
              -- a = Int.negSucc an = -(an+1), b = Int.negSucc bn = -(bn+1)
              -- So -a = an+1, -b = bn+1
              let an' := an + 1
              let bn' := bn + 1
              have han : -(Int.negSucc an : ℤ) = (an' : ℤ) := by simp [Int.negSucc_eq, an']
              have hbn' : -(Int.negSucc bn : ℤ) = (bn' : ℤ) := by simp [Int.negSucc_eq, bn']
              have hbn_pos : 0 < bn' := Nat.succ_pos bn

              -- Invert equation: p^(-b) = q^(-a)
              have hzpow_eq' : pR ^ (-(Int.negSucc bn) : ℤ) = qR ^ (-(Int.negSucc an) : ℤ) := by
                rw [zpow_neg, zpow_neg, hzpow_eq]

              have hpow_nat : p ^ bn' = q ^ an' := by
                rw [han, hbn'] at hzpow_eq'
                simp only [zpow_natCast] at hzpow_eq'
                -- hzpow_eq' : pR ^ bn' = qR ^ an', i.e. (p:ℝ)^bn' = (q:ℝ)^an'
                have h : ((p : ℕ) : ℝ) ^ bn' = ((q : ℕ) : ℝ) ^ an' := hzpow_eq'
                exact_mod_cast h

              -- Contradiction via FTA
              have hmn := (prime_power_eq_iff hp hq hne bn' an').1 hpow_nat
              exact (Nat.ne_of_gt hbn_pos) hmn.1

/-!
## Lemma 3: Bounded Holomorphic Part Near a Pole
-/

/-- A function differentiable at a point is bounded in a neighborhood. -/
theorem differentiableAt_bounded_near {f : ℂ → ℂ} {z₀ : ℂ} (hf : DifferentiableAt ℂ f z₀) :
    ∃ δ > 0, ∃ M > 0, ∀ z, ‖z - z₀‖ < δ → ‖f z‖ ≤ M := by
  have hcont := hf.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  specialize hcont 1 one_pos
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hcont
  use δ, hδ_pos
  use ‖f z₀‖ + 1
  constructor
  · have := norm_nonneg (f z₀); linarith
  intro z hz
  have hdist : dist z z₀ < δ := hz
  have hball := hδ_ball hdist
  have hnorm_diff : ‖f z - f z₀‖ < 1 := hball
  calc ‖f z‖
      = ‖(f z - f z₀) + f z₀‖ := by simp only [sub_add_cancel]
    _ ≤ ‖f z - f z₀‖ + ‖f z₀‖ := norm_add_le _ _
    _ ≤ 1 + ‖f z₀‖ := by linarith
    _ = ‖f z₀‖ + 1 := by ring

/-- Bounded complex function has bounded real part. -/
theorem differentiableAt_re_bounded_near {f : ℂ → ℂ} {z₀ : ℂ} (hf : DifferentiableAt ℂ f z₀) :
    ∃ δ > 0, ∃ M > 0, ∀ z, ‖z - z₀‖ < δ → |(f z).re| ≤ M := by
  obtain ⟨δ, hδ_pos, M, hM_pos, hbound⟩ := differentiableAt_bounded_near hf
  use δ, hδ_pos, M, hM_pos
  intro z hz
  calc |(f z).re|
      ≤ ‖f z‖ := Complex.abs_re_le_norm (f z)
    _ ≤ M := hbound z hz

end NumberTheoryFTA
