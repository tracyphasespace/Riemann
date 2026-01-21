import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential

noncomputable section
open Real BigOperators Complex

namespace ChiralPath

/-!
# Job 2: The Polygon Inequality (Geometry)

This proof establishes the "Geometric Non-Closure" condition.
If the vectors in the sum ∑ c_p * exp(i * θ_p) form a "Polygon",
and one edge is longer than the sum of all other edges, the polygon
cannot close (sum cannot be zero).

This is a direct application of the Reverse Triangle Inequality.
-/

/--
The magnitude of the Zeta derivative coefficient for prime p at sigma.
|c_p| = |log p / p^σ|
-/
def deriv_coeff_mag (σ : ℝ) (p : ℕ) : ℝ :=
  (Real.log p) / (p : ℝ) ^ σ

/--
The vector term for prime p at time t.
v_p(t) = - (log p / p^σ) * exp(i * t * log p)
Note: We drop the negative sign for magnitude checks as it doesn't affect norm.
-/
def zeta_vec (σ : ℝ) (p : ℕ) (t : ℝ) : ℂ :=
  (deriv_coeff_mag σ p) * cexp (t * Real.log p * I)

/-!
## Helper Lemmas for Norm Calculations
-/

/-- The norm of exp(i*θ) is 1 -/
lemma norm_cexp_pure_imaginary (θ : ℝ) : ‖cexp (θ * I)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Log of natural number ≥ 2 is nonnegative -/
lemma log_nat_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ Real.log n := by
  apply Real.log_nonneg
  have : 1 ≤ n := Nat.one_le_of_lt (Nat.one_lt_two.trans_le hn)
  norm_cast

/-- deriv_coeff_mag is nonnegative for primes -/
lemma deriv_coeff_mag_nonneg (σ : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ deriv_coeff_mag σ p := by
  unfold deriv_coeff_mag
  apply div_nonneg
  · exact log_nat_nonneg hp.two_le
  · apply rpow_nonneg
    exact Nat.cast_nonneg p

/-- The norm of zeta_vec equals deriv_coeff_mag for primes -/
lemma norm_zeta_vec (σ : ℝ) {p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    ‖zeta_vec σ p t‖ = deriv_coeff_mag σ p := by
  unfold zeta_vec
  rw [norm_mul]
  -- ‖cexp(t * log p * I)‖ = 1
  have h_exp_norm : ‖cexp (t * Real.log p * I)‖ = 1 := by
    -- Rewrite to get the form (r : ℂ) * I where r : ℝ
    have : (t : ℂ) * (Real.log p : ℂ) * I = ((t * Real.log p : ℝ) : ℂ) * I := by
      simp only [ofReal_mul]
    rw [this]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h_exp_norm, mul_one]
  -- ‖(deriv_coeff_mag σ p : ℂ)‖ = deriv_coeff_mag σ p
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (deriv_coeff_mag_nonneg σ hp)]

/-!
## The Main Theorem
-/

/--
**The Polygon Inequality Theorem**
If there exists a "Dominant Prime" p_dom whose coefficient magnitude
exceeds the sum of all other coefficients, then the total sum is strictly non-zero
for ALL time t.

This is a direct application of the Reverse Triangle Inequality:
‖A + B‖ ≥ |‖A‖ - ‖B‖|

When ‖A‖ > ‖B‖, this gives ‖A + B‖ ≥ ‖A‖ - ‖B‖ > 0.
-/
theorem no_geometric_closure_of_dominant
    (σ : ℝ) (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (p_dom : ℕ) (h_mem : p_dom ∈ S)
    (h_dominant : deriv_coeff_mag σ p_dom > ∑ p ∈ S.erase p_dom, deriv_coeff_mag σ p) :
    ∀ t, ‖∑ p ∈ S, zeta_vec σ p t‖ > 0 := by

  intro t

  -- 1. Split the sum into the Dominant term and the Tail
  have h_split : ∑ p ∈ S, zeta_vec σ p t =
      zeta_vec σ p_dom t + ∑ p ∈ S.erase p_dom, zeta_vec σ p t := by
    symm
    exact Finset.add_sum_erase S (fun p => zeta_vec σ p t) h_mem

  -- 2. Apply Reverse Triangle Inequality: ‖A + B‖ ≥ ‖A‖ - ‖B‖
  have h_rev_tri : ‖∑ p ∈ S, zeta_vec σ p t‖ ≥
      ‖zeta_vec σ p_dom t‖ - ‖∑ p ∈ S.erase p_dom, zeta_vec σ p t‖ := by
    rw [h_split]
    -- Use: ‖a + b‖ ≥ |‖a‖ - ‖b‖| ≥ ‖a‖ - ‖b‖
    have := norm_sub_norm_le (zeta_vec σ p_dom t) (-(∑ p ∈ S.erase p_dom, zeta_vec σ p t))
    simp only [norm_neg, sub_neg_eq_add] at this
    linarith [abs_nonneg (‖zeta_vec σ p_dom t‖ - ‖∑ p ∈ S.erase p_dom, zeta_vec σ p t‖)]

  -- 3. The dominant term's norm equals its coefficient magnitude
  have h_norm_dom : ‖zeta_vec σ p_dom t‖ = deriv_coeff_mag σ p_dom := by
    exact norm_zeta_vec σ (hS p_dom h_mem) t

  -- 4. Bound the Tail using Triangle Inequality: ‖∑ v_i‖ ≤ ∑ ‖v_i‖
  have h_norm_tail : ‖∑ p ∈ S.erase p_dom, zeta_vec σ p t‖ ≤
      ∑ p ∈ S.erase p_dom, deriv_coeff_mag σ p := by
    calc ‖∑ p ∈ S.erase p_dom, zeta_vec σ p t‖
      _ ≤ ∑ p ∈ S.erase p_dom, ‖zeta_vec σ p t‖ := norm_sum_le _ _
      _ = ∑ p ∈ S.erase p_dom, deriv_coeff_mag σ p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp_prime : Nat.Prime p := hS p (Finset.mem_of_mem_erase hp)
        exact norm_zeta_vec σ hp_prime t

  -- 5. Combine: ‖Total‖ ≥ ‖Dom‖ - ‖Tail‖ > 0
  have h_pos : deriv_coeff_mag σ p_dom - ∑ p ∈ S.erase p_dom, deriv_coeff_mag σ p > 0 :=
    sub_pos.mpr h_dominant

  calc ‖∑ p ∈ S, zeta_vec σ p t‖
      _ ≥ ‖zeta_vec σ p_dom t‖ - ‖∑ p ∈ S.erase p_dom, zeta_vec σ p t‖ := h_rev_tri
      _ = deriv_coeff_mag σ p_dom - ‖∑ p ∈ S.erase p_dom, zeta_vec σ p t‖ := by rw [h_norm_dom]
      _ ≥ deriv_coeff_mag σ p_dom - ∑ p ∈ S.erase p_dom, deriv_coeff_mag σ p := by
          linarith [h_norm_tail]
      _ > 0 := h_pos

/-!
## Analysis

**What this proves:** If one prime's coefficient dominates the sum of all others,
the derivative sum can NEVER be zero, regardless of the phases.

**The Catch:** For the full Zeta function, the "Tail" (sum over all primes > p_dom)
diverges, so h_dominant eventually fails for large truncations.

**Why this leads to Job 3:** Since geometry alone cannot prove non-vanishing
for the infinite series, we must use Baker's Theorem to show that the
constrained phases θ_p = t·log(p) can never conspire to hit zero.
-/

end ChiralPath
