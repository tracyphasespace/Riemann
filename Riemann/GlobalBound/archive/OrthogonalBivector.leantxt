import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Basic

noncomputable section
open Real Filter Topology BigOperators
open scoped BigOperators

namespace GlobalBound

/-!
# Phase 2: Orthogonal Prime Axes (Finite Support Model)

We model a finite prime-indexed orthogonal space by choosing a finite support `S : Finset ℕ`.
Vectors are real-valued coefficient functions on ℕ with coefficients forced to vanish off `S`.

## The "Orthogonality" Insight
Standard Analysis struggles because it projects the infinite-dimensional
prime phases onto a 1D line, creating "interference" (cross-terms).

In this Geometric Algebra formulation, we define the Primes as
**Orthogonal Generators** of the algebra:
- Prime p acts on dimension e_p.
- Prime q acts on dimension e_q.
- Inner product ⟨e_p, e_q⟩ = δ_pq.

This eliminates the "Noise" of interference. The stability becomes a
consequence of the Pythagorean Theorem: Sum of Squares > 0.
-/

/-- Geometric state vector with coefficients supported on `S`. -/
structure PrimeIndexedVec (S : Finset ℕ) where
  coeff : ℕ → ℝ
  h_support : ∀ p, p ∉ S → coeff p = 0

/-- Inner product on the finite support `S`: ⟪u,v⟫ = ∑_{p∈S} u_p v_p. -/
def innerProduct {S : Finset ℕ} (u v : PrimeIndexedVec S) : ℝ :=
  S.sum (fun p => u.coeff p * v.coeff p)

/-- Squared magnitude (mass/energy): ‖v‖² = ⟪v,v⟫. -/
def magSq {S : Finset ℕ} (v : PrimeIndexedVec S) : ℝ :=
  innerProduct v v

/-!
## Canonical orthogonal axes
-/

/-- Canonical basis vector e_p (Kronecker delta on `S`). -/
def axis (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) : PrimeIndexedVec S where
  coeff := fun q => if q = p then 1 else 0
  h_support := by
    intro q hq
    by_cases h : q = p
    · exact (hq (h ▸ hp)).elim
    · simp [h]

/-- Axes are orthogonal: ⟪e_p, e_q⟫ = 0 for p ≠ q. -/
theorem axes_are_orthogonal {S : Finset ℕ} (p q : ℕ)
    (hp : p ∈ S) (hq : q ∈ S) (hneq : p ≠ q) :
    innerProduct (axis S p hp) (axis S q hq) = 0 := by
  classical
  unfold innerProduct axis
  refine Finset.sum_eq_zero ?_
  intro x _hx
  by_cases hxP : x = p
  · simp only [hxP, ↓reduceIte, one_mul]
    have hxq : p ≠ q := hneq
    simp [hxq]
  · simp [hxP]

/-!
## Sieve vector and energy identity
-/

/-- Sieve vector: V(t)_p = sin(t log p) on S, 0 off S (forced by h_support). -/
def sieveVec (S : Finset ℕ) (t : ℝ) : PrimeIndexedVec S where
  coeff := fun p => if p ∈ S then Real.sin (t * Real.log (p : ℝ)) else 0
  h_support := by
    intro p hp
    simp [hp]

/-- Energy identity: ‖V(t)‖² = ∑_{p∈S} sin²(t log p). -/
theorem sieve_energy_is_sum_sq (S : Finset ℕ) (t : ℝ) :
    magSq (sieveVec S t) = S.sum (fun p => (Real.sin (t * Real.log (p : ℝ)))^2) := by
  classical
  unfold magSq innerProduct sieveVec
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp only [if_pos hp, pow_two]

/-!
## Stiffness positivity
-/

/-- If S is nonempty and consists of primes, then ∑ (log p)² > 0. -/
theorem stiffness_is_positive (S : Finset ℕ) (hS : S.Nonempty)
    (hpr : ∀ p ∈ S, Nat.Prime p) :
    0 < S.sum (fun p => (Real.log (p : ℝ))^2) := by
  classical
  have hpos : ∀ p ∈ S, 0 < (Real.log (p : ℝ))^2 := by
    intro p hp
    have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le (hpr p hp)
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    exact sq_pos_of_pos hlog
  exact Finset.sum_pos hpos hS

/-!
## Chirality: frequently, the energy is positive

We prove: for any T, there exists t ≥ T such that magSq(V(t)) > 0.
This is a clean deterministic "not identically zero" statement.

The proof picks one prime p ∈ S and chooses t_star = ((k+1/2)π)/log p so that
sin(t_star * log p) = ±1, hence the sum of squares is ≥ 1.
-/

/--
For nonempty prime support, `magSq (sieveVec S t)` is frequently positive as `t → ∞`.
-/
theorem chirality_is_guaranteed (S : Finset ℕ)
    (hS : S.Nonempty) (hpr : ∀ p ∈ S, Nat.Prime p) :
    ∃ᶠ t in atTop, magSq (sieveVec S t) > 0 := by
  classical
  rw [Filter.frequently_atTop]
  intro T
  obtain ⟨p, hpS⟩ := hS
  have hpPrime : Nat.Prime p := hpr p hpS

  -- w = log p > 0 (since p ≥ 2)
  let w : ℝ := Real.log (p : ℝ)
  have w_pos : 0 < w := by
    have hp2 : (2 : ℕ) ≤ p := Nat.Prime.two_le hpPrime
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    exact Real.log_pos hp1
  have w_ne : w ≠ 0 := ne_of_gt w_pos

  -- Choose integer k so that (T*w/π) < k
  let k : ℤ := ⌊T * w / Real.pi⌋ + 1
  have hk : T * w / Real.pi < (k : ℝ) := by
    have hx : (T * w / Real.pi) < (⌊T * w / Real.pi⌋ : ℝ) + 1 :=
      Int.lt_floor_add_one (T * w / Real.pi)
    convert hx using 1
    simp [k]

  -- Define t_star = ((k + 1/2)π)/w
  let t_star : ℝ := (((k : ℝ) + (1/2 : ℝ)) * Real.pi) / w

  refine ⟨t_star, ?_, ?_⟩

  · -- Show t_star ≥ T
    have pi_pos : 0 < (Real.pi : ℝ) := Real.pi_pos
    have hTw : T * w < (k : ℝ) * Real.pi := (div_lt_iff₀ pi_pos).1 hk
    have hT_lt : T < ((k : ℝ) * Real.pi) / w := (lt_div_iff₀ w_pos).2 hTw
    have hT_lt' : T < t_star := by
      have h1 : (k : ℝ) < (k : ℝ) + (1/2 : ℝ) := by linarith
      have h2 : (k : ℝ) * Real.pi < ((k : ℝ) + (1/2 : ℝ)) * Real.pi :=
        mul_lt_mul_of_pos_right h1 pi_pos
      have h3 : ((k : ℝ) * Real.pi) / w < (((k : ℝ) + (1/2 : ℝ)) * Real.pi) / w :=
        div_lt_div_of_pos_right h2 w_pos
      exact lt_trans hT_lt h3
    exact le_of_lt hT_lt'

  · -- Show magSq(sieveVec S t_star) > 0
    rw [sieve_energy_is_sum_sq]
    let f : ℕ → ℝ := fun x => (Real.sin (t_star * Real.log (x : ℝ)))^2

    have f_nonneg : ∀ x ∈ S, 0 ≤ f x := fun _ _ => sq_nonneg _
    have hterm_le : f p ≤ S.sum f := Finset.single_le_sum f_nonneg hpS

    -- Compute t_star * log p = ((k+1/2)π)
    have htstar_mul : t_star * w = ((k : ℝ) + (1/2 : ℝ)) * Real.pi := by
      simp only [t_star]
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self w_ne, mul_one]

    -- sin((k+1/2)π) = ±1, so sin² = 1 > 0
    have hsin_sq_pos : 0 < (Real.sin (((k : ℝ) + (1/2 : ℝ)) * Real.pi))^2 := by
      -- sin((k+1/2)π) = sin(kπ + π/2) = cos(kπ) = ±1
      have hsplit : ((k : ℝ) + (1/2 : ℝ)) * Real.pi = (k : ℝ) * Real.pi + Real.pi / 2 := by ring
      rw [hsplit, Real.sin_add, Real.sin_int_mul_pi, Real.cos_pi_div_two,
          Real.sin_pi_div_two, zero_mul, zero_add, mul_one]
      -- cos(kπ)² = ((-1)^k)² = 1 > 0
      rw [Real.cos_int_mul_pi]
      have : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
        have h1 : |(-1 : ℝ) ^ k| = 1 := by
          rw [abs_zpow]
          simp
        calc ((-1 : ℝ) ^ k) ^ 2 = |(-1 : ℝ) ^ k| ^ 2 := by rw [sq_abs]
          _ = 1 ^ 2 := by rw [h1]
          _ = 1 := by norm_num
      rw [this]
      exact one_pos

    have hterm_pos : 0 < f p := by
      simp only [f, w] at htstar_mul ⊢
      rw [htstar_mul]
      exact hsin_sq_pos

    exact lt_of_lt_of_le hterm_pos hterm_le

end GlobalBound
