import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Riemann.ProofEngine.DiophantineGeometry

/-!
# Job 1 Solved: Linear Independence of Log Primes
Agent: Swarm #001
Status: Framework Complete (connects to DiophantineGeometry.lean for FTA)

We prove: If ∑ z_i * log(p_i) = 0 for integers z_i, then all z_i = 0.
Key Tool: `Nat.factors_unique` (The Fundamental Theorem of Arithmetic).

## Relationship to DiophantineGeometry.lean

The core FTA theorem `fta_all_exponents_zero` is proven in DiophantineGeometry.lean.
This file provides the wrapper to expose it as `LinearIndependent ℚ (log primes)`.
-/

noncomputable section
open Real BigOperators Finsupp

namespace LinearIndependenceSolved

/-!
## Core Result: Import from DiophantineGeometry

The heavy lifting is done in `OutstandingProofs.fta_all_exponents_zero`.
Here we establish the bridge to `LinearIndependent ℚ`.
-/

/-- Helper: Clear denominators from rational coefficients -/
lemma clear_denominators (s : Finset {x : ℕ // x.Prime}) (g : {x : ℕ // x.Prime} → ℚ)
    (_h_sum : ∑ p ∈ s, g p * Real.log (p : ℕ) = 0) :
    ∃ D : ℕ, 0 < D ∧ ∀ p ∈ s, ∃ z : ℤ, (g p * D : ℚ) = z := by
  -- KEY LEMMA: Rat.mul_den_eq_num : q * q.den = q.num
  -- Strategy: D = ∏ denominators, then g p * D = g p * (den * k) = num * k
  use s.prod (fun p => (g p).den)
  constructor
  · apply Finset.prod_pos
    intro p _
    exact (g p).den_pos
  · intro p hp
    have h_dvd : (g p).den ∣ s.prod (fun q => (g q).den) := Finset.dvd_prod_of_mem _ hp
    obtain ⟨k, hk⟩ := h_dvd
    use (g p).num * k
    rw [hk]; push_cast; rw [← mul_assoc, Rat.mul_den_eq_num]

/--
**Main Theorem**: Logs of distinct primes are linearly independent over ℚ.
This follows from the FTA: If ∑ (a_i/b_i) * log(p_i) = 0, then clearing
denominators gives ∑ z_i * log(p_i) = 0 for integers z_i, which by FTA
implies all z_i = 0.
-/
theorem log_primes_linear_independent :
    LinearIndependent ℚ (fun (p : {x : ℕ // x.Prime}) => Real.log (p : ℕ)) := by
  -- Use linearIndependent_iff' to reduce to: ∑ g(p) • log(p) = 0 → g = 0
  rw [linearIndependent_iff']
  intro s g h_sum p hp
  -- Convert smul to multiplication: g(p) • log(p) = (g(p) : ℝ) * log(p)
  simp only [Rat.smul_def] at h_sum
  -- Handle empty set case
  by_cases hs : s = ∅
  · simp [hs] at hp
  -- Use clear_denominators to get D > 0 and integer values
  obtain ⟨D, hD_pos, hD_int⟩ := clear_denominators s g h_sum
  -- Construct integer-valued function z
  -- For p ∈ s, z(p) = g(p) * D (which is an integer by hD_int)
  -- Use Classical.choose to extract the integer
  have h_z_exists : ∀ q ∈ s, ∃ z : ℤ, (g q * D : ℚ) = z := hD_int
  let z : {x : ℕ // x.Prime} → ℤ := fun q =>
    if hq : q ∈ s then Classical.choose (h_z_exists q hq) else 0
  -- z(q) = g(q) * D for q ∈ s
  have hz_eq : ∀ q ∈ s, (g q * D : ℚ) = z q := fun q hq => by
    simp only [z, dif_pos hq]
    exact Classical.choose_spec (h_z_exists q hq)
  -- Multiply the original sum by D: ∑ (g p * D : ℝ) * log p = 0
  have h_scaled : ∑ q ∈ s, ((g q * D : ℚ) : ℝ) * Real.log (q : ℕ) = 0 := by
    have : (D : ℝ) ≠ 0 := by positivity
    calc ∑ q ∈ s, ((g q * D : ℚ) : ℝ) * Real.log (q : ℕ)
        = ∑ q ∈ s, (((g q : ℝ) * D) * Real.log (q : ℕ)) := by simp [Rat.cast_mul]
      _ = ∑ q ∈ s, ((g q : ℝ) * Real.log (q : ℕ)) * D := by
          congr 1; ext q; ring
      _ = (∑ q ∈ s, (g q : ℝ) * Real.log (q : ℕ)) * D := by rw [Finset.sum_mul]
      _ = 0 * D := by rw [h_sum]
      _ = 0 := zero_mul _
  -- Convert to integer sum: ∑ (z q : ℝ) * log q = 0
  have h_int_sum : ∑ q ∈ s, (z q : ℝ) * Real.log (q : ℕ) = 0 := by
    convert h_scaled using 2 with q hq
    -- hz_eq: (g q * D : ℚ) = (z q : ℚ), need to show (z q : ℝ) = ((g q * D : ℚ) : ℝ)
    have heq : (z q : ℚ) = g q * D := (hz_eq q hq).symm
    have heq_real : (z q : ℝ) = ((g q : ℝ) * D) := by
      calc (z q : ℝ) = ((z q : ℚ) : ℝ) := by simp
        _ = ((g q * D : ℚ) : ℝ) := by rw [heq]
        _ = (g q : ℝ) * D := by simp [Rat.cast_mul]
    rw [heq_real]
    simp only [Rat.cast_mul, Rat.cast_natCast]
  -- Apply FTA: z(p) = 0 for all p ∈ s
  have h_fta := OutstandingProofs.fta_all_exponents_zero s z h_int_sum
  -- z(p) = 0, so g(p) * D = 0, so g(p) = 0 (since D > 0)
  have hz_p : z p = 0 := h_fta p hp
  have hgD : (g p * D : ℚ) = 0 := by
    rw [hz_eq p hp, hz_p, Int.cast_zero]
  have hD_ne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hD_pos)
  exact mul_eq_zero.mp hgD |>.resolve_right hD_ne

/-!
## Corollary: Phase Space is Infinite Torus

The linear independence of log primes implies that the phases
θ_p = t * log(p) mod 2π form an infinite-dimensional torus T^∞.
No rational relation can collapse this structure.
-/

/-- The phase map is injective modulo 2π on any finite prime set -/
theorem phase_space_is_torus (S : Finset {x : ℕ // x.Prime}) :
    ∀ t₁ t₂ : ℝ, (∀ p ∈ S, ∃ k : ℤ, t₁ * Real.log p - t₂ * Real.log p = 2 * π * k) →
    ∃ k : ℤ, t₁ - t₂ = 2 * π * k ∨ S.card ≤ 1 := by
  intro t₁ t₂ h_phases
  by_cases h_card : S.card ≤ 1
  · -- Easy case: |S| ≤ 1
    exact ⟨0, Or.inr h_card⟩
  · -- Hard case: |S| > 1, need to show (t₁ - t₂) is 2π-multiple
    push_neg at h_card
    -- We assume t₁ ≠ t₂ and derive contradiction or result
    by_cases h_eq : t₁ = t₂
    · use 0; left; simp [h_eq]

    -- Extract two distinct primes p1, p2 from S
    have h_card_pos : 0 < S.card := by linarith
    obtain ⟨p1, hp1⟩ := Finset.card_pos.mp h_card_pos
    let S' := S.erase p1
    have h_card_S' : 0 < S'.card := by
      rw [Finset.card_erase_of_mem hp1]
      omega
    obtain ⟨p2, hp2_mem_S'⟩ := Finset.card_pos.mp h_card_S'
    have hp2 : p2 ∈ S := Finset.mem_of_mem_erase hp2_mem_S'
    have p1_ne_p2 : p1 ≠ p2 := (Finset.mem_erase.mp hp2_mem_S').1.symm

    -- Get integer witnesses for p1 and p2
    obtain ⟨k1, hk1⟩ := h_phases p1 hp1
    obtain ⟨k2, hk2⟩ := h_phases p2 hp2
    -- Rewrite equations: (t1 - t2) * log p = 2π * k
    have eq1 : (t₁ - t₂) * Real.log p1 = 2 * π * k1 := by linear_combination hk1
    have eq2 : (t₁ - t₂) * Real.log p2 = 2 * π * k2 := by linear_combination hk2

    -- Cross-multiply to eliminate (t1 - t2) and 2π
    -- k2 * eq1: k2 * (t1 - t2) * log p1 = k2 * 2π * k1
    -- k1 * eq2: k1 * (t1 - t2) * log p2 = k1 * 2π * k2
    -- RHS are equal: 2π * k1 * k2
    have h_cross : (t₁ - t₂) * (k2 * Real.log p1 - k1 * Real.log p2) = 0 := by
      calc (t₁ - t₂) * (k2 * Real.log p1 - k1 * Real.log p2)
          = k2 * ((t₁ - t₂) * Real.log p1) - k1 * ((t₁ - t₂) * Real.log p2) := by ring
        _ = k2 * (2 * π * k1) - k1 * (2 * π * k2) := by rw [eq1, eq2]
        _ = 0 := by ring

    -- Since t1 ≠ t2, the log combination must be zero
    have h_log_comb : (k2 : ℝ) * Real.log p1 + (-k1 : ℝ) * Real.log p2 = 0 := by
      have h_diff_ne_zero : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h_eq
      have h_zero := mul_eq_zero.mp h_cross
      cases h_zero with
      | inl h => contradiction
      | inr h =>
        rw [sub_eq_add_neg] at h
        convert h using 2
        ring

    -- Apply Linear Independence to {p1, p2}
    let s_pair : Finset {x : ℕ // x.Prime} := {p1, p2}
    let g : {x : ℕ // x.Prime} → ℚ := fun p =>
      if p = p1 then (k2 : ℚ)
      else if p = p2 then (-k1 : ℚ)
      else 0

    -- First show what g evaluates to at p1 and p2
    have hg_p1 : g p1 = (k2 : ℚ) := by simp only [g, if_pos rfl]
    have hg_p2 : g p2 = (-k1 : ℚ) := by
      simp only [g, if_neg (Ne.symm p1_ne_p2), ite_true]

    have h_pair_sum : ∑ p ∈ s_pair, g p * Real.log p = 0 := by
      simp only [s_pair, Finset.sum_pair p1_ne_p2]
      rw [hg_p1, hg_p2]
      -- Now have: k2 * log p1 + (-k1) * log p2 = 0
      push_cast
      linarith [h_log_comb]

    -- Apply the main theorem
    have h_indep := linearIndependent_iff'.mp log_primes_linear_independent s_pair g h_pair_sum

    -- Deduce coefficients are zero
    -- h_indep gives g p = 0, need to unfold g definition
    have hk2_zero : (k2 : ℚ) = 0 := by
      have h := h_indep p1 (Finset.mem_insert_self p1 {p2})
      simp only [g, if_pos rfl] at h
      exact h
    have hk1_zero : (-k1 : ℚ) = 0 := by
      have hp2_in : p2 ∈ s_pair := Finset.mem_insert_of_mem (Finset.mem_singleton_self p2)
      have h := h_indep p2 hp2_in
      simp only [g, if_neg (Ne.symm p1_ne_p2), ite_true] at h
      exact h

    -- Propagate back to k1 = 0
    have k1_is_zero : k1 = 0 := by
      rw [neg_eq_zero] at hk1_zero
      exact Int.cast_eq_zero.mp hk1_zero

    -- Substitute k1=0 into eq1: (t1 - t2) * log p1 = 0
    rw [k1_is_zero, Int.cast_zero, mul_zero] at eq1

    -- Since p1 is prime, log p1 ≠ 0
    have h_log_ne : Real.log p1 ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one
      -- p1 is prime -> p1 >= 2 -> p1 > 0
      · have : 1 < p1.val := Nat.Prime.one_lt p1.prop
        positivity
      -- p1 is prime -> p1 >= 2 -> p1 ≠ 1
      · have : 1 < p1.val := Nat.Prime.one_lt p1.prop
        norm_cast
        linarith

    have h_final : t₁ - t₂ = 0 := mul_eq_zero.mp eq1 |>.resolve_right h_log_ne
    use 0
    left
    simp only [Int.cast_zero, mul_zero]
    exact h_final

end LinearIndependenceSolved
