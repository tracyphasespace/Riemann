import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

/-!
# Mathlib 4.27 Compatibility Shim

This file collects local implementations of lemmas that are either:
1.  Renamed/Moved in Mathlib 4.27 (vs older versions).
2.  Missing from the specific 4.27 imports used.
3.  Common helper patterns for type casting (ℕ ↔ ℤ ↔ ℚ ↔ ℝ).

## Usage
Import this file in your proof headers:
`import Riemann.Common.Mathlib427Compat`
-/

namespace RiemannCompat

open BigOperators

section FinsetLemmas

/--
**Fix for `Finset.prod_ne_zero`**
In Mathlib 4.27, `prod_ne_zero` is often not found directly in basic imports.
This wrapper uses `prod_pos` for types with PosMulStrictMono.
-/
lemma finset_prod_ne_zero {α ι : Type*} [CommMonoidWithZero α] [PartialOrder α]
    [ZeroLEOneClass α] [PosMulStrictMono α] [Nontrivial α]
    (s : Finset ι) (f : ι → α) (h : ∀ x ∈ s, 0 < f x) :
    s.prod f ≠ 0 := by
  apply ne_of_gt
  exact Finset.prod_pos h

/--
**Fix for `Finset.card_le_one` pattern**
Helper to extract a pair from a set with card > 1.
Replaces manual `erase` logic.
-/
lemma exists_pair_of_card_gt_one {α : Type*} (s : Finset α) (h : 1 < s.card) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
  classical
  have h_nonempty : s.Nonempty := by
    rw [← Finset.card_pos]
    linarith
  obtain ⟨x, hx⟩ := h_nonempty
  have h_card_erase : 0 < (s.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp h_card_erase
  use x, y
  constructor
  · exact hx
  · constructor
    · exact Finset.mem_of_mem_erase hy
    · exact (Finset.mem_erase.mp hy).1.symm

end FinsetLemmas

section RatLemmas

/--
**Fix for `Rat.mul_den_eq_num`**
The exact name varies by version. This provides the algebraic identity
`q * q.den = q.num` in ℚ.
-/
lemma rat_mul_denom_eq_num (q : ℚ) : q * (q.den : ℚ) = (q.num : ℚ) := by
  rw [Rat.mul_den_eq_num] -- Try standard name first
  -- Fallback if the standard name fails or simplifies differently
  try simp only [Rat.mul_den_eq_num]

/--
**Fix for `Rat.smul_def` mismatch**
Explicitly connects scalar multiplication to standard multiplication
for Rationals to Reals.
-/
lemma rat_smul_eq_mul (q : ℚ) (r : ℝ) : q • r = (q : ℝ) * r := by
  rfl

end RatLemmas

section CastHelpers

/--
**Auto-caster for ℕ → ℝ equalities**
Reduces the manual `norm_cast`, `inj`, `push_cast` cycle.
Usage: `apply nat_to_real_eq`
-/
lemma nat_to_real_eq {a b : ℕ} (h : (a : ℝ) = (b : ℝ)) : a = b := by
  exact Nat.cast_injective h

/--
**Auto-caster for ℤ → ℚ → ℝ chain**
Useful when proving `z • log p = 0` implies `z = 0`.
-/
lemma int_cast_real_eq_zero {z : ℤ} (h : (z : ℝ) = 0) : z = 0 := by
  have h_rat : (z : ℚ) = 0 := by
    exact_mod_cast h
  exact_mod_cast h_rat

end CastHelpers

section AsymptoticLemmas

open Filter Asymptotics Real

/--
**Asymptotic Ratio Divergence**

If `f = O(g^α)` with `α < 1`, and `g → ∞` with `g > 0` eventually,
then `g / |f| → ∞` (requires `f ≠ 0` eventually).

This is the key lemma for SNR divergence proofs: when noise grows
slower than signal, the signal-to-noise ratio diverges.
-/
theorem isBigO_ratio_divergence {α : ℝ} (hα : α < 1)
    {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (h_bound : IsBigO l f (fun i => (g i) ^ α))
    (h_g_pos : ∀ᶠ i in l, 0 < g i)
    (h_f_ne0 : ∀ᶠ i in l, f i ≠ 0)
    (h_g_lim : Tendsto g l atTop) :
    Tendsto (fun i => g i / |f i|) l atTop := by
  -- Step 1: Extract constant C > 0 from IsBigO
  rw [isBigO_iff] at h_bound
  obtain ⟨C, hC⟩ := h_bound
  -- hC : ∀ᶠ i in l, ‖f i‖ ≤ C * ‖g i ^ α‖
  -- Step 2: Get C' > 0 to avoid division issues
  set C' := max C 1 with hC'_def
  have hC'_pos : 0 < C' := lt_max_of_lt_right one_pos
  -- Step 3: Eventually we have the key inequality
  have h_ineq : ∀ᶠ i in l, C'⁻¹ * (g i) ^ (1 - α) ≤ g i / |f i| := by
    filter_upwards [hC, h_g_pos, h_f_ne0, h_g_lim.eventually_ge_atTop 1] with i hCi hgi hfi hgi_ge1
    -- For g i ≥ 1 > 0, we have |g i ^ α| = g i ^ α
    have h_gpow_eq : ‖(g i) ^ α‖ = (g i) ^ α := by
      rw [Real.norm_eq_abs]
      rw [abs_rpow_of_nonneg (le_of_lt hgi)]
      rw [abs_of_pos hgi]
    -- Also |f i| ≤ C * g i ^ α ≤ C' * g i ^ α
    have h_fi_bound : |f i| ≤ C' * (g i) ^ α := by
      calc |f i| = ‖f i‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖(g i) ^ α‖ := hCi
        _ = C * (g i) ^ α := by rw [h_gpow_eq]
        _ ≤ C' * (g i) ^ α := by apply mul_le_mul_of_nonneg_right (le_max_left _ _)
                                  (rpow_nonneg (le_of_lt hgi) _)
    -- Since f i ≠ 0, we have |f i| > 0
    have h_fi_pos : 0 < |f i| := abs_pos.mpr hfi
    have h_gpow_pos : 0 < (g i) ^ α := rpow_pos_of_pos hgi α
    calc C'⁻¹ * (g i) ^ (1 - α)
        = C'⁻¹ * ((g i) ^ (1 : ℝ) * (g i) ^ (-α)) := by
          rw [← rpow_add hgi]
          ring_nf
        _ = C'⁻¹ * (g i * (g i) ^ (-α)) := by
          rw [rpow_one]
        _ = C'⁻¹ * (g i / (g i) ^ α) := by
          rw [rpow_neg (le_of_lt hgi), div_eq_mul_inv]
        _ = g i / (C' * (g i) ^ α) := by
          field_simp
        _ ≤ g i / |f i| := by
          apply div_le_div_of_nonneg_left (le_of_lt hgi) h_fi_pos h_fi_bound
  -- Step 4: Show C'⁻¹ * g^(1-α) → +∞
  have h_base_div : Tendsto (fun i => C'⁻¹ * (g i) ^ (1 - α)) l atTop := by
    have h_exp_pos : 0 < 1 - α := by linarith
    have h_rpow_lim : Tendsto (fun i => (g i) ^ (1 - α)) l atTop := by
      -- Use composition: (x^b) ∘ g where x^b → ∞ and g → ∞
      exact (tendsto_rpow_atTop h_exp_pos).comp h_g_lim
    exact Tendsto.const_mul_atTop (inv_pos.mpr hC'_pos) h_rpow_lim
  -- Step 5: Conclude by monotonicity
  exact tendsto_atTop_mono' l h_ineq h_base_div

end AsymptoticLemmas

end RiemannCompat
