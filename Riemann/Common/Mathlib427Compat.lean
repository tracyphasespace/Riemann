import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Real.Basic

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
This wrapper uses `prod_pos` for ordered semirings (like ℕ, ℝ) which implies non-zero.
-/
lemma finset_prod_ne_zero {α : Type*} [OrderedCommSemiring α] [Nontrivial α]
    (s : Finset α) (f : α → α) (h : ∀ x ∈ s, 0 < f x) :
    s.prod f ≠ 0 := by
  apply ne_of_gt
  exact Finset.prod_pos h

/--
**Fix for `Finset.card_le_one` pattern**
Helper to extract a pair from a set with card > 1.
Replaces manual `erase` logic.
-/
lemma exists_pair_of_card_gt_one {α : Type*} [DecidableEq α] (s : Finset α) (h : 1 < s.card) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y := by
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
    · exact (Finset.mem_erase.mp hy).1

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

end RiemannCompat
