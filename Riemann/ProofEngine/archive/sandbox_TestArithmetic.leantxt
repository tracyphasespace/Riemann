import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

example (p n : ℕ) (hp : p.Prime) : log (p ^ n : ℝ) = n * log p := by
  rw [Nat.cast_pow, log_pow]

example (p : ℕ) (hp : p.Prime) : p ^ 0 = 1 := by simp

example (p n : ℕ) (hp : p.Prime) (h : p ^ n = 1) : n = 0 := by
  exact (Nat.pow_eq_one_iff (Nat.Prime.pos hp)).mp h |>.resolve_left (Nat.Prime.ne_one hp)

example (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p ∣ q) : p = q := by
  exact (Nat.Prime.dvd_iff hq).mp h |>.resolve_left (Nat.Prime.ne_one hp)
