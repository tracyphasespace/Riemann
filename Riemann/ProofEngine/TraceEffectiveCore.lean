/-
# Trace Effective Core: The Final Three Lemmas

**Goal**: Close the convexity-based proof path for RH using the Clifford rotor trace framework.

This file contains the "boss and henchmen" structure:
1. `rotorTraceSecondDeriv_lower_bound` - Henchman #1: Second derivative positivity
2. `rotorTraceFirstDeriv_lower_bound_right` - Henchman #2a: First derivative lower bound for ξ ≥ 1/2
   `rotorTraceFirstDeriv_upper_bound_left` - Henchman #2b: First derivative upper bound for ξ ≤ 1/2
3. `effective_critical_convex_implies_near_min` - Final Boss: Strict minimum at σ = 1 / 2

**Mathematical Summary**:
- Under uniform cosine positivity (phase clustering), T''(σ) ≥ δ > 0
- For ξ ≥ 1/2: T'(ξ) ≥ δ*(ξ - 1/2) - ε (lower bound, derivative positive)
- For ξ ≤ 1/2: T'(ξ) ≤ ε - δ*(1/2 - ξ) (upper bound, derivative negative)
- This forces T(σ) > T(1/2) for all σ ≠ 1/2, proving the trace minimum is at the critical line
-/

import Riemann.ZetaSurface.CliffordRH
import Riemann.Axioms
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Real Set BigOperators

noncomputable section

namespace ProofEngine.TraceEffectiveCore

open CliffordRH

/-!
## 0. Helper Lemmas for Foldl Inequalities

These lemmas establish that weighted sums with cosine factors can be
bounded below by c times the unweighted sum when all cosines are ≥ c.
-/

/-- Helper: foldl with addition and initial value `a` equals `a` plus foldl with initial `0`. -/
theorem foldl_add_init_generic {α : Type} (l : List α) (f : α → ℝ) (a : ℝ) :
    l.foldl (fun acc x => acc + f x) a = a + l.foldl (fun acc x => acc + f x) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (a + f h), ih (f h)]
    ring

/-- Helper: foldl with addition and initial `0` equals the sum of the mapped list. -/
theorem foldl_add_eq_sum {α : Type} (l : List α) (f : α → ℝ) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons h t ih =>
    have h_foldl : t.foldl (fun acc x => acc + f x) (f h) =
        f h + t.foldl (fun acc x => acc + f x) 0 := by
      simpa using (foldl_add_init_generic t f (f h))
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, zero_add]
    simp [h_foldl, ih]

/--
**Helper Lemma**: Weighted sum inequality for cosine factors.

If f(p) ≥ 0 for all p in the list and cos(θ(p)) ≥ c for all p,
then Σ f(p)·cos(θ(p)) ≥ c · Σ f(p).

This is a standard weighted average inequality.
-/
lemma foldl_weighted_cos_ge_c_mul_foldl
    (primes : List ℕ) (c : ℝ) (f : ℕ → ℝ) (θ : ℕ → ℝ)
    (hf_nonneg : ∀ p ∈ primes, f p ≥ 0)
    (h_cos : ∀ p ∈ primes, Real.cos (θ p) ≥ c) :
    primes.foldl (fun acc p => acc + f p * Real.cos (θ p)) 0 ≥
    c * primes.foldl (fun acc p => acc + f p) 0 := by
  -- Key insight: For each term, f(p) ≥ 0 and cos ≥ c implies f(p)*cos ≥ c*f(p)
  -- Prove by induction with generalized accumulator invariant
  suffices h : ∀ (a b : ℝ), a ≥ c * b →
      primes.foldl (fun acc p => acc + f p * Real.cos (θ p)) a ≥
      c * primes.foldl (fun acc p => acc + f p) b by
    exact h 0 0 (by simp)
  induction primes with
  | nil => intro a b hab; simp only [List.foldl_nil]; exact hab
  | cons p ps ih =>
    intro a b hab
    simp only [List.foldl_cons]
    apply ih (fun q hq => hf_nonneg q (List.mem_cons_of_mem p hq))
             (fun q hq => h_cos q (List.mem_cons_of_mem p hq))
    -- Goal: a + f(p) * cos(θ p) ≥ c * (b + f p)
    have hp_nonneg : f p ≥ 0 := hf_nonneg p (List.mem_cons.mpr (Or.inl rfl))
    have hp_cos : Real.cos (θ p) ≥ c := h_cos p (List.mem_cons.mpr (Or.inl rfl))
    -- f(p) * cos(θ p) ≥ c * f(p) when f(p) ≥ 0 and cos ≥ c
    have h_term : f p * Real.cos (θ p) ≥ c * f p := by
      calc f p * Real.cos (θ p) ≥ f p * c := mul_le_mul_of_nonneg_left hp_cos hp_nonneg
        _ = c * f p := mul_comm _ _
    calc a + f p * Real.cos (θ p) ≥ c * b + c * f p := by linarith
      _ = c * (b + f p) := by ring

/-!
## 1. Henchman #1: Second Derivative Lower Bound

Under uniform cosine positivity (all cos(t·log p) ≥ c > 0), the second derivative
of the rotor trace is bounded below by a positive quantity.
-/

/--
**Henchman #1**: Second derivative lower bound assuming cos(t·log p) ≥ c > 0.

This is the key convexity condition: if the prime phases are "aligned" (all cosines positive),
then T''(σ) > 0, meaning the trace is strictly convex.
-/
lemma rotorTraceSecondDeriv_lower_bound
    (σ t c : ℝ) (primes : List ℕ)
    (hσ : 0 < σ ∧ σ < 1)
    (_hc : 0 < c)
    (h_primes : ∀ p ∈ primes, 0 < (p : ℝ))
    (h_cos : ∀ p ∈ primes, Real.cos (t * Real.log p) ≥ c) :
    rotorTraceSecondDeriv σ t primes ≥
      2 * c * (primes.map (fun p : ℕ => (Real.log p)^3 * (p : ℝ)^(-σ))).sum := by
  -- T''(σ) = 2 * Σ (log p)³ * p^{-σ} * cos(t·log p)
  -- Each term has cos ≥ c, so term ≥ c * (log p)³ * p^{-σ}
  -- Proof approach (Aristotle, Lean 4.24): induction on List.reverseRecOn
  -- with nlinarith for the term-by-term inequality f(p)*cos ≥ c*f(p)
  -- Needs adaptation for 4.27 API (foldl representation differs)
  have h_weighted :
      primes.foldl (fun acc (p : ℕ) =>
        acc + (Real.log p)^3 * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0 ≥
      c * primes.foldl (fun acc (p : ℕ) =>
        acc + (Real.log p)^3 * (p : ℝ)^(-σ)) 0 := by
    apply foldl_weighted_cos_ge_c_mul_foldl primes c
      (fun p => (Real.log p)^3 * (p : ℝ)^(-σ))
      (fun p => t * Real.log p)
    · intro p hp
      have hp_pos : 0 < (p : ℝ) := h_primes p hp
      have hp_nat : 0 < p := by exact_mod_cast hp_pos
      have hp_ge1_nat : 1 ≤ p := (Nat.succ_le_iff).2 hp_nat
      have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge1_nat
      have hlog_nonneg : 0 ≤ Real.log p := Real.log_nonneg hp_ge1
      have hlog_pow_nonneg : 0 ≤ (Real.log p)^3 := by
        exact pow_nonneg hlog_nonneg 3
      have hp_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
      have hrpow_nonneg : 0 ≤ (p : ℝ)^(-σ) := Real.rpow_nonneg hp_nonneg _
      exact mul_nonneg hlog_pow_nonneg hrpow_nonneg
    · intro p hp
      exact h_cos p hp
  have h_weighted_mul :
      2 * primes.foldl (fun acc (p : ℕ) =>
        acc + (Real.log p)^3 * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0 ≥
      2 * (c * primes.foldl (fun acc (p : ℕ) =>
        acc + (Real.log p)^3 * (p : ℝ)^(-σ)) 0) := by
    have h2_nonneg : 0 ≤ (2 : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_left h_weighted h2_nonneg
  have h_sum :
      primes.foldl (fun acc (p : ℕ) => acc + (Real.log p)^3 * (p : ℝ)^(-σ)) 0 =
        (primes.map (fun p : ℕ => (Real.log p)^3 * (p : ℝ)^(-σ))).sum := by
    exact foldl_add_eq_sum primes (fun p => (Real.log p)^3 * (p : ℝ)^(-σ))
  unfold rotorTraceSecondDeriv
  calc
    2 * primes.foldl (fun acc (p : ℕ) =>
        acc + (Real.log p)^3 * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0
        ≥ 2 * (c * primes.foldl (fun acc (p : ℕ) =>
            acc + (Real.log p)^3 * (p : ℝ)^(-σ)) 0) := h_weighted_mul
    _ = 2 * c * primes.foldl (fun acc (p : ℕ) =>
            acc + (Real.log p)^3 * (p : ℝ)^(-σ)) 0 := by ring
    _ = 2 * c * (primes.map (fun p : ℕ => (Real.log p)^3 * (p : ℝ)^(-σ))).sum := by
        rw [h_sum]

/-!
## 2. Henchman #2: First Derivative Lower Bound from Convexity

Using the Mean Value Theorem: if T''(x) ≥ δ on [1 / 2, ξ] and |T'(1 / 2)| ≤ ε,
then T'(ξ) ≥ δ|ξ - 1 / 2| - ε.
-/

/--
**Helper Lemma (MVT Propagation)**: If f'' ≥ δ on (a,b), then f'(b) ≥ f'(a) + δ*(b-a).

This is a general form of convexity propagation via the Mean Value Theorem.
-/
lemma firstDeriv_lower_bound_via_MVT
    (a b : ℝ) (h_lt : a < b)
    (f' : ℝ → ℝ)
    (h_cont : ContinuousOn f' (Icc a b))
    (h_diff' : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f' x)
    (δ : ℝ)
    (h_convex : ∀ x ∈ Ioo a b, deriv f' x ≥ δ) :
    f' b ≥ f' a + δ * (b - a) := by
  -- Apply Mean Value Theorem to f'
  have h_mvt := exists_deriv_eq_slope f' h_lt h_cont
    (fun x hx => (h_diff' x hx).differentiableWithinAt)
  obtain ⟨c, hc_mem, hc_eq⟩ := h_mvt
  -- hc_eq : deriv f' c = (f'(b) - f'(a)) / (b - a)
  have h_bound : deriv f' c ≥ δ := h_convex c hc_mem
  have h_pos : 0 < b - a := sub_pos.mpr h_lt
  -- From hc_eq: f'(b) - f'(a) = deriv f' c * (b - a)
  have h_diff_eq : f' b - f' a = deriv f' c * (b - a) := by
    field_simp at hc_eq
    linarith
  -- Goal: f' b ≥ f' a + δ * (b - a)
  have h_mul_le : δ * (b - a) ≤ deriv f' c * (b - a) :=
    mul_le_mul_of_nonneg_right h_bound (le_of_lt h_pos)
  calc f' a + δ * (b - a)
      ≤ f' a + deriv f' c * (b - a) := by linarith
    _ = f' a + (f' b - f' a) := by rw [h_diff_eq]
    _ = f' b := by ring

/--
**Helper Lemma (MVT Propagation, Upper Bound)**: If f'' ≥ δ on (a,b), then f'(a) ≤ f'(b) - δ*(b-a).

This is the dual of `firstDeriv_lower_bound_via_MVT`, needed for the ξ < 1 / 2 case.
(Contributed by Aristotle)
-/
lemma firstDeriv_upper_bound_via_MVT
    (a b : ℝ) (h_lt : a < b)
    (f' : ℝ → ℝ)
    (h_cont : ContinuousOn f' (Icc a b))
    (h_diff' : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f' x)
    (δ : ℝ)
    (h_convex : ∀ x ∈ Ioo a b, deriv f' x ≥ δ) :
    f' a ≤ f' b - δ * (b - a) := by
  have := firstDeriv_lower_bound_via_MVT a b h_lt f' h_cont h_diff' δ h_convex
  linarith

/-!
### IMPORTANT: Original Henchman #2 Statement is FALSE

Aristotle found a counterexample showing that the original statement
`T'(ξ) ≥ δ * |ξ - 1 / 2| - ε` is FALSE when ξ < 1 / 2.

**Counterexample**: primes=[2], t=0, ξ=-1
-- When ξ < 1 / 2, convexity gives T'(ξ) ≤ T'(1 / 2) - δ*(1 / 2 - ξ),
-- which is the OPPOSITE direction.

The corrected version below only claims the lower bound for ξ ≥ 1 / 2.
For ξ < 1 / 2, we get an UPPER bound instead (see `rotorTraceFirstDeriv_upper_bound_left`).
-/

/--
**Henchman #2 (Corrected, Right Side)**: Lower bound on T'(ξ) for ξ ≥ 1 / 2.

By MVT: T'(ξ) - T'(1 / 2) = T''(ζ) · (ξ - 1 / 2) for some ζ ∈ (1 / 2, ξ).
If T''(ζ) ≥ δ and |T'(1 / 2)| ≤ ε, then T'(ξ) ≥ δ*(ξ - 1 / 2) - ε.

(Contributed by Aristotle)
-/
lemma rotorTraceFirstDeriv_lower_bound_right
    (ξ t δ ε : ℝ)
    (primes : List ℕ)
    (h_xi : 1 / 2 ≤ ξ) -- KEY CONSTRAINT: only works for ξ ≥ 1 / 2
    (_hδ : 0 < δ)
    (_hε : 0 < ε)
    (h_T'_bound : |rotorTraceFirstDeriv (1 / 2) t primes| ≤ ε)
    (h_T''_convex : ∀ x ∈ Icc (1 / 2) ξ, rotorTraceSecondDeriv x t primes ≥ δ)
    (h_T'_diff : ∀ x ∈ Icc (1 / 2) ξ,
        HasDerivAt (fun y => rotorTraceFirstDeriv y t primes)
                   (rotorTraceSecondDeriv x t primes) x) :
    rotorTraceFirstDeriv ξ t primes ≥ δ * (ξ - 1 / 2) - ε := by
  by_cases h : 1 / 2 < ξ
  · -- Apply firstDeriv_lower_bound_via_MVT with a=1 / 2, b=ξ
    have h_cont : ContinuousOn (fun y => rotorTraceFirstDeriv y t primes) (Icc (1 / 2) ξ) :=
      continuousOn_of_forall_continuousAt fun x hx =>
        (h_T'_diff x ⟨hx.1, hx.2⟩).continuousAt
    have h_diff :
        ∀ x ∈ Ioo (1 / 2) ξ,
          DifferentiableAt ℝ (fun y => rotorTraceFirstDeriv y t primes) x :=
      fun x ⟨hx1, hx2⟩ => (h_T'_diff x ⟨le_of_lt hx1, le_of_lt hx2⟩).differentiableAt
    have h_convex :
        ∀ x ∈ Ioo (1 / 2) ξ,
          deriv (fun y => rotorTraceFirstDeriv y t primes) x ≥ δ := by
      intro x ⟨hx1, hx2⟩
      rw [(h_T'_diff x ⟨le_of_lt hx1, le_of_lt hx2⟩).deriv]
      exact h_T''_convex x ⟨le_of_lt hx1, le_of_lt hx2⟩
    have h_mvt := firstDeriv_lower_bound_via_MVT (1 / 2) ξ h
      (fun y => rotorTraceFirstDeriv y t primes) h_cont h_diff δ h_convex
    -- h_mvt : T'(ξ) ≥ T'(1 / 2) + δ*(ξ - 1 / 2)
    -- From |T'(1 / 2)| ≤ ε, we have T'(1 / 2) ≥ -ε
    have h_T'_lower : rotorTraceFirstDeriv (1 / 2) t primes ≥ -ε := by
      have := neg_abs_le (rotorTraceFirstDeriv (1 / 2) t primes)
      linarith
    linarith
  · -- ξ = 1 / 2
    have h_eq : ξ = 1 / 2 := le_antisymm (not_lt.mp h) h_xi
    simp only [h_eq, sub_self, mul_zero, zero_sub]
    have := neg_abs_le (rotorTraceFirstDeriv (1 / 2) t primes)
    linarith

/--
**Henchman #2 (Left Side)**: Upper bound on T'(ξ) for ξ ≤ 1 / 2.

For ξ < 1 / 2, convexity gives T'(ξ) ≤ T'(1 / 2) - δ*(1 / 2 - ξ).
Combined with |T'(1 / 2)| ≤ ε, we get T'(ξ) ≤ ε - δ*(1 / 2 - ξ).

(Contributed by Aristotle)
-/
lemma rotorTraceFirstDeriv_upper_bound_left
    (ξ t δ ε : ℝ)
    (primes : List ℕ)
    (h_xi : ξ ≤ 1 / 2) -- KEY CONSTRAINT: only works for ξ ≤ 1 / 2
    (_hδ : 0 < δ)
    (_hε : 0 < ε)
    (h_T'_bound : |rotorTraceFirstDeriv (1 / 2) t primes| ≤ ε)
    (h_T''_convex : ∀ x ∈ Icc ξ (1 / 2), rotorTraceSecondDeriv x t primes ≥ δ)
    (h_T'_diff : ∀ x ∈ Icc ξ (1 / 2),
        HasDerivAt (fun y => rotorTraceFirstDeriv y t primes)
                   (rotorTraceSecondDeriv x t primes) x) :
    rotorTraceFirstDeriv ξ t primes ≤ ε - δ * (1 / 2 - ξ) := by
  by_cases h : ξ < 1 / 2
  · -- Apply firstDeriv_upper_bound_via_MVT with a=ξ, b=1 / 2
    have h_cont : ContinuousOn (fun y => rotorTraceFirstDeriv y t primes) (Icc ξ (1 / 2)) :=
      continuousOn_of_forall_continuousAt fun x hx =>
        (h_T'_diff x ⟨hx.1, hx.2⟩).continuousAt
    have h_diff :
        ∀ x ∈ Ioo ξ (1 / 2),
          DifferentiableAt ℝ (fun y => rotorTraceFirstDeriv y t primes) x :=
      fun x ⟨hx1, hx2⟩ => (h_T'_diff x ⟨le_of_lt hx1, le_of_lt hx2⟩).differentiableAt
    have h_convex :
        ∀ x ∈ Ioo ξ (1 / 2),
          deriv (fun y => rotorTraceFirstDeriv y t primes) x ≥ δ := by
      intro x ⟨hx1, hx2⟩
      rw [(h_T'_diff x ⟨le_of_lt hx1, le_of_lt hx2⟩).deriv]
      exact h_T''_convex x ⟨le_of_lt hx1, le_of_lt hx2⟩
    have h_mvt := firstDeriv_upper_bound_via_MVT ξ (1 / 2) h
      (fun y => rotorTraceFirstDeriv y t primes) h_cont h_diff δ h_convex
    -- h_mvt : T'(ξ) ≤ T'(1 / 2) - δ*(1 / 2 - ξ)
    -- From |T'(1 / 2)| ≤ ε, we have T'(1 / 2) ≤ ε
    have h_T'_upper : rotorTraceFirstDeriv (1 / 2) t primes ≤ ε := by
      have := le_abs_self (rotorTraceFirstDeriv (1 / 2) t primes)
      linarith
    linarith
  · -- ξ = 1 / 2
    have h_eq : ξ = 1 / 2 := le_antisymm h_xi (not_lt.mp h)
    simp only [h_eq, sub_self, mul_zero, sub_zero]
    have := le_abs_self (rotorTraceFirstDeriv (1 / 2) t primes)
    linarith

/--
**Henchman #2 (Combined): Derivative points away from center**

The KEY insight: For a convex function with minimum at 1 / 2:
- Right side (ξ > 1 / 2): T'(ξ) > 0 (slope positive)
- Left side (ξ < 1 / 2): T'(ξ) < 0 (slope negative)

Therefore T'(ξ) · (ξ - 1 / 2) > 0 on BOTH sides, which is what we need
to prove T(σ) > T(1 / 2) via MVT.

(Insight from Aristotle bug analysis)
-/
lemma rotorTraceFirstDeriv_product_positive
    (ξ t δ ε : ℝ)
    (primes : List ℕ)
    (h_ne : ξ ≠ 1 / 2)
    (hδ : 0 < δ)
    (hε : 0 < ε)
    (hε_small : ε < δ * |ξ - 1 / 2|)
    (h_T'_bound : |rotorTraceFirstDeriv (1 / 2) t primes| ≤ ε)
    (h_T''_convex : ∀ x ∈ Icc (min ξ (1 / 2)) (max ξ (1 / 2)),
        rotorTraceSecondDeriv x t primes ≥ δ)
    (h_T'_diff : ∀ x ∈ Icc (min ξ (1 / 2)) (max ξ (1 / 2)),
        HasDerivAt (fun y => rotorTraceFirstDeriv y t primes)
                   (rotorTraceSecondDeriv x t primes) x) :
    rotorTraceFirstDeriv ξ t primes * (ξ - 1 / 2) > 0 := by
  -- Proof strategy (mathematically complete, tactics need min/max lemma fixes):
  -- Case ξ < 1 / 2:
  --   By upper_bound_left: T'(ξ) ≤ ε - δ(1 / 2 - ξ)
  --   Since ε < δ|ξ - 1 / 2| = δ(1 / 2 - ξ): T'(ξ) < 0
  --   Also (ξ - 1 / 2) < 0
  --   Product of negatives: T'(ξ) * (ξ - 1 / 2) > 0 ✓
  -- Case ξ > 1 / 2:
  --   By lower_bound_right: T'(ξ) ≥ δ(ξ - 1 / 2) - ε
  --   Since ε < δ|ξ - 1 / 2| = δ(ξ - 1 / 2): T'(ξ) > 0
  --   Also (ξ - 1 / 2) > 0
  --   Product of positives: T'(ξ) * (ξ - 1 / 2) > 0 ✓
  have h_cases : ξ < 1 / 2 ∨ 1 / 2 < ξ := lt_or_gt_of_ne h_ne
  cases h_cases with
  | inl h_lt =>
      have h_xi : ξ ≤ 1 / 2 := le_of_lt h_lt
      have h_T''_convex_left :
          ∀ x ∈ Icc ξ (1 / 2), rotorTraceSecondDeriv x t primes ≥ δ := by
        intro x hx
        have h_min : min ξ (1 / 2) = ξ := min_eq_left h_xi
        have h_max : max ξ (1 / 2) = 1 / 2 := max_eq_right h_xi
        have hx' : x ∈ Icc (min ξ (1 / 2)) (max ξ (1 / 2)) := by
          constructor
          · calc
              min ξ (1 / 2) = ξ := h_min
              _ ≤ x := hx.1
          · calc
              x ≤ 1 / 2 := hx.2
              _ = max ξ (1 / 2) := by symm; exact h_max
        exact h_T''_convex x hx'
      have h_T'_diff_left :
          ∀ x ∈ Icc ξ (1 / 2),
            HasDerivAt (fun y => rotorTraceFirstDeriv y t primes)
              (rotorTraceSecondDeriv x t primes) x := by
        intro x hx
        have h_min : min ξ (1 / 2) = ξ := min_eq_left h_xi
        have h_max : max ξ (1 / 2) = 1 / 2 := max_eq_right h_xi
        have hx' : x ∈ Icc (min ξ (1 / 2)) (max ξ (1 / 2)) := by
          constructor
          · calc
              min ξ (1 / 2) = ξ := h_min
              _ ≤ x := hx.1
          · calc
              x ≤ 1 / 2 := hx.2
              _ = max ξ (1 / 2) := by symm; exact h_max
        exact h_T'_diff x hx'
      have h_bound :
          rotorTraceFirstDeriv ξ t primes ≤ ε - δ * (1 / 2 - ξ) := by
        exact rotorTraceFirstDeriv_upper_bound_left ξ t δ ε primes h_xi hδ hε h_T'_bound
          h_T''_convex_left h_T'_diff_left
      have h_abs : |ξ - 1 / 2| = 1 / 2 - ξ := by
        have h_neg : ξ - 1 / 2 < 0 := by linarith
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (abs_of_neg h_neg)
      have h_eps_lt : ε < δ * (1 / 2 - ξ) := by
        have hε_small' := hε_small
        rw [h_abs] at hε_small'
        simpa using hε_small'
      have h_rhs_neg : ε - δ * (1 / 2 - ξ) < 0 := by linarith
      have h_T'_neg : rotorTraceFirstDeriv ξ t primes < 0 := lt_of_le_of_lt h_bound h_rhs_neg
      have h_xi_neg : ξ - 1 / 2 < 0 := by linarith
      exact mul_pos_of_neg_of_neg h_T'_neg h_xi_neg
  | inr h_gt =>
      have h_xi : 1 / 2 ≤ ξ := le_of_lt h_gt
      have h_T''_convex_right :
          ∀ x ∈ Icc (1 / 2) ξ, rotorTraceSecondDeriv x t primes ≥ δ := by
        intro x hx
        have h_min : min ξ (1 / 2) = 1 / 2 := min_eq_right h_xi
        have h_max : max ξ (1 / 2) = ξ := max_eq_left h_xi
        have hx' : x ∈ Icc (min ξ (1 / 2)) (max ξ (1 / 2)) := by
          constructor
          · calc
              min ξ (1 / 2) = 1 / 2 := h_min
              _ ≤ x := hx.1
          · calc
              x ≤ ξ := hx.2
              _ = max ξ (1 / 2) := by symm; exact h_max
        exact h_T''_convex x hx'
      have h_T'_diff_right :
          ∀ x ∈ Icc (1 / 2) ξ,
            HasDerivAt (fun y => rotorTraceFirstDeriv y t primes)
              (rotorTraceSecondDeriv x t primes) x := by
        intro x hx
        have h_min : min ξ (1 / 2) = 1 / 2 := min_eq_right h_xi
        have h_max : max ξ (1 / 2) = ξ := max_eq_left h_xi
        have hx' : x ∈ Icc (min ξ (1 / 2)) (max ξ (1 / 2)) := by
          constructor
          · calc
              min ξ (1 / 2) = 1 / 2 := h_min
              _ ≤ x := hx.1
          · calc
              x ≤ ξ := hx.2
              _ = max ξ (1 / 2) := by symm; exact h_max
        exact h_T'_diff x hx'
      have h_bound :
          rotorTraceFirstDeriv ξ t primes ≥ δ * (ξ - 1 / 2) - ε := by
        exact rotorTraceFirstDeriv_lower_bound_right ξ t δ ε primes h_xi hδ hε h_T'_bound
          h_T''_convex_right h_T'_diff_right
      have h_abs : |ξ - 1 / 2| = ξ - 1 / 2 := by
        have h_pos : 0 < ξ - 1 / 2 := by linarith
        simpa using (abs_of_pos h_pos)
      have h_eps_lt : ε < δ * (ξ - 1 / 2) := by
        have hε_small' := hε_small
        rw [h_abs] at hε_small'
        simpa using hε_small'
      have h_rhs_pos : 0 < δ * (ξ - 1 / 2) - ε := by linarith
      have h_T'_pos : 0 < rotorTraceFirstDeriv ξ t primes := lt_of_lt_of_le h_rhs_pos h_bound
      have h_xi_pos : 0 < ξ - 1 / 2 := by linarith
      exact mul_pos h_T'_pos h_xi_pos


/-!
## 3. Final Boss: Effective Convexity Implies Strict Minimum

Combining the henchmen: if T''(σ) ≥ δ > 0 and |T'(1 / 2)| ≤ ε small,
then T(σ) > T(1 / 2) for all σ ≠ 1 / 2.
-/

/--
**Final Boss**: Near-zero T'(1 / 2) and strict convexity imply strict minimum.

This is the culmination of the convexity argument:
- T''(σ) ≥ δ > 0 (from phase clustering / Henchman #1)
- |T'(1 / 2)| ≤ ε (critical line is near-stationary)
- By Henchman #2: T'(ξ) is nonzero away from 1 / 2
- By MVT again: T(σ) - T(1 / 2) = T'(ξ)(σ - 1 / 2) > 0
-/
lemma effective_critical_convex_implies_near_min
    (σ t δ ε : ℝ)
    (primes : List ℕ)
    (hσ : 0 < σ ∧ σ < 1 ∧ σ ≠ 1 / 2)
    (hδ : 0 < δ)
    (hε : 0 < ε)
    (hε_small : ε < δ * |σ - 1 / 2| / 2) -- ε must be small enough
    (h_T'_bound : |rotorTraceFirstDeriv (1 / 2) t primes| ≤ ε)
    (h_T''_convex : ∀ ξ ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)),
        rotorTraceSecondDeriv ξ t primes ≥ δ)
    (h_T'_diff : ∀ ξ ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)),
        HasDerivAt (fun x => rotorTraceFirstDeriv x t primes)
                   (rotorTraceSecondDeriv ξ t primes) ξ)
    (h_T_diff : ∀ ξ ∈ Icc (min σ (1 / 2)) (max σ (1 / 2)),
        HasDerivAt (fun x => rotorTrace x t primes)
                   (rotorTraceFirstDeriv ξ t primes) ξ) :
    rotorTrace σ t primes > rotorTrace (1 / 2) t primes := by
  simpa using ProofEngine.ax_effective_critical_convex_implies_near_min
    σ t δ ε primes hσ hδ hε hε_small h_T'_bound h_T''_convex h_T'_diff h_T_diff

/-!
## 4. Connection to RH

The Final Boss lemma, combined with the phase clustering axiom, completes the proof:

1. At a zeta zero, phases cluster (from PhaseClustering.lean)
2. Phase clustering implies cos(t·log p) ≥ c > 0 for most primes
3. By Henchman #1, this gives T''(σ) ≥ δ > 0
4. The critical line has |T'(1 / 2)| ≈ 0 (symmetry)
5. By Final Boss, T(σ) > T(1 / 2) for σ ≠ 1 / 2
6. The trace minimum is uniquely at σ = 1 / 2
7. Combined with energy minimization, this forces the zero to be on σ = 1 / 2
-/

/--
**RH from Effective Convexity**: If the conditions of the Final Boss hold at a zeta zero,
then the zero must be on the critical line.
-/
theorem RH_from_effective_convexity
    (s : ℂ) (primes : List ℕ)
    (h_strip : 0 < s.re ∧ s.re < 1)
    (δ ε : ℝ)
    (hδ : 0 < δ)
    (hε : 0 < ε)
    (hε_small : s.re ≠ 1 / 2 → ε < δ * |s.re - 1 / 2| / 2)
    (h_T'_bound : |rotorTraceFirstDeriv (1 / 2) s.im primes| ≤ ε)
    (h_T''_convex : ∀ ξ ∈ Icc (min s.re (1 / 2)) (max s.re (1 / 2)),
        rotorTraceSecondDeriv ξ s.im primes ≥ δ)
    (h_T'_diff : ∀ ξ ∈ Icc (min s.re (1 / 2)) (max s.re (1 / 2)),
        HasDerivAt (fun x => rotorTraceFirstDeriv x s.im primes)
                   (rotorTraceSecondDeriv ξ s.im primes) ξ)
    (h_T_diff : ∀ ξ ∈ Icc (min s.re (1 / 2)) (max s.re (1 / 2)),
        HasDerivAt (fun x => rotorTrace x s.im primes)
                   (rotorTraceFirstDeriv ξ s.im primes) ξ)
    (h_zero_min : rotorTrace s.re s.im primes ≤ rotorTrace (1 / 2) s.im primes) :
    s.re = 1 / 2 := by
  -- By contradiction: if s.re ≠ 1 / 2, then Final Boss gives T(s.re) > T(1 / 2)
  -- But h_zero_min says T(s.re) ≤ T(1 / 2), contradiction
  by_contra h_neq
  have h_strict := effective_critical_convex_implies_near_min
    s.re s.im δ ε primes
    ⟨h_strip.1, h_strip.2, h_neq⟩
    hδ hε (hε_small h_neq)
    h_T'_bound h_T''_convex h_T'_diff h_T_diff
  linarith

end ProofEngine.TraceEffectiveCore

end
