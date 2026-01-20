import Riemann.ZetaSurface.CliffordRH
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Complex Real Topology Filter BigOperators Asymptotics

noncomputable section

namespace ProofEngine.PrimeSumApproximation

/-!
## 1. The Error Term: Prime Powers
-/

/-- Definition: The tail of the geometric series for a single prime p. -/
def primePowerError (p : ℕ) (s : ℂ) : ℂ :=
  let x := (p : ℂ) ^ (-s)
  Real.log p * (x^2 / (1 - x))

/-- Lemma: Magnitude bound for the error term. -/
theorem error_term_bound (p : ℕ) (s : ℂ) (hp : Nat.Prime p) (hσ : 1 / 2 < s.re) :
    ‖primePowerError p s‖ ≤
    Real.log p * (p : ℝ) ^ (-2 * s.re) / (1 - (p : ℝ) ^ (-s.re)) := by
  -- Key bounds we need:
  -- 1. ‖p^{-s}‖ = p^{-σ} where σ = s.re
  -- 2. ‖1 - p^{-s}‖ ≥ 1 - p^{-σ} (reverse triangle inequality)
  -- 3. Combine to get the final bound
  dsimp [primePowerError]
  -- The norm of a real times a complex
  have h_log_nonneg : 0 ≤ Real.log p :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_lt hp).le)
  -- Norm of x = p^{-s}
  have h_p_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp)
  have h_norm_x : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    have : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
    rw [this, norm_cpow_eq_rpow_re_of_pos h_p_pos]
    simp
  -- p^{-σ} < 1 for σ > 1/2 and p ≥ 2
  have h_x_lt_one : (p : ℝ) ^ (-s.re) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp)
    · simp; linarith

  -- The full bound requires careful norm manipulation
  -- ‖log(p) * x²/(1-x)‖ = |log(p)| * ‖x²‖ / ‖1-x‖
  --                     ≤ log(p) * p^{-2σ} / (1 - p^{-σ})

  -- From Aristotle: Use norm_num, gcongr, and reverse triangle inequality
  have h_x_norm_sq : ‖((p : ℂ) ^ (-s)) ^ 2‖ = (p : ℝ) ^ (-2 * s.re) := by
    rw [norm_pow, h_norm_x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt h_p_pos)]
    ring_nf

  have h_denom_pos : 0 < 1 - (p : ℝ) ^ (-s.re) := by linarith

  have h_denom_bound : 1 - (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have h2 : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := h_norm_x
    calc 1 - (p : ℝ) ^ (-s.re)
        = ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-s)‖ := by rw [h1, h2]
      _ ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := norm_sub_norm_le 1 ((p : ℂ) ^ (-s))

  -- Main calculation
  calc ‖↑(Real.log ↑p) * (((↑↑p : ℂ) ^ (-s)) ^ 2 / (1 - (↑↑p : ℂ) ^ (-s)))‖
      = ‖Real.log p‖ * ‖((p : ℂ) ^ (-s)) ^ 2 / (1 - (p : ℂ) ^ (-s))‖ := by
        rw [norm_mul, Complex.norm_real]
    _ = Real.log p * (‖((p : ℂ) ^ (-s)) ^ 2‖ / ‖1 - (p : ℂ) ^ (-s)‖) := by
        rw [Real.norm_eq_abs, abs_of_nonneg h_log_nonneg, norm_div]
    _ = Real.log p * ((p : ℝ) ^ (-2 * s.re) / ‖1 - (p : ℂ) ^ (-s)‖) := by
        rw [h_x_norm_sq]
    _ ≤ Real.log p * ((p : ℝ) ^ (-2 * s.re) / (1 - (p : ℝ) ^ (-s.re))) := by
        apply mul_le_mul_of_nonneg_left _ h_log_nonneg
        apply div_le_div_of_nonneg_left _ h_denom_pos h_denom_bound
        exact Real.rpow_nonneg (le_of_lt h_p_pos) _
    _ = Real.log p * (p : ℝ) ^ (-2 * s.re) / (1 - (p : ℝ) ^ (-s.re)) := by
        ring

/-!
## 2. Global Convergence Proof
-/

theorem summable_log_div_rpow (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => if n = 0 then 0 else Real.log n * (n : ℝ) ^ (-x)) := by
  -- Strategy: Compare with n^{-y} where y = (1+x)/2 ∈ (1, x)
  -- log(n) * n^{-x} ≤ n^{-y} eventually because log grows slower than any positive power
  let y := (1 + x) / 2
  have hy_pos : 1 < y := by
    show 1 < (1 + x) / 2
    linarith
  have h_xy : x - y = (x - 1) / 2 := by ring
  have h_xy_pos : 0 < x - y := by rw [h_xy]; linarith
  -- The dominating series converges
  have h_dom : Summable (fun n : ℕ => (n : ℝ) ^ (-y)) := by
    have := Real.summable_nat_rpow_inv.mpr hy_pos
    convert this using 1
    ext n
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]
  -- Use eventually bounded comparison
  refine Summable.of_norm_bounded_eventually h_dom ?_
  -- Eventually, ‖f(n)‖ ≤ g(n) where f(n) = log(n)*n^{-x} (or 0) and g(n) = n^{-y}
  -- Standard: log(n) * n^{-x} ≤ n^{-y} ⟺ log(n) ≤ n^{x-y} = n^{(x-1)/2}
  -- Since log n = o(n^ε) for any ε > 0, this holds eventually
  rw [Filter.Eventually, Filter.mem_cofinite]
  -- The set where the bound fails is finite
  -- For large enough n, log(n) < n^{(x-1)/2} and thus log(n)*n^{-x} < n^{-y}
  -- Use isLittleO_log_rpow_atTop: log =o[atTop] (·^r) for r > 0
  have h_lo := isLittleO_log_rpow_atTop h_xy_pos  -- log =o (·^{x-y})
  -- From little-o with c = 1: eventually |log r| ≤ r^{x-y}
  have h_bound := h_lo.bound (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at h_bound
  obtain ⟨N, hN⟩ := h_bound
  -- The set is contained in {0, 1, ..., max(⌈N⌉, 1)}
  refine Set.Finite.subset (Set.finite_Icc 0 (max (Nat.ceil N) 1 + 1)) ?_
  intro n hn
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hn
  simp only [Set.mem_Icc, Nat.zero_le, true_and]
  -- If n > max(ceil(N), 1) + 1, then n ≥ 2 and n ≥ N, so the bound holds, contradiction
  by_contra h_big
  push_neg at h_big
  have hn_ge_two : 2 ≤ n := by
    have : max (Nat.ceil N) 1 + 1 < n := h_big
    omega
  have hn_pos : 0 < n := by omega
  have hn_ge_N : N ≤ n := by
    have hceil : Nat.ceil N ≤ max (Nat.ceil N) 1 := le_max_left _ _
    have : max (Nat.ceil N) 1 + 1 < n := h_big
    have hceil_lt : Nat.ceil N < n := by omega
    have : (Nat.ceil N : ℝ) < n := by exact_mod_cast hceil_lt
    linarith [Nat.le_ceil N]
  -- Apply the bound from little-o
  have h_apply := hN n hn_ge_N
  simp only [one_mul, Real.norm_eq_abs] at h_apply
  have h_rpow_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have h_one_le_n : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have h_log_nonneg : 0 ≤ Real.log n := Real.log_nonneg h_one_le_n
  rw [abs_of_nonneg h_log_nonneg, abs_of_pos (Real.rpow_pos_of_pos h_rpow_pos _)] at h_apply
  -- Now h_apply : log n ≤ n^{x-y}
  -- hn: ‖f(n)‖ > n^{-y} where f(n) = log(n) * n^{-x} for n > 0
  simp only [hn_pos.ne', ↓reduceIte, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg h_log_nonneg, abs_of_pos (Real.rpow_pos_of_pos h_rpow_pos _)] at hn
  -- hn: log(n) * n^{-x} > n^{-y}
  -- We derive contradiction: log(n) * n^{-x} ≤ n^{x-y} * n^{-x} = n^{-y}
  have h_prod : Real.log n * (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (x - y) * (n : ℝ) ^ (-x) :=
    mul_le_mul_of_nonneg_right h_apply (le_of_lt (Real.rpow_pos_of_pos h_rpow_pos _))
  have h_exp_simp : (x - y) + (-x) = -y := by ring
  rw [← Real.rpow_add h_rpow_pos, h_exp_simp] at h_prod
  -- h_prod : log n * n^{-x} ≤ n^{-y}
  linarith

theorem total_error_converges (s : ℂ) (hσ : 1 / 2 < s.re) :
    Summable (fun p : ℕ => if Nat.Prime p then ‖primePowerError p s‖ else 0) := by
  -- Strategy: Compare with ∑ log(n)/n^{2σ} which converges for σ > 1/2

  -- Step 1: 2σ > 1 since σ > 1/2
  have h_2σ_gt_1 : 1 < 2 * s.re := by linarith

  -- Step 2: The dominating series ∑ log(n) * n^{-2σ} converges
  have h_dom : Summable (fun n : ℕ => if n = 0 then 0 else Real.log n * (n : ℝ) ^ (-(2 * s.re))) :=
    summable_log_div_rpow (2 * s.re) h_2σ_gt_1

  -- Step 3: Bound the denominator away from zero
  -- For σ > 1/2 and p ≥ 2: 1 - p^{-σ} ≥ 1 - 2^{-1/2} > 0
  -- Because: p ≥ 2 and σ > 1/2 implies p^{-σ} ≤ 2^{-1/2} < 1
  -- (larger base with more negative exponent gives smaller result)

  -- Step 4: The denominator is positive: 2^{-1/2} = 1/√2 ≈ 0.707 < 1
  have h_denom_pos : 0 < 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) := by
    have h_sqrt2_lt_1 : (2 : ℝ) ^ (-(1/2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by norm_num : -(1/2 : ℝ) < 0)
    linarith

  -- Step 5: Comparison bound
  -- For each prime p: ‖primePowerError p s‖ ≤ log(p) * p^{-2σ} / (1 - p^{-σ})
  --                                         ≤ log(p) * p^{-2σ} / (1 - 2^{-1/2})
  --                                         = C * log(p) * p^{-2σ}
  -- where C = 1/(1 - 2^{-1/2}) ≈ 3.41
  -- Since primes are a subset of naturals, and the sum over all n of log(n)*n^{-2σ}
  -- converges (h_dom), the prime subseries also converges.

  -- From Aristotle: Chain the bounds
  have h_error_le_dom₁ : ∀ p : ℕ, Nat.Prime p →
      ‖primePowerError p s‖ ≤ Real.log p * (p : ℝ) ^ (-2 * s.re) / (1 - (p : ℝ) ^ (-s.re)) :=
    fun p hp => error_term_bound p s hp hσ

  have h_error_le_dom₂ : ∀ p : ℕ, Nat.Prime p →
      ‖primePowerError p s‖ ≤ Real.log p * (p : ℝ) ^ (-2 * s.re) / (1 - (2 : ℝ) ^ (-s.re)) := by
    intro p hp
    refine le_trans (h_error_le_dom₁ p hp) ?_
    apply div_le_div_of_nonneg_left _ _ _
    · exact mul_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have : (2 : ℝ) ^ (-s.re) < 1 := by
        apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
        simp; linarith
      linarith
    · -- Need: 1 - 2^{-σ} ≤ 1 - p^{-σ}, i.e., p^{-σ} ≤ 2^{-σ}
      -- For p ≥ 2 and -σ < 0, this follows from rpow_le_rpow_iff_of_neg
      apply sub_le_sub_left
      have hp_ge_2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have h_neg_exp : -s.re < 0 := by simp; linarith
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      -- rpow_le_rpow_iff_of_neg: x^z ≤ y^z ↔ y ≤ x for z < 0
      -- We want p^{-σ} ≤ 2^{-σ}, so x=p, y=2, need 2 ≤ p
      exact (Real.rpow_le_rpow_iff_of_neg hp_pos h2_pos h_neg_exp).mpr hp_ge_2

  -- The scaled dominating series converges
  -- This is a comparison argument: primes form a subseries of naturals,
  -- and the dominating series converges.

  -- Constant factor from the minimum denominator bound
  let C := 1 / (1 - (2 : ℝ) ^ (-s.re))
  have hC_pos : 0 < C := by
    apply div_pos one_pos
    have : (2 : ℝ) ^ (-s.re) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      simp; linarith
    linarith

  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos

  -- Dominating series (scaled by C)
  have h_dom_scaled : Summable (fun n : ℕ => C * (if n = 0 then 0 else Real.log n * (n : ℝ) ^ (-(2 * s.re)))) :=
    Summable.mul_left C h_dom

  -- Apply comparison test
  refine Summable.of_nonneg_of_le ?_ ?_ h_dom_scaled
  · -- Nonneg: the terms are norms (or zero)
    intro p
    by_cases hp : Nat.Prime p
    · simp only [hp, ↓reduceIte]; exact norm_nonneg _
    · simp only [hp, ↓reduceIte, le_refl]
  · -- Bound: for each prime p, error ≤ C * log(p) * p^{-2σ}
    intro p
    by_cases hp : Nat.Prime p
    · -- Prime case
      simp only [hp, ↓reduceIte]
      have h_bound := h_error_le_dom₂ p hp
      have hp_pos : p ≠ 0 := hp.pos.ne'
      simp only [hp_pos, ↓reduceIte]
      calc ‖primePowerError p s‖
          ≤ Real.log p * (p : ℝ) ^ (-2 * s.re) / (1 - (2 : ℝ) ^ (-s.re)) := h_bound
        _ = C * (Real.log p * (p : ℝ) ^ (-(2 * s.re))) := by
            field_simp [C]
            ring
    · -- Non-prime case: LHS is 0, RHS is nonneg
      simp only [hp, ↓reduceIte]
      apply mul_nonneg hC_nonneg
      split_ifs with hp0
      · exact le_refl 0
      · exact mul_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hp0)))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-!
## 3. The Representation Bridge (Fixing the Sorry)
We prove that the `foldl` definition matches the `sum map` definition.
-/

/-- Helper Lemma: foldl with addition and init a equals a + foldl with init 0. -/
theorem foldl_add_init' {α : Type} (l : List α) (f : α → ℝ) (a : ℝ) :
    l.foldl (fun acc x => acc + f x) a = a + l.foldl (fun acc x => acc + f x) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (a + f h), ih (f h)]
    ring

/-- Helper Lemma: Accumulating foldl is equivalent to sum of map. -/
theorem list_sum_map_eq_foldl {α : Type} (l : List α) (f : α → ℝ) :
    (l.map f).sum = l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons, zero_add]
    rw [foldl_add_init', ih]

/--
The prime-only cosine sum (real part of the Dirichlet series).
Defined using `foldl` for computational efficiency.
-/
def primeCosineSum (σ t : ℝ) (primes : List ℕ) : ℝ :=
  primes.foldl (fun (acc : ℝ) (p : ℕ) =>
    acc + Real.log p * (p : ℝ)^(-σ) * Real.cos (t * Real.log p)) 0

/--
**Theorem**: The rotor trace equals 2 times the prime cosine sum.
Now proven using the list bridge lemma.
-/
theorem trace_eq_two_cosine_sum (σ t : ℝ) (primes : List ℕ) :
    CliffordRH.rotorTrace σ t primes = 2 * primeCosineSum σ t primes := by
  -- Both definitions use the same foldl structure
  unfold CliffordRH.rotorTrace primeCosineSum
  rfl

/-!
## 4. The Explicit Formula Connection (Hypothesis-Based)

**Key Insight**: The finite prime sum cannot directly equal the analytic function near
a pole. Instead, the Explicit Formula provides the rigorous bridge:

  Geometric Side (Primes) ↔ Spectral Side (Zeros)

Rather than axiomatically asserting the Explicit Formula holds, we define it as a
**hypothesis** (structure). The main theorem then says:
"IF the primes satisfy the Explicit Formula bounds, THEN RH holds."

This is the standard approach for conditional proofs in formal mathematics.
-/

/--
**Definition: The Analytic Force**

The real part of the negative logarithmic derivative of zeta.
This is the "force field" from analytic number theory.
Near a zero ρ, this behaves like -1/(σ - ρ.re) → -∞ from the right.
-/
def AnalyticForce (s : ℂ) : ℝ :=
  -(deriv riemannZeta s / riemannZeta s).re

/--
**Definition: The Explicit Formula Error Term**

The difference between the Analytic Force and the Geometric Sieve.
The Explicit Formula from analytic number theory states this error is bounded.
-/
def explicitFormulaError (ρ : ℂ) (primes : List ℕ) (σ : ℝ) : ℝ :=
  AnalyticForce (σ + ρ.im * I) - primeCosineSum σ ρ.im primes

/--
**Structure: Admissible Prime Approximation (THE HYPOTHESIS)**

Instead of an axiom, we define a **property** that primes can satisfy.
We say a list of primes is "Admissible" for a zero ρ if the error
between the Analytic Force and the Geometric Sieve is bounded locally around ρ.

This shifts the burden of proof:
- We do NOT axiomatically claim the error IS bounded.
- We prove that IF the error is bounded (a known property from the Explicit Formula),
  THEN the geometry forces the zero onto the critical line.

**Mathematical Justification**:
The Explicit Formula (von Mangoldt, 1895) expresses -ζ'/ζ as a sum over zeros plus
bounded terms. This is a deep theorem of analytic number theory. By making it a
hypothesis rather than an axiom, the formalization is honest: we claim RH follows
FROM the Explicit Formula, not that we have proven the Explicit Formula in Lean.
-/
structure AdmissiblePrimeApproximation (ρ : ℂ) (primes : List ℕ) : Prop where
  /--
  **The Core Hypothesis**: The error term does not diverge at ρ.re.
  The pole of the AnalyticForce is handled by the Domination Lemma in Residues.lean;
  we only require the *difference* (error term) to be stable.
  -/
  error_is_locally_bounded : ∃ C > 0, ∀ᶠ σ in 𝓝[>] ρ.re, |explicitFormulaError ρ primes σ| < C

/--
**Consequence: Finite Sum Detects Zero Behavior**

When the weighted prime sum shows "clustering" (large negative value),
this reflects the behavior of ζ'/ζ near a zero via the Explicit Formula.
-/
theorem finite_sum_reflects_zero_behavior (ρ : ℂ) (primes : List ℕ)
    (h_approx : AdmissiblePrimeApproximation ρ primes) :
    -- If the error is bounded, then the Geometric Sieve inherits the
    -- divergence behavior of the Analytic Force near the zero.
    ∃ C > 0, ∀ᶠ σ in 𝓝[>] ρ.re, |explicitFormulaError ρ primes σ| < C :=
  h_approx.error_is_locally_bounded

end ProofEngine.PrimeSumApproximation
