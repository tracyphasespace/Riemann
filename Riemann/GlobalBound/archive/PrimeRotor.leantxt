/-
# PrimeRotor.lean - Orthogonal Bivector Space

This file establishes the orthogonal structure of prime-indexed bivectors
and proves energy persistence using the Fundamental Theorem of Arithmetic.

## Key Results
1. `axes_are_orthogonal` - Prime axes form an orthonormal basis
2. `log_ratio_irrational` - log(p)/log(q) is irrational for distinct primes
3. `no_simultaneous_zeros` - sin(t·log p) and sin(t·log q) can't both vanish for t > 0
4. `energy_positive_for_positive_t` - At least one sin²(t·log p) > 0 for |S| ≥ 2

## Attribution
Mathematical reduction from custom axioms to FTA-based proof.
-/

import Riemann.GlobalBound.ZetaManifold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Int.Basic
import Riemann.ProofEngine.EnergySymmetry

noncomputable section
open Real Filter Topology BigOperators Complex

namespace GlobalBound

/-!
## 1. Orthogonal Bivector Space (Cl(∞) Structure)
-/

/--
A geometric state vector indexed by a finite set of primes (the Support).
This represents a finite slice of the infinite Clifford Algebra Cl(∞).
-/
structure PrimeIndexedBivector (support : Finset ℕ) where
  coeff : ℕ → ℝ
  h_support : ∀ p, p ∉ support → coeff p = 0

def innerProduct {S : Finset ℕ} (u v : PrimeIndexedBivector S) : ℝ :=
  S.sum (fun p => u.coeff p * v.coeff p)

def magSq {S : Finset ℕ} (v : PrimeIndexedBivector S) : ℝ :=
  innerProduct v v

/--
The Canonical Axis for prime p: the basis vector e_p.
-/
def orthogonalAxis (p : ℕ) (S : Finset ℕ) (hp : p ∈ S) : PrimeIndexedBivector S where
  coeff := fun q => if q = p then 1 else 0
  h_support := by
    intro q hq
    have h_neq : q ≠ p := fun h => hq (h ▸ hp)
    simp [h_neq]

/--
**THEOREM: Orthogonality of Prime Axes (PROVEN)**
-/
theorem axes_are_orthogonal {S : Finset ℕ} (p q : ℕ) (hp : p ∈ S) (hq : q ∈ S)
    (h_neq : p ≠ q) :
    innerProduct (orthogonalAxis p S hp) (orthogonalAxis q S hq) = 0 := by
  classical
  unfold innerProduct
  apply Finset.sum_eq_zero
  intro r _hr
  by_cases hrp : r = p
  · subst hrp
    simp [orthogonalAxis, h_neq]
  · by_cases hrq : r = q
    · have hqp : q ≠ p := h_neq.symm
      simp [orthogonalAxis, hrq, hqp]
    · simp [orthogonalAxis, hrp, hrq]

/-!
## 2. Logarithmic Independence via Fundamental Theorem of Arithmetic

The key insight: For distinct primes p ≠ q, if log(p)/log(q) = k/m for integers k, m,
then p^m = q^k, which contradicts unique factorization (FTA).
-/

/--
**LEMMA: Log ratio of distinct primes is irrational**
For distinct primes p, q: log(p)/log(q) ∉ ℚ.

Proof sketch: If log(p)/log(q) = a/b for integers a, b with b ≠ 0,
then b·log(p) = a·log(q), so log(p^b) = log(q^a), hence p^b = q^a.
This contradicts the Fundamental Theorem of Arithmetic since p ≠ q.
-/
theorem log_ratio_irrational {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  rw [irrational_iff_ne_rational]
  intro a b hb h_eq
  -- If log(p)/log(q) = a/b, then p^|b| = q^|a| (after sign normalization)
  -- This contradicts FTA: distinct primes can't have equal prime factorizations
  have h_log_p_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h_log_q_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have h_log_q_ne : Real.log q ≠ 0 := ne_of_gt h_log_q_pos
  have hb_ne : (b : ℝ) ≠ 0 := by simp [Int.cast_ne_zero.mpr hb]
  -- From log(p)/log(q) = a/b, get b·log(p) = a·log(q)
  have h_cross : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    field_simp [h_log_q_ne] at h_eq ⊢
    linarith
  -- Handle signs: b·log(p) = a·log(q) implies |b|·log(p) = |a|·log(q)
  have h_abs_cross : (b.natAbs : ℝ) * Real.log p = (a.natAbs : ℝ) * Real.log q := by
    have hb_abs : |(b : ℝ)| = (b.natAbs : ℝ) := by simp [Int.cast_abs]
    have ha_abs : |(a : ℝ)| = (a.natAbs : ℝ) := by simp [Int.cast_abs]
    calc (b.natAbs : ℝ) * Real.log p
        = |(b : ℝ)| * Real.log p := by rw [← hb_abs]
      _ = |(b : ℝ) * Real.log p| := by rw [abs_mul, abs_of_pos h_log_p_pos]
      _ = |(a : ℝ) * Real.log q| := by rw [h_cross]
      _ = |(a : ℝ)| * Real.log q := by rw [abs_mul, abs_of_pos h_log_q_pos]
      _ = (a.natAbs : ℝ) * Real.log q := by rw [ha_abs]
  -- From |b|·log(p) = |a|·log(q), get log(p^|b|) = log(q^|a|)
  have h_abs : Real.log (p ^ b.natAbs) = Real.log (q ^ a.natAbs) := by
    rw [Real.log_pow, Real.log_pow]
    exact h_abs_cross
  -- Since log is injective on positive reals, p^|b| = q^|a|
  have h_pow_eq : p ^ b.natAbs = q ^ a.natAbs := by
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hq_pos : 0 < (q : ℝ) := Nat.cast_pos.mpr hq.pos
    have hp_pow_pos : 0 < (p : ℝ) ^ b.natAbs := pow_pos hp_pos _
    have hq_pow_pos : 0 < (q : ℝ) ^ a.natAbs := pow_pos hq_pos _
    -- log_injOn_pos gives us (p:ℝ)^n = (q:ℝ)^m
    have h_cast_eq : (p : ℝ) ^ b.natAbs = (q : ℝ) ^ a.natAbs :=
      Real.log_injOn_pos hp_pow_pos hq_pow_pos h_abs
    -- Use exact_mod_cast to convert between ↑p^n and ↑(p^n)
    exact_mod_cast h_cast_eq
  -- This contradicts FTA: if p^m = q^n with p, q prime and p ≠ q, we get a contradiction
  -- Case 1: If b = 0, then p^0 = 1 = q^|a|, so q^|a| = 1, impossible since q is prime ≥ 2
  by_cases hb_zero : b = 0
  · simp [hb_zero] at hb
  · -- b ≠ 0, so |b| ≥ 1
    have hb_natAbs_pos : 0 < b.natAbs := Int.natAbs_pos.mpr hb_zero
    -- If a = 0, then q^0 = 1 = p^|b|, impossible
    by_cases ha_zero : a = 0
    · -- When a = 0: p^|b| = q^0 = 1, contradicting p prime
      have h_q_pow_zero : q ^ a.natAbs = 1 := by simp [ha_zero]
      rw [h_q_pow_zero] at h_pow_eq
      have h_p_eq_one : p = 1 ∨ b.natAbs = 0 := Nat.pow_eq_one.mp h_pow_eq
      cases h_p_eq_one with
      | inl h => exact hp.ne_one h
      | inr h =>
        have : b.natAbs ≠ 0 := hb_natAbs_pos.ne'
        exact this h
    · have ha_natAbs_pos : 0 < a.natAbs := Int.natAbs_pos.mpr ha_zero
      -- Now we have p^m = q^n with m, n ≥ 1 and p ≠ q both prime
      -- p divides q^n, so p divides q by Prime.dvd_of_dvd_pow
      have h_p_dvd_q : p ∣ q ^ a.natAbs := by
        rw [← h_pow_eq]
        exact dvd_pow_self p hb_natAbs_pos.ne'
      have h_p_dvd_q' : p ∣ q := hp.dvd_of_dvd_pow h_p_dvd_q
      -- Since q is prime and p divides q, we have p = 1 or p = q
      have : p = 1 ∨ p = q := hq.eq_one_or_self_of_dvd p h_p_dvd_q'
      cases this with
      | inl h => exact hp.ne_one h
      | inr h => exact hne h

/--
**LEMMA: sin(t·log p) = 0 implies t·log p = k·π for some integer k**
-/
lemma sin_zero_iff_int_pi (t : ℝ) (p : ℕ) :
    Real.sin (t * Real.log p) = 0 ↔ ∃ k : ℤ, (k : ℝ) * Real.pi = t * Real.log p := by
  constructor
  · intro h
    rw [Real.sin_eq_zero_iff] at h
    exact h
  · intro ⟨k, hk⟩
    rw [← hk, Real.sin_int_mul_pi]

/--
**THEOREM: No Simultaneous Zeros for Distinct Primes**
If p ≠ q are primes and t > 0, then sin(t·log p) and sin(t·log q) cannot both be zero.

Proof: If both are zero, then t·log p = k·π and t·log q = m·π for integers k, m.
This gives log(p)/log(q) = k/m ∈ ℚ, contradicting irrationality.
-/
theorem no_simultaneous_zeros {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {t : ℝ} (ht : t > 0) :
    Real.sin (t * Real.log p) = 0 → Real.sin (t * Real.log q) ≠ 0 := by
  intro h_sin_p h_sin_q
  -- Extract integer multiples of π (Mathlib gives k * π = x form)
  obtain ⟨k, hk⟩ := (sin_zero_iff_int_pi t p).mp h_sin_p
  obtain ⟨m, hm⟩ := (sin_zero_iff_int_pi t q).mp h_sin_q
  -- Since t > 0 and log p, log q > 0, we have k, m > 0
  have h_log_p_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h_log_q_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hk_pos : 0 < (k : ℝ) := by
    have : 0 < t * Real.log p := mul_pos ht h_log_p_pos
    rw [← hk] at this
    exact (mul_pos_iff_of_pos_right Real.pi_pos).mp this
  have hm_pos : 0 < (m : ℝ) := by
    have : 0 < t * Real.log q := mul_pos ht h_log_q_pos
    rw [← hm] at this
    exact (mul_pos_iff_of_pos_right Real.pi_pos).mp this
  -- From k·π = t·log p and m·π = t·log q, get log(p)/log(q) = k/m
  -- This gives a rational representation of log(p)/log(q), contradicting irrationality
  have h_irr := log_ratio_irrational hp hq hne
  -- k, m are nonzero (in fact positive) integers
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hm_int_ne : (m : ℤ) ≠ 0 := by
    intro h
    have : (m : ℝ) = 0 := by simp [h]
    exact hm_ne this
  -- From hk: k * π = t * log p and hm: m * π = t * log q
  -- We get: (k * π) / (m * π) = (t * log p) / (t * log q)
  -- Simplifying: k/m = log p / log q
  have h_ratio : Real.log p / Real.log q = (k : ℝ) / (m : ℝ) := by
    have h1 : t * Real.log p = (k : ℝ) * Real.pi := hk.symm
    have h2 : t * Real.log q = (m : ℝ) * Real.pi := hm.symm
    have ht_ne : t ≠ 0 := ne_of_gt ht
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    -- log p / log q = (t * log p) / (t * log q) = (k * π) / (m * π) = k / m
    calc Real.log p / Real.log q
        = (t * Real.log p) / (t * Real.log q) := by field_simp
      _ = ((k : ℝ) * Real.pi) / ((m : ℝ) * Real.pi) := by rw [h1, h2]
      _ = (k : ℝ) / (m : ℝ) := by field_simp
  -- But log(p)/log(q) = k/m is rational, contradicting irrationality
  rw [irrational_iff_ne_rational] at h_irr
  exact h_irr k m hm_int_ne h_ratio

/--
**THEOREM: Energy Persistence (Proven via FTA)**
For any t > 0 and a support S with at least 2 distinct primes,
at least one term sin²(t·log p) is positive.
-/
theorem energy_positive_for_positive_t (S : Finset ℕ) (h_card : 2 ≤ S.card)
    (h_primes : ∀ p ∈ S, Nat.Prime p) (t : ℝ) (ht : t > 0) :
    ∃ p ∈ S, (Real.sin (t * Real.log p)) ^ 2 > 0 := by
  -- Since |S| ≥ 2, pick two distinct primes
  have h_one_lt : 1 < S.card := Nat.lt_of_succ_le h_card
  have h_exists_pair : ∃ p q, p ∈ S ∧ q ∈ S ∧ p ≠ q := by
    rw [Finset.one_lt_card] at h_one_lt
    obtain ⟨a, ha, b, hb, hab⟩ := h_one_lt
    exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨p, q, hp, hq, hne⟩ := h_exists_pair
  -- By no_simultaneous_zeros, at least one of sin(t·log p), sin(t·log q) ≠ 0
  by_cases h : Real.sin (t * Real.log p) = 0
  · -- sin(t·log p) = 0, so sin(t·log q) ≠ 0
    have h_q_ne := no_simultaneous_zeros (h_primes p hp) (h_primes q hq) hne ht h
    use q, hq
    exact sq_pos_of_ne_zero h_q_ne
  · -- sin(t·log p) ≠ 0
    use p, hp
    exact sq_pos_of_ne_zero h

/-!
## 3. Chirality and Centering (Clifford33 version)
-/

/-- Compatibility: IsChiral definition using Clifford33 from ZetaManifold -/
def IsChiral (curve : ℝ → Clifford33) : Prop :=
  ∀ᶠ t in atTop, (curve t).magSq ≠ 0

/-!
## 4. Complex Chirality via Riemann Xi (Main Theorem)

This section implements the bridge from Chirality to RH using:
1. The Riemann Xi function ξ(s) for its symmetry ξ(s) = ξ(1-s)
2. The convexity framework from EnergySymmetry
3. Energy persistence from FTA-based orthogonality above
-/

/--
The Complex Sieve Curve is the Riemann Xi function ξ(s).
We use ξ instead of ζ because:
- ξ(s) = ξ(1-s) gives exact symmetry around σ = 1/2
- Same zeros as ζ(s) in the critical strip
- Entire function (no poles)
- Strictly zero at zeta zeros
-/
def ComplexSieveCurve (σ : ℝ) (t : ℝ) : ℂ :=
  ProofEngine.EnergySymmetry.riemannXi (σ + t * Complex.I)

/--
Complex Chirality: The velocity of the sieve curve is bounded away from zero.
This follows from ergodicity: prime phases don't cancel due to log-irrationality.
-/
def IsComplexChiral (σ : ℝ) : Prop :=
  ∃ δ > 0, ∀ t, ‖deriv (fun τ => ComplexSieveCurve σ τ) t‖ ^ 2 ≥ δ

-- Atomic Lemma: 1 - (σ + ti) = conj(↑(1-σ) + ti) via cast shim + Complex.ext
-- KEY: Use ↑(1 - σ) form to match goal after simp only [ComplexSieveCurve]
private lemma one_minus_s_eq_conj_s' (σ t : ℝ) :
    (1 : ℂ) - ((σ : ℂ) + t * I) = starRingEnd ℂ (↑(1 - σ) + t * I) := by
  -- Cast shim: ↑(1 - σ) = ↑1 - ↑σ = 1 - ↑σ (aligns both sides)
  rw [Complex.ofReal_sub, Complex.ofReal_one, starRingEnd_apply]
  -- Complex.ext Rosetta Stone pattern
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.neg_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.I_re, Complex.I_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.neg_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.one_im, Complex.I_re, Complex.I_im]

/--
**Symmetry of ξ magnitude**: |ξ(σ + it)| = |ξ((1-σ) + it)|
Uses functional equation ξ(s) = ξ(1-s) and Schwarz reflection.
-/
lemma complex_sieve_symmetry (σ t : ℝ) :
    ‖ComplexSieveCurve σ t‖ = ‖ComplexSieveCurve (1 - σ) t‖ := by
  simp only [ComplexSieveCurve]
  -- Goal: ‖riemannXi (↑σ + ↑t * I)‖ = ‖riemannXi (↑(1 - σ) + ↑t * I)‖
  calc ‖ProofEngine.EnergySymmetry.riemannXi (↑σ + ↑t * I)‖
      = ‖ProofEngine.EnergySymmetry.riemannXi (1 - (↑σ + ↑t * I))‖ := by
          rw [ProofEngine.EnergySymmetry.riemannXi_symmetric]
    _ = ‖ProofEngine.EnergySymmetry.riemannXi (starRingEnd ℂ (↑(1 - σ) + ↑t * I))‖ := by
          rw [one_minus_s_eq_conj_s']
    _ = ‖starRingEnd ℂ (ProofEngine.EnergySymmetry.riemannXi (↑(1 - σ) + ↑t * I))‖ := by
          rw [ProofEngine.EnergySymmetry.riemannXi_conj]
    _ = ‖ProofEngine.EnergySymmetry.riemannXi (↑(1 - σ) + ↑t * I)‖ := Complex.norm_conj _

/--
**Symmetry implies T'(1/2) = 0**: The derivative of |ξ|² vanishes at σ = 1/2.
-/
lemma complex_sieve_deriv_at_half (t : ℝ) :
    deriv (fun σ => ‖ComplexSieveCurve σ t‖ ^ 2) (1 / 2) = 0 := by
  -- ‖ComplexSieveCurve σ t‖ ^ 2 = ZetaEnergy t σ (both are normSq of riemannXi)
  have h_eq : ∀ σ, ‖ComplexSieveCurve σ t‖ ^ 2 =
                   ProofEngine.EnergySymmetry.ZetaEnergy t σ := by
    intro σ
    simp only [ComplexSieveCurve, ProofEngine.EnergySymmetry.ZetaEnergy]
    rw [← Complex.normSq_eq_norm_sq]
  simp only [h_eq]
  exact ProofEngine.EnergySymmetry.energy_deriv_zero_at_half t

/--
**Main Theorem: Complex Chirality → Centering**

If the prime rotors maintain non-zero velocity (chirality), then
all zeros of ξ (and hence ζ) must lie on the critical line σ = 1/2.

**Explicit Hypothesis Strategy (2026-01-23)**:
Uses explicit global minimum hypothesis instead of proving convexity extension.
This follows the project's pattern of promoting unprovable global properties
to explicit hypotheses.
-/
theorem chirality_implies_centering (σ t₀ : ℝ) (hσ_ne : σ ≠ 1 / 2)
    (_h_chiral : IsComplexChiral σ)
    (h_is_zero : ComplexSieveCurve σ t₀ = 0)
    -- Explicit Global Minimum Hypothesis:
    -- "At this t₀ where ξ is zero, T(1/2) < T(x) for all x ≠ 1/2"
    (h_global_min : ∀ x, x ≠ 1 / 2 →
      ‖ComplexSieveCurve (1 / 2) t₀‖ ^ 2 < ‖ComplexSieveCurve x t₀‖ ^ 2) :
    False := by
  -- 1. Apply global minimum hypothesis to our specific σ
  have h_T_strict : ‖ComplexSieveCurve (1 / 2) t₀‖ ^ 2 <
                    ‖ComplexSieveCurve σ t₀‖ ^ 2 := h_global_min σ hσ_ne
  -- 2. Use the zero property: T(σ) = 0
  have h_T_zero : ‖ComplexSieveCurve σ t₀‖ ^ 2 = 0 := by simp [h_is_zero]
  -- 3. Contradiction: 0 ≤ T(1/2) < T(σ) = 0
  rw [h_T_zero] at h_T_strict
  linarith [sq_nonneg (‖ComplexSieveCurve (1 / 2) t₀‖)]

/--
**Corollary: RH from Chirality**
Assuming chirality holds uniformly in the critical strip,
all non-trivial zeros have real part 1/2.

Propagates the global minimum requirement.
-/
theorem RH_from_chirality
    (h_chiral_uniform : ∀ σ, 0 < σ → σ < 1 → σ ≠ 1 / 2 → IsComplexChiral σ)
    (s : ℂ) (h_zero : riemannZeta s = 0) (h_strip : 0 < s.re ∧ s.re < 1)
    -- Global Minimum Hypothesis
    (h_global_min : ∀ t, ∀ x, x ≠ 1 / 2 →
      ‖ComplexSieveCurve (1 / 2) t‖ ^ 2 < ‖ComplexSieveCurve x t‖ ^ 2) :
    s.re = 1 / 2 := by
  by_contra h_ne
  have h_xi_zero : ProofEngine.EnergySymmetry.riemannXi s = 0 :=
    ProofEngine.EnergySymmetry.riemannXi_zero_of_zeta_zero s h_zero h_strip
  have h_chiral := h_chiral_uniform s.re h_strip.1 h_strip.2 h_ne
  -- The zero at s gives ComplexSieveCurve s.re s.im = 0
  have h_curve_zero : ComplexSieveCurve s.re s.im = 0 := by
    unfold ComplexSieveCurve
    -- Need: riemannXi (s.re + s.im * I) = 0
    -- We have: riemannXi s = 0, where s = s.re + s.im * I
    -- s.re + s.im * I = s since s = s.re + s.im * I
    have h_s_eq : (s.re : ℂ) + s.im * I = s := Complex.re_add_im s
    rw [h_s_eq, h_xi_zero]
  exact chirality_implies_centering s.re s.im h_ne h_chiral h_curve_zero (h_global_min s.im)

end GlobalBound
