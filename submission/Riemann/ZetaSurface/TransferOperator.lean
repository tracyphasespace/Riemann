/-
# Transfer Operator (Pre-Completion)

**Purpose**: Define the basic weighted sum operator over primes before completion.

## Key Results

1. Weight α(s,p) = p^{-s} for forward shifts
2. Basic operator: A_s = Σ_p α(s,p) · T_p
3. This is NOT self-adjoint; completion is needed for functional equation symmetry

## Architecture Note (Cl33 Refactoring)

This module provides both:
- **Cl33 version**: Uses SpectralParam from Cl33Ops with Clifford algebra weights
- **Complex version**: Legacy interface for backward compatibility

The Cl33 weights decompose α(s,p) = p^{-σ} · (cos(t·log p) - B·sin(t·log p))
where B is the bivector from Cl(3,3) with B² = -1.

## Connection to Zeta Function

The logarithmic derivative of ζ(s) involves sums over prime powers:
  -ζ'(s)/ζ(s) = Σ_p Σ_k log(p) · p^{-ks}

Our transfer operator captures the prime structure. The completion
(adding backward shifts with appropriate weights) will give the
adjoint symmetry matching the functional equation.

## References

- PrimeShifts.lean (prime shift operators)
- Translations.lean (base operators)
- Riemann/GA/Cl33Ops.lean (Clifford algebra weights)
-/

import Riemann.ZetaSurface.PrimeShifts
import Riemann.GA.Cl33Ops
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
open scoped Real ComplexConjugate
open MeasureTheory
open Riemann.GA
open Riemann.GA.Ops
open Complex

namespace Riemann.ZetaSurface

/-! ## 1. Weight Functions (Cl33 - Primary) -/

/--
The cosine component of the Cl33 weight.
This is the "real" part: p^{-σ} · cos(t · log p)
-/
def αCos (s : SpectralParam) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-s.sigma) * Real.cos (s.t * Real.log p)

/--
The sine component of the Cl33 weight.
This is the "imaginary" part: p^{-σ} · sin(t · log p)
-/
def αSin (s : SpectralParam) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-s.sigma) * Real.sin (s.t * Real.log p)

/--
Single-prime contribution to the transfer operator on real Hilbert space.

On HR × HR (representing complex via the 2×2 matrix action):
  A_{s,p} acts as [ αCos(s,p)  -αSin(s,p) ] · T_p
                  [ αSin(s,p)   αCos(s,p) ]

For simplicity, we define the scalar action on HR here.
-/
def AtermCos (s : SpectralParam) (p : ℕ) : HR →L[ℝ] HR :=
  (αCos s p) • (TprimeR p).toContinuousLinearMap

def AtermSin (s : SpectralParam) (p : ℕ) : HR →L[ℝ] HR :=
  (αSin s p) • (TprimeR p).toContinuousLinearMap

/-! ## 2. Weight Functions (Complex - Legacy) -/

/--
The forward weight for prime p at parameter s.
α(s, p) = p^{-s}
-/
def α (s : ℂ) (p : ℕ) : ℂ :=
  (p : ℂ) ^ (-s)

/--
Weight at s = 1/2 + it has modulus p^{-1/2}.
-/
theorem α_modulus_critical (p : ℕ) (hp : Nat.Prime p) (t : ℝ) :
    ‖α (1/2 + t * I) p‖ = Real.rpow p (-1/2 : ℝ) := by
  unfold α
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have h : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
  rw [h, norm_cpow_eq_rpow_re_of_pos hp_pos]
  -- Goal: (↑p).rpow (-(1/2 + ↑t * I)).re = (↑p).rpow (-1/2)
  -- re(-(1/2 + t*I)) = -1/2 - re(t*I) = -1/2 - 0 = -1/2
  congr 1
  simp only [neg_add_rev, add_re, neg_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
             mul_zero, sub_zero, mul_one, one_div]
  norm_num

/--
Weight decomposes into modulus and phase on critical line.
-/
theorem α_decomposition_critical (p : ℕ) (hp : Nat.Prime p) (t : ℝ) :
    α (1/2 + t * I) p =
    (Real.rpow p (-1/2 : ℝ) : ℂ) * Complex.exp (-I * t * Real.log p) := by
  unfold α
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  -- Split the exponent: -(1/2 + t*I) = -1/2 + (-t*I)
  rw [neg_add, cpow_add _ _ hp_ne]
  -- p^{-1/2} as real
  have h1 : (p : ℂ) ^ (-(1 / 2) : ℂ) = (Real.rpow p (-1/2 : ℝ) : ℂ) := by
    have key : ((p : ℝ) : ℂ) ^ (((-1/2 : ℝ)) : ℂ) = ((Real.rpow (p : ℝ) (-1/2 : ℝ)) : ℂ) :=
      (Complex.ofReal_cpow hp_pos.le _).symm
    simp only [ofReal_natCast] at key
    convert key using 2
    simp only [one_div]
    norm_num
  -- p^{-t*I} = exp(-t*I*log p)
  have h2 : (p : ℂ) ^ (-(↑t * I)) = exp (-I * ↑t * ↑(Real.log p)) := by
    rw [cpow_def_of_ne_zero hp_ne]
    have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast, Complex.ofReal_log hp_pos.le]
    rw [hlog]
    ring_nf
  rw [h1, h2]

/-! ## 2. Basic Transfer Operator (Forward Only) -/

/--
Single-prime contribution to the transfer operator.
A_{s,p} = α(s,p) · T_p
-/
def Aterm (s : ℂ) (p : ℕ) : H →L[ℂ] H :=
  (α s p) • (Tprime p).toContinuousLinearMap

/--
Basic transfer operator: sum over primes up to B.
A_{s,B} = Σ_{p ≤ B prime} α(s,p) · T_p
-/
def A (s : ℂ) (B : ℕ) : H →L[ℂ] H := by
  classical
  exact (primesUpTo B).sum (fun p => Aterm s p)

/-! ## 3. Adjoint of Basic Operator -/

/--
Adjoint of single-prime term.
(α · T_p)† = conj(α) · T_p†  = conj(α) · T_p⁻¹
-/
theorem Aterm_adjoint (s : ℂ) (p : ℕ) :
    (Aterm s p).adjoint =
    (conj (α s p)) • (TprimeInv p).toContinuousLinearMap := by
  unfold Aterm
  rw [map_smulₛₗ ContinuousLinearMap.adjoint]
  simp only [starRingEnd_apply]
  rw [Tprime_adjoint]

/-
**Note: Adjoint Asymmetry**

The adjoint of the basic operator is NOT A(s) for any s.
This shows completion is necessary.

A(s)† = Σ_p conj(α(s,p)) · T_p⁻¹ ≠ A(s') for any s'

The forward-only operator lacks the symmetry for the functional equation.
-/

/-! ## 4. Critical Line Properties -/

/--
On the critical line σ = 1/2, weights have uniform modulus decay.
All α(1/2 + it, p) have modulus p^{-1/2}.
-/
theorem weights_uniform_modulus (t : ℝ) (p : ℕ) (hp : Nat.Prime p) :
    ‖α (1/2 + t * I) p‖ = Real.rpow p (-1/2 : ℝ) := by
  exact α_modulus_critical p hp t

/--
The phase of weights on the critical line encodes the "frequency" t.
Phase of α(1/2 + it, p) = -t · log(p)
-/
theorem weights_phase_critical (t : ℝ) (p : ℕ) (hp : Nat.Prime p)
    (ht : -t * Real.log p ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg (α (1/2 + t * I) p) = -t * Real.log p := by
  -- Use the decomposition: α = (positive real) * exp(-i*t*log p)
  rw [α_decomposition_critical p hp t]
  -- α = (positive real) * exp(-I * t * log p)
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hrpow_pos : 0 < Real.rpow p (-1/2 : ℝ) := Real.rpow_pos_of_pos hp_pos _
  -- Rewrite exp to match the standard form exp(θ * I)
  have h_exp : Complex.exp (-I * ↑t * ↑(Real.log p)) = Complex.exp (↑(-t * Real.log p) * I) := by
    congr 1
    push_cast
    ring
  rw [h_exp]
  -- arg(r * z) = arg(z) for r > 0
  rw [Complex.arg_real_mul _ hrpow_pos]
  -- exp(θ * I) = cos θ + sin θ * I
  rw [Complex.exp_mul_I]
  -- arg(cos θ + sin θ * I) = θ when θ ∈ (-π, π]
  exact Complex.arg_cos_add_sin_mul_I ht

/-! ## 5. Why Completion is Needed -/

/-
The basic operator A(s) = Σ_p p^{-s} · T_p has adjoint
  A(s)† = Σ_p p^{-conj(s)} · T_p⁻¹

For the functional equation symmetry, we want:
  K(s)† = K(1 - conj(s))

The solution is to add backward shifts:
  K(s) = Σ_p [ α(s,p) · T_p + β(s,p) · T_p⁻¹ ]

where β is chosen so that taking adjoint swaps α ↔ β appropriately.

Two approaches:
1. Kernel completion (CompletionKernel.lean): Choose β algebraically
2. Measure completion (CompletionMeasure.lean): Change the Hilbert space

Both achieve K(s)† = K(1 - conj(s)).
-/

/-! ## Physical Summary

The basic transfer operator captures the prime structure of ζ(s):

1. **Weights**: Each prime p contributes with weight p^{-s}
2. **Shifts**: Each prime shifts by log(p) in log-space
3. **Critical line**: At σ = 1/2, weights have uniform decay p^{-1/2}
4. **Asymmetry**: The forward-only operator lacks functional equation symmetry

The completion (adding backward shifts) restores the symmetry needed
to connect operator spectrum to zeta zeros.
-/

end Riemann.ZetaSurface

end