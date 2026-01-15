/-
# Surface Tension for Measure Model: The Concrete Rayleigh Identity

**Purpose**: Provide the concrete implementation of the Surface Tension
hypothesis for the Measure Completion model. This bridges the abstract
`SurfaceTensionHypothesis` structure with the explicit `Kw` operator.

## Key Insight

The B-coefficient (bivector part) of the Rayleigh quotient ⟨v, Kw(s)v⟩ is
controlled by the deviation from the critical line:

  B-coeff⟨v, Kw(s)v⟩ = (Re(s) - 1/2) · Q_B(v)

where Q_B(v) > 0 for nonzero v. This makes the "Hammer" a one-line algebraic
consequence: real eigenvalue → B-coeff = 0 → (σ - 1/2) · Q = 0 → σ = 1/2.

**Cl(N,N) Framework**: In code, we use Lean's `.im` accessor, but conceptually
this is the B-coefficient under the isomorphism Span{1,B} ≅ ℂ where B² = -1.
Everything in Cl(N,N) is real - see `RayleighBridge.lean` for details.

## Mathematical Content

The Tension Operator T(B) captures the log(p)-weighted prime contributions:
  T(B) = ∑_{p ≤ B} log(p) · [derivative terms]

The quadratic form is Q_B(v) = ⟨v, T(B)v⟩ (real part).

## References

- SpectralReal.lean: SurfaceTensionHypothesis structure
- CompletionMeasure.lean: Kw operator and infrastructure
- CompletionCore.lean: CompletedModel interface
-/

import Riemann.ZetaSurface.CompletionMeasure
import Riemann.ZetaSurface.SpectralReal

noncomputable section
open scoped Real ComplexConjugate
open MeasureTheory
open Complex
open Riemann.ZetaSurface
open Riemann.ZetaSurface.CompletionMeasure
open Riemann.ZetaSurface.Spectral

namespace Riemann.ZetaSurface.SurfaceTensionMeasure

variable {w : Weight} [AdmitsUnitaryTranslation w]

/-! ## 1. The Tension Operator Component -/

/--
The log-weight for a prime p.
This is the derivative factor in the p^{-s} expansion.
-/
def logWeight (p : ℕ) : ℝ := Real.log p

/--
Single-prime Tension Term on Hw(w).
This is the operator that contributes to the imaginary part of the Rayleigh quotient.

The tension comes from the log(p) factor in differentiating p^{-s} with respect to σ.
-/
def KwTensionTerm (s : ℂ) (p : ℕ) : Hw w →L[ℂ] Hw w :=
  let logp := (Real.log p : ℂ)
  -- T_p = log(p) · (α(s,p) · T_p - β(s,p) · T_p^{-1})
  (logp * α s p) • (Twprime w p).toContinuousLinearMap -
  (logp * β s p) • (TwprimeInv w p).toContinuousLinearMap

/--
The Total Surface Tension Operator T(B).
Sum over primes up to B of the log-weighted terms.
-/
def KwTension (s : ℂ) (B : ℕ) : Hw w →L[ℂ] Hw w := by
  classical
  exact (primesUpTo B).sum (fun p => KwTensionTerm s p)

/-! ## 2. The Quadratic Form Q_B (Pattern 3: Sum of Squared Norms) -/

/--
The Quadratic Form Q_B(v) for the Surface Tension hypothesis.

Defined as a weighted sum of squared norms of shifted vectors:
  Q_B(v) = Σ_{p ≤ B} log(p) · ‖T_p v‖²

where T_p is the unitary prime shift operator.

Since T_p is an isometry, ‖T_p v‖ = ‖v‖, so this simplifies to:
  Q_B(v) = (Σ_{p ≤ B} log(p)) · ‖v‖²

This form is manifestly positive for v ≠ 0 since:
- log(p) > 0 for all primes p ≥ 2
- ‖v‖² > 0 for v ≠ 0

The connection to the Rayleigh identity comes from the derivative
structure of p^{-s} with respect to σ.
-/
def KwQuadraticForm (B : ℕ) (v : Hw w) : ℝ := by
  classical
  exact (primesUpTo B).sum (fun p => logWeight p * ‖(Twprime w p) v‖^2)

/--
Log of a prime ≥ 2 is positive.
-/
theorem logWeight_pos (p : ℕ) (hp : Nat.Prime p) : 0 < logWeight p := by
  unfold logWeight
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 < (p : ℝ) := by
    have h1 : (1 : ℝ) < 2 := one_lt_two
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact Nat.ofNat_le_cast.mpr hp2
    linarith
  exact Real.log_pos hp1

/--
**Positivity of the Quadratic Form**: Q_B(v) > 0 for nonzero v when B ≥ 2.

Proof: Each term log(p) · ‖T_p v‖² is non-negative, and since T_p is an isometry,
‖T_p v‖ = ‖v‖ > 0. There is at least one prime p ≤ B with log(p) > 0,
so the sum is strictly positive.
-/
theorem KwQuadraticForm_pos (B : ℕ) (hB : 2 ≤ B) (v : Hw w) (hv : v ≠ 0) :
    0 < KwQuadraticForm B v := by
  classical
  unfold KwQuadraticForm
  -- v ≠ 0 implies ‖v‖ > 0
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hv_sq : 0 < ‖v‖^2 := sq_pos_of_pos hv_norm
  -- Twprime is an isometry, so ‖(Twprime w p) v‖ = ‖v‖
  have h_isometry : ∀ p, ‖(Twprime w p) v‖ = ‖v‖ := fun p => (Twprime w p).norm_map v
  -- 2 is prime and 2 ≤ B, so 2 ∈ primesUpTo B
  have h2_prime : Nat.Prime 2 := Nat.prime_two
  have h2_mem : 2 ∈ primesUpTo B := by
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hB, h2_prime⟩
  -- log(2) > 0
  have hlog2 : 0 < logWeight 2 := logWeight_pos 2 h2_prime
  -- The term for p = 2 is strictly positive: log(2) * ‖T_2 v‖² = log(2) * ‖v‖² > 0
  have h2_pos : 0 < logWeight 2 * ‖(Twprime w 2) v‖^2 := by
    rw [h_isometry 2]
    exact mul_pos hlog2 hv_sq
  -- All terms are non-negative
  have h_nonneg : ∀ p ∈ primesUpTo B, 0 ≤ logWeight p * ‖(Twprime w p) v‖^2 := by
    intro p hp
    simp only [primesUpTo, Finset.mem_filter] at hp
    have hp_prime := hp.2
    have hlogp : 0 < logWeight p := logWeight_pos p hp_prime
    rw [h_isometry p]
    exact mul_nonneg (le_of_lt hlogp) (sq_nonneg _)
  -- Sum with one positive term and all non-negative terms is positive
  exact Finset.sum_pos' h_nonneg ⟨2, h2_mem, h2_pos⟩

/-! ## 3. The Rayleigh Identity Structure -/

/--
**The Rayleigh Identity Structure**: Encapsulates the proof that
Im⟨v, Kw(s)v⟩ = (Re(s) - 1/2) · Q_B(v).

This is made into a conditional structure because proving it requires
careful analysis of the prime weight contributions.
-/
structure RayleighIdentity (w : Weight) [AdmitsUnitaryTranslation w] where
  /-- The identity holds for all s, B, v -/
  identity : ∀ (s : ℂ) (B : ℕ) (v : Hw w),
    (@inner ℂ (Hw w) _ v (Kw w s B v)).im =
    (s.re - 1/2) * KwQuadraticForm B v

/--
**Theorem**: Given the Rayleigh identity, we can prove the one-line Hammer.
If Kw(s)v = ev·v with ev ∈ ℝ and v ≠ 0, then Re(s) = 1/2.

Note: Requires B ≥ 2 for positivity (Fix B domain).
-/
theorem Real_Eigenvalue_Implies_Critical_of_Rayleigh
    (RI : RayleighIdentity w)
    (hQ_pos : ∀ B : ℕ, 2 ≤ B → ∀ v : Hw w, v ≠ 0 → 0 < KwQuadraticForm B v)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : Hw w) (hv : v ≠ 0)
    (h_eigen : Kw w s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := by
  -- Step 1: ⟨v, Kw(s)v⟩ = ev * ⟨v,v⟩ is real
  have h_rayleigh : @inner ℂ (Hw w) _ v (Kw w s B v) = (ev : ℂ) * @inner ℂ (Hw w) _ v v := by
    rw [h_eigen, inner_smul_right]
  -- Step 2: The imaginary part is zero (real * real = real)
  have h_im_zero : (@inner ℂ (Hw w) _ v (Kw w s B v)).im = 0 := by
    rw [h_rayleigh]
    have h_inner_im : RCLike.im (@inner ℂ (Hw w) _ v v) = 0 := inner_self_im v
    have h_inner_im' : (@inner ℂ (Hw w) _ v v).im = 0 := h_inner_im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h_inner_im',
               mul_zero, zero_mul, add_zero]
  -- Step 3: Apply Rayleigh identity: 0 = (Re(s) - 1/2) * Q_B(v)
  have h_ri := RI.identity s B v
  rw [h_im_zero] at h_ri
  -- Step 4: Q_B(v) > 0 since v ≠ 0 and B ≥ 2 (Fix B domain)
  have h_Q_pos : 0 < KwQuadraticForm B v := hQ_pos B hB v hv
  -- Step 5: (Re(s) - 1/2) * Q = 0 with Q > 0 implies Re(s) = 1/2
  have h_factor : s.re - 1/2 = 0 := by
    by_contra h_ne
    have : (s.re - 1/2) * KwQuadraticForm B v ≠ 0 := mul_ne_zero h_ne (ne_of_gt h_Q_pos)
    exact this h_ri.symm
  linarith

/-! ## 4. Positivity Structure (Legacy, Fix B Domain) -/

/--
**Positivity Structure**: Bundles the positivity requirement for B ≥ 2.
This is a legacy structure; prefer using KwQuadraticForm_pos directly.
-/
structure QuadraticFormPositivity (w : Weight) [AdmitsUnitaryTranslation w] where
  pos : ∀ B : ℕ, 2 ≤ B → ∀ v : Hw w, v ≠ 0 → 0 < KwQuadraticForm B v

/-! ## 4a. Proved Hammer Theorem -/

/--
**The Direct Hammer Theorem (Proved for B ≥ 2)**.

If Kw(s)v = ev·v with ev ∈ ℝ, v ≠ 0, B ≥ 2, and the Rayleigh identity holds,
then Re(s) = 1/2.

This is the "one-line Hammer" with proved positivity - the key step uses:
1. Real eigenvalue ⟹ Im⟨v, Kw(s)v⟩ = 0
2. Rayleigh identity: Im⟨v, Kw(s)v⟩ = (σ - 1/2) · Q_B(v)
3. Proved positivity: Q_B(v) > 0 for v ≠ 0, B ≥ 2
4. Therefore: σ = 1/2
-/
theorem Real_Eigenvalue_Implies_Critical_Proved
    (RI : RayleighIdentity w)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : Hw w) (hv : v ≠ 0)
    (h_eigen : Kw w s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := by
  -- Step 1: ⟨v, Kw(s)v⟩ = ev * ⟨v,v⟩ is real
  have h_rayleigh : @inner ℂ (Hw w) _ v (Kw w s B v) = (ev : ℂ) * @inner ℂ (Hw w) _ v v := by
    rw [h_eigen, inner_smul_right]
  -- Step 2: The imaginary part is zero (real * real = real)
  have h_im_zero : (@inner ℂ (Hw w) _ v (Kw w s B v)).im = 0 := by
    rw [h_rayleigh]
    have h_inner_im : RCLike.im (@inner ℂ (Hw w) _ v v) = 0 := inner_self_im v
    have h_inner_im' : (@inner ℂ (Hw w) _ v v).im = 0 := h_inner_im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h_inner_im',
               mul_zero, zero_mul, add_zero]
  -- Step 3: Apply Rayleigh identity: 0 = (Re(s) - 1/2) * Q_B(v)
  have h_ri := RI.identity s B v
  rw [h_im_zero] at h_ri
  -- Step 4: Q_B(v) > 0 since v ≠ 0 and B ≥ 2 (PROVED, not assumed)
  have h_Q_pos : 0 < KwQuadraticForm B v := KwQuadraticForm_pos B hB v hv
  -- Step 5: (Re(s) - 1/2) * Q = 0 with Q > 0 implies Re(s) = 1/2
  have h_factor : s.re - 1/2 = 0 := by
    by_contra h_ne
    have : (s.re - 1/2) * KwQuadraticForm B v ≠ 0 := mul_ne_zero h_ne (ne_of_gt h_Q_pos)
    exact this h_ri.symm
  linarith

/-! ## 5. Building the MeasureModel -/

/--
Construct a CompletedModel from a weight with unitary translations.
-/
def MeasureModel (w : Weight) [AdmitsUnitaryTranslation w] : CompletedModel where
  H := Hw w
  instNormedAddCommGroup := inferInstance
  instInner := inferInstance
  instComplete := inferInstance
  Op := fun s B => Kw w s B
  adjoint_symm := fun s B => Kw_adjoint_symm w s B
  normal_on_critical := by
    intro t B
    -- On the critical line, Kw is self-adjoint (from Kw_selfadjoint_half generalized)
    -- For self-adjoint operators, Op† * Op = Op * Op†
    simp only []
    have h_sa : (Kw w ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint =
                Kw w ((1/2 : ℂ) + (t : ℂ) * I) B := by
      rw [Kw_adjoint_symm]
      congr 1
      -- 1 - conj(1/2 + t*I) = 1 - (1/2 - t*I) = 1/2 + t*I
      apply Complex.ext
      · simp only [sub_re, one_re, conj_re, add_re, ofReal_re, mul_re,
                   ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero]
        norm_num
      · simp only [sub_im, one_im, conj_im, add_im, ofReal_im, mul_im,
                   ofReal_re, I_re, mul_zero, I_im, mul_one, add_zero]
        ring
    -- Self-adjoint implies normal: Op† * Op = Op * Op†
    rw [h_sa]

/-! ## 6. Instantiating SurfaceTensionHypothesis -/

/--
**Conditional SurfaceTensionHypothesis for MeasureModel**.

Given the Rayleigh identity, we can instantiate SurfaceTensionHypothesis.
The positivity for B ≥ 2 is now proved directly via KwQuadraticForm_pos.
-/
def MeasureModelSurfaceTension
    (RI : RayleighIdentity w) :
    SurfaceTensionHypothesis (MeasureModel w) where

  quadraticForm := fun B v => KwQuadraticForm B v

  quadraticForm_pos := fun B hB v hv => KwQuadraticForm_pos B hB v hv

  rayleigh_imaginary_part := fun s B v => RI.identity s B v

/-! ## 7. The Complete Logic Chain -/

/--
**Main Theorem**: With the Rayleigh identity,
we get the "Hammer" theorem for the MeasureModel (for B ≥ 2).
-/
theorem MeasureModel_Hammer
    (RI : RayleighIdentity w)
    (s : ℂ) (B : ℕ) (hB : 2 ≤ B) (ev : ℝ) (v : Hw w) (hv : v ≠ 0)
    (h_eigen : Kw w s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 :=
  Real_Eigenvalue_Implies_Critical_of_SurfaceTension
    (MeasureModel w)
    (MeasureModelSurfaceTension RI)
    s B hB ev v hv h_eigen

/-! ## Summary

The Surface Tension framework for MeasureModel provides:

1. **KwTension**: The concrete Tension operator T(B) from prime log-weights
2. **KwQuadraticForm**: The positive-definite form Q_B(v) = Σ_p log(p)·‖T_p v‖²
3. **KwQuadraticForm_pos**: Proved positivity for B ≥ 2 (Pattern 3 + Isometry)
4. **RayleighIdentity**: Structure encoding Im⟨v, Kw(s)v⟩ = (σ - 1/2)·Q_B(v)
5. **MeasureModelSurfaceTension**: Instantiation of SurfaceTensionHypothesis

The "Hammer" follows: real eigenvalue ev forces Q_B(v) > 0 with Im = 0,
so (σ - 1/2)·Q = 0 implies σ = 1/2.

**Status (Fix B)**:
- ✅ KwQuadraticForm_pos: Proved for B ≥ 2
- ✅ Real_Eigenvalue_Implies_Critical_Proved: Uses proved positivity
- 🔲 RayleighIdentity: To be proved from explicit weight formulas
-/

end Riemann.ZetaSurface.SurfaceTensionMeasure

end
