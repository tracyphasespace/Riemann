/-
# Adapter: QFD Ricker Wavelet → Riemann Namespace

**Purpose**: Bridge the QFD wavelet/soliton libraries into the Riemann namespace
for use in compression.

## Contents

1. Ricker "Mexican hat" wavelet definition
2. L² membership proofs
3. Wavelet atom construction (translation + dilation)

## Note

Some analytic proofs (Gaussian integrability) are marked sorry pending
alignment with exact Mathlib API signatures.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open scoped Real ENNReal
open MeasureTheory

namespace Riemann.Adapters.QFD

/-! ## 1. Ricker Wavelet Definition -/

/--
Base Ricker "Mexican hat" wavelet as a real function.
S(x) = (1 - x²) · exp(-x²/2)
-/
def rickerReal (x : ℝ) : ℝ :=
  (1 - x^2) * Real.exp (-(x^2) / 2)

/--
Complex-valued Ricker wavelet (for ℂ-linear operators).
-/
def ricker (x : ℝ) : ℂ := (rickerReal x : ℂ)

/-! ## 2. Basic Properties -/

theorem rickerReal_measurable : Measurable rickerReal := by
  unfold rickerReal
  exact (measurable_const.sub (measurable_id.pow_const 2)).mul
    (measurable_id.pow_const 2 |>.neg.div_const 2 |>.exp)

theorem ricker_measurable : Measurable ricker :=
  Complex.measurable_ofReal.comp rickerReal_measurable

theorem rickerReal_aestronglyMeasurable : AEStronglyMeasurable rickerReal volume :=
  rickerReal_measurable.aestronglyMeasurable

theorem ricker_aestronglyMeasurable : AEStronglyMeasurable ricker volume :=
  ricker_measurable.aestronglyMeasurable

/-! ## 3. L² Membership -/

/--
Ricker wavelet is in L²(ℝ).
The squared Ricker is (1 - 2x² + x⁴) · exp(-x²), which is integrable
as a polynomial times a Gaussian.
-/
theorem rickerReal_memLp2 : MemLp rickerReal 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq rickerReal_aestronglyMeasurable]
  unfold rickerReal
  -- |rickerReal x|² = (1-x²)² * exp(-x²)
  have h_sq : ∀ x : ℝ, ((1 - x ^ 2) * Real.exp (-(x ^ 2) / 2)) ^ 2 =
      (1 - x ^ 2) ^ 2 * Real.exp (-1 * (x ^ 2)) := by
    intro x
    rw [mul_pow, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [h_sq]
  -- Integrability of each Gaussian moment term
  have h1 : Integrable (fun x => Real.exp (-1 * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have h2 : Integrable (fun x => x ^ 2 * Real.exp (-1 * x ^ 2)) volume := by
    have hmain := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (-1 : ℝ) < 2)
    convert hmain using 1
    ext x; congr 1; exact (Real.rpow_natCast x 2).symm
  have h4 : Integrable (fun x => x ^ 4 * Real.exp (-1 * x ^ 2)) volume := by
    have hmain := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (-1 : ℝ) < 4)
    convert hmain using 1
    ext x; congr 1; exact (Real.rpow_natCast x 4).symm
  -- (1-x²)² = 1 - 2x² + x⁴, so (1-x²)² * exp(-x²) is a sum of integrable terms
  have h_expand : ∀ x : ℝ, (1 - x ^ 2) ^ 2 * Real.exp (-1 * x ^ 2) =
      Real.exp (-1 * x ^ 2) - 2 * (x ^ 2 * Real.exp (-1 * x ^ 2)) +
      x ^ 4 * Real.exp (-1 * x ^ 2) := by intro x; ring
  simp_rw [h_expand]
  exact (h1.sub (h2.const_mul 2)).add h4

theorem ricker_memLp2 : MemLp ricker 2 (volume : Measure ℝ) := by
  unfold ricker
  exact MemLp.ofReal rickerReal_memLp2

def rickerVec : Lp ℂ 2 (volume : Measure ℝ) :=
  ricker_memLp2.toLp ricker

/-! ## 4. Wavelet Atoms (Translation + Dilation) -/

def atomReal (a b : ℝ) (_hb : 0 < b) : ℝ → ℝ :=
  fun u => Real.sqrt b * rickerReal (b * u - a)

def atom (a b : ℝ) (_hb : 0 < b) : ℝ → ℂ :=
  fun u => (Real.sqrt b : ℂ) * ricker (b * u - a)

theorem atom_measurable (a b : ℝ) (hb : 0 < b) : Measurable (atom a b hb) := by
  unfold atom
  exact measurable_const.mul
    (ricker_measurable.comp ((measurable_const.mul measurable_id).sub_const a))

theorem atom_aestronglyMeasurable (a b : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (atom a b hb) volume :=
  (atom_measurable a b hb).aestronglyMeasurable

/--
Atom is in L²(ℝ). The proof uses:
1. ricker ∈ L² (from rickerReal_memLp2)
2. Translation invariance: f(x-a) ∈ L² if f ∈ L²
3. Dilation invariance: f(bx) ∈ L² if f ∈ L² (with appropriate Jacobian)
4. Scalar multiplication preserves L²
-/
theorem atom_memLp2 (a b : ℝ) (hb : 0 < b) :
    MemLp (atom a b hb) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm (atom_aestronglyMeasurable a b hb)]
  unfold atom
  -- ‖√b * ricker(bu - a)‖² = b * ‖ricker(bu - a)‖²
  have h_norm : ∀ u, ‖(Real.sqrt b : ℂ) * ricker (b * u - a)‖ ^ 2 =
      b * ‖ricker (b * u - a)‖ ^ 2 := by
    intro u
    rw [norm_mul]
    have h_sqrt_norm : ‖(Real.sqrt b : ℂ)‖ = Real.sqrt b := by
      have := @RCLike.norm_ofReal ℂ _ (Real.sqrt b)
      simp only [RCLike.ofReal_eq_complex_ofReal] at this
      rw [this, abs_of_nonneg (Real.sqrt_nonneg b)]
    rw [h_sqrt_norm, sq, sq, mul_mul_mul_comm]
    congr 1
    exact Real.mul_self_sqrt (le_of_lt hb)
  simp_rw [h_norm]
  apply Integrable.const_mul
  -- ‖ricker(bu - a)‖² is integrable via change of variables
  -- ricker(y) = rickerReal(y) as complex, so ‖ricker(y)‖ = |rickerReal(y)|
  unfold ricker
  have h_ricker_norm : ∀ x, ‖(rickerReal x : ℂ)‖ = |rickerReal x| := fun x =>
    RCLike.norm_ofReal (rickerReal x)
  simp_rw [h_ricker_norm]
  -- Base integrability: |rickerReal x|² is integrable
  have h_base : Integrable (fun x => |rickerReal x| ^ 2) volume := by
    have := (memLp_two_iff_integrable_sq rickerReal_aestronglyMeasurable).mp rickerReal_memLp2
    simp_rw [sq_abs]
    exact this
  -- First translate: x ↦ x - a, giving |rickerReal(x - a)|²
  have h_trans : Integrable (fun u => |rickerReal (u - a)| ^ 2) volume :=
    h_base.comp_sub_right a
  -- Then dilate: u ↦ b*u, giving |rickerReal(bu - a)|²
  have h_result : Integrable (fun u => |rickerReal (b * u - a)| ^ 2) volume :=
    h_trans.comp_mul_left' (ne_of_gt hb)
  exact h_result

def atomVec (a b : ℝ) (hb : 0 < b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (atom_memLp2 a b hb).toLp (atom a b hb)

/-! ## 5. Overlap Bound (Cauchy-Schwarz) -/

/--
The inner product of two atoms is bounded by the product of their norms.
-/
theorem atom_inner_bounded (a₁ b₁ a₂ b₂ : ℝ)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    ‖@inner ℂ _ _ (atomVec a₁ b₁ hb₁) (atomVec a₂ b₂ hb₂)‖ ≤
    ‖atomVec a₁ b₁ hb₁‖ * ‖atomVec a₂ b₂ hb₂‖ :=
  norm_inner_le_norm (atomVec a₁ b₁ hb₁) (atomVec a₂ b₂ hb₂)

end Riemann.Adapters.QFD

end
