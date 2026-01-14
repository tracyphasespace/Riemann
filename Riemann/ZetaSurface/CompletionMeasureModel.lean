/-
# Measure Completion Model Instance

**Purpose**: Instantiate the CompletedModel interface using the measure completion.

## Contents

1. Define `MeasureModel w : CompletedModel` for a quasi-invariant weight w
2. Prove adjoint_symm using Kw_adjoint_symm
3. Prove normal_on_critical using self-adjointness on critical line

## Note

This model requires a weight function w and quasi-invariance hypothesis.
It is parametric over the weight choice, allowing different completions
(e.g., Gamma-weighted) to be instantiated.

## References

- CompletionCore.lean (interface definition)
- CompletionMeasure.lean (operator definition and adjoint theorem)
-/

import Riemann.ZetaSurface.CompletionCore
import Riemann.ZetaSurface.CompletionMeasure

noncomputable section
open scoped Real ComplexConjugate
open MeasureTheory
open Complex

namespace Riemann.ZetaSurface

/-! ## 1. Helper Lemma for Critical Line -/

/--
On the critical line, 1 - conj(s) = s.
This is the key algebraic fact for self-adjointness.
-/
theorem one_minus_conj_critical' (t : ℝ) :
    (1 : ℂ) - conj ((1/2 : ℂ) + (t : ℂ) * I) = (1/2 : ℂ) + (t : ℂ) * I := by
  -- conj(1/2 + t*I) = 1/2 - t*I  (since conj of real = real, conj(I) = -I)
  -- 1 - (1/2 - t*I) = 1/2 + t*I
  simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
  have h : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by simp [starRingEnd_apply]
  rw [h]
  ring

/-! ## 2. The Measure Model -/

/--
Measure completion model instance for a given weight w.
- H := L²(ℝ, μ_w; ℂ) where μ_w = volume.withDensity w
- Op := Kw w (from CompletionMeasure.lean)

This satisfies:
- adjoint_symm: Op(s)† = Op(1 - conj(s)) via Kw_adjoint_symm
- normal_on_critical: on Re(s) = 1/2, Op is self-adjoint hence normal
-/
def MeasureModel (w : CompletionMeasure.Weight) : CompletedModel where
  H := CompletionMeasure.Hw w

  instNormedAddCommGroup := inferInstance
  instInner := inferInstance
  instComplete := inferInstance

  Op := fun s B => CompletionMeasure.Kw w s B

  adjoint_symm := by
    intro s B
    exact CompletionMeasure.Kw_adjoint_symm w s B

  normal_on_critical := by
    intro t B
    -- Unfold the let-binding explicitly
    change (CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint *
         CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B =
         CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B *
         (CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint
    -- Kw(s)† = Kw(1 - conj(s)) = Kw(s) on critical line
    have h_sa : (CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint =
                CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B := by
      rw [CompletionMeasure.Kw_adjoint_symm, one_minus_conj_critical']
    -- Self-adjoint operators are normal: A† A = A A = A A†
    rw [h_sa]

/-! ## 3. Specific Weight Choices -/

/--
Trivial weight w ≡ 1.
μ_{1} = volume.
-/
def trivialWeight : CompletionMeasure.Weight := fun _ => 1

def TrivialMeasureModel : CompletedModel := MeasureModel trivialWeight

/--
Exponential weight for a given σ₀.
w(u) = exp(σ₀ · u)
-/
def expWeight (σ₀ : ℝ) : CompletionMeasure.Weight :=
  fun u => ENNReal.ofReal (Real.exp (σ₀ * u))

def ExpMeasureModel (σ₀ : ℝ) : CompletedModel := MeasureModel (expWeight σ₀)

/-! ## 4. Derived Theorems for Measure Model -/

theorem measure_selfadjoint_critical (w : CompletionMeasure.Weight) (t : ℝ) (B : ℕ) :
    (CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B).adjoint =
    CompletionMeasure.Kw w ((1/2 : ℂ) + (t : ℂ) * I) B := by
  rw [CompletionMeasure.Kw_adjoint_symm, one_minus_conj_critical']

theorem measure_selfadjoint_half (w : CompletionMeasure.Weight) (B : ℕ) :
    (CompletionMeasure.Kw w (1/2 : ℂ) B).adjoint = CompletionMeasure.Kw w (1/2 : ℂ) B := by
  rw [CompletionMeasure.Kw_adjoint_symm]
  -- 1 - conj(1/2) = 1 - 1/2 = 1/2 for real 1/2
  have h : conj (1/2 : ℂ) = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal (1/2)
  rw [h]
  norm_num

theorem measure_normal_critical (w : CompletionMeasure.Weight) (t : ℝ) (B : ℕ) :
    let s := (1/2 : ℂ) + (t : ℂ) * I
    (CompletionMeasure.Kw w s B).adjoint * CompletionMeasure.Kw w s B =
    CompletionMeasure.Kw w s B * (CompletionMeasure.Kw w s B).adjoint := by
  intro s
  have h := measure_selfadjoint_critical w t B
  dsimp [s]
  rw [h]

/-! ## 5. Comparison with Kernel Model

The two models agree on the key structural properties:
- Both have adjoint_symm
- Both have normal_on_critical
- Both are self-adjoint on the critical line

The difference is:
- KernelModel: Fixed space L²(ℝ, du), weights in operator
- MeasureModel: Parametric space L²(ℝ, w·du), weights in measure

For most structural proofs, either model works.
For matching ξ(s) precisely, MeasureModel with Gamma-weight may be needed.

## Physical Summary

The MeasureModel demonstrates that the measure completion approach:

1. **Satisfies the same interface**: adjoint_symm and normal_on_critical hold
2. **Parametric over weight**: Different w give different completions
3. **Gamma absorption**: Weight can encode Γ(s/2)·π^{-s/2} factors
4. **Same algebraic proofs**: Critical line self-adjointness is identical

Trade-offs vs KernelModel:
- **Pro**: Natural place for Gamma factors
- **Con**: Requires quasi-invariance infrastructure
- **Con**: More measure theory dependencies

For initial formalization, KernelModel is recommended.
For final ξ(s) matching, MeasureModel with appropriate weight.

Note: Spectrum properties (real eigenvalues on critical line) are handled
by SpectralReal.lean, which operates on any CompletedModel instance.
-/

end Riemann.ZetaSurface

end
