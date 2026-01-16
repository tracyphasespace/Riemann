/-
# Spectral Mapping: Zeros of Z Map to Kernel Vectors of K

**Purpose**: Establish the spectral mapping theorem for the log-gradient operator.
**Status**: Core theorem using axioms from Axioms.lean.

## Design Note: Why These Are Axioms

This file encodes a **conjectural correspondence** between:

1. **Analytic**: `IsGeometricZero σ t` - the Dirichlet series sums vanish
2. **Spectral**: `KwTension σ B v = 0` - the operator has a kernel vector

**Key Point**: These are NOT equivalent from definitions alone.

The operator `KwTension` is defined algebraically as:
```
  KwTension = (σ - 1/2) * LatticeStiffness B • J
```

It does not "know about" the Dirichlet series. The connection between
zeta zeros and operator kernels requires the **Spectral Mapping Principle**
from functional analysis: ζ(s) = det(I - K(s)).

The axiom `zero_implies_kernel` is defined in `Axioms.lean` and encodes
this deep spectral-arithmetic bridge. (The dual `kernel_implies_zero` was
removed as unnecessary for the main RH proof.)

## Consequence
Once these axioms hold, `RH_from_SpectralMapping` proves σ = 1/2
using the Rayleigh identity and positivity of the quadratic form.
-/

import Riemann.ZetaSurface.Axioms
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open scoped Real
open Riemann.ZetaSurface.SurfaceTensionInstantiation
open Riemann.ZetaSurface.GeometricZeta
open Riemann.ZetaSurface.Axioms

namespace Riemann.ZetaSurface.SpectralMapping

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
**The Core Observation (Convergent Region)**: For σ > 1, geometric zero means both sums vanish.
-/
theorem geometric_zero_is_spectral_zero_convergent (sigma t : ℝ) (h : sigma > 1) :
    IsGeometricZero sigma t ↔
    (∑' n : ℕ, ScalarTerm n sigma t = 0) ∧
    (∑' n : ℕ, BivectorTerm n sigma t = 0) := by
  unfold IsGeometricZero IsGeometricZero_Convergent
  simp only [if_pos h]

/--
**The Core Observation (Critical Strip)**: For 0 < σ < 1, geometric zero means riemannZeta = 0.
-/
theorem geometric_zero_is_spectral_zero_critical (sigma t : ℝ) (h : 0 < sigma ∧ sigma < 1) :
    IsGeometricZero sigma t ↔ riemannZeta (⟨sigma, t⟩ : ℂ) = 0 :=
  critical_strip_geometric_eq_complex sigma t h

/--
**The Spectral Mapping Theorem (Geometric Form, Forward Direction)**

Uses axiom from Axioms.lean:
- `zero_implies_kernel`: Geometric zero → kernel vector exists

Note: The backward direction (`kernel_implies_zero`) was removed as an axiom
since the main RH proof only needs the forward direction.
-/
theorem spectral_mapping_geometric (Geom : BivectorStructure H) (sigma t : ℝ) (B : ℕ) (hB : 2 ≤ B) :
    IsGeometricZero sigma t →
    ∃ (v : H), v ≠ 0 ∧ KwTension Geom sigma B v = 0 • v :=
  zero_implies_kernel Geom sigma t B hB

/--
**The Complete Argument for RH**

Given: IsGeometricZero σ t with 0 < σ < 1 and t ≠ 0
Result: σ = 1/2

**Key Insight**: Eigenvalue 1 is automatically real!
-/
theorem RH_from_SpectralMapping (Geom : BivectorStructure H) (sigma t : ℝ) (B : ℕ) (hB : 2 ≤ B)
    (h_strip : 0 < sigma ∧ sigma < 1)
    (h_zero : IsGeometricZero sigma t)
    (h_t_nonzero : t ≠ 0) :
    sigma = 1/2 := by
  obtain ⟨v, hv, h_kernel⟩ := zero_implies_kernel Geom sigma t B hB h_zero
  -- h_kernel: KwTension v = 0 • v = 0
  have h_kw_zero : KwTension Geom sigma B v = 0 := by
    rw [zero_smul] at h_kernel; exact h_kernel
  -- BivectorComponent T v = -⟨v, J(T v)⟩
  -- When T v = 0: BivectorComponent T v = -⟨v, J(0)⟩ = -⟨v, 0⟩ = 0
  have h_bivector_zero : BivectorComponent Geom (KwTension Geom sigma B) v = 0 := by
    unfold BivectorComponent
    rw [h_kw_zero]
    simp only [ContinuousLinearMap.map_zero, inner_zero_right, neg_zero]
  -- Apply Rayleigh identity
  have h_rayleigh := Geometric_Rayleigh_Identity Geom sigma B v
  rw [h_bivector_zero] at h_rayleigh
  -- Now 0 = (sigma - 1/2) * Q(v), with Q(v) > 0
  have h_Q_pos : 0 < RealQuadraticForm B v := RealQuadraticForm_pos B hB v hv
  -- Therefore sigma - 1/2 = 0
  have h_factor : sigma - 1/2 = 0 := by
    by_contra h_ne
    have h_nonzero : (sigma - 1/2) * RealQuadraticForm B v ≠ 0 :=
      mul_ne_zero h_ne (ne_of_gt h_Q_pos)
    exact h_nonzero h_rayleigh.symm
  linarith

/--
**The Geometric Zeta Link (Derived, not Axiom)**

IsGeometricZero σ t ∧ 0 < σ < 1 ∧ t ≠ 0 → σ = 1/2
-/
theorem GeometricZetaLink_Derived (Geom : BivectorStructure H) (sigma t : ℝ) (B : ℕ) (hB : 2 ≤ B)
    (h_strip : 0 < sigma ∧ sigma < 1)
    (h_zero : IsGeometricZero sigma t)
    (h_t_nonzero : t ≠ 0) :
    sigma = 1/2 :=
  RH_from_SpectralMapping Geom sigma t B hB h_strip h_zero h_t_nonzero

end Riemann.ZetaSurface.SpectralMapping
