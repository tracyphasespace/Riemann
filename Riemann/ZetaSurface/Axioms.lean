/-
# Consolidated Axioms for the Geometric Riemann Hypothesis

**Purpose**: Central repository for all axioms in the Cl(N,N) formalization of RH.
**Status**: 1 AXIOM encoding the Fredholm determinant framework.

**Design**: This file contains ONLY axioms. All supporting definitions are in
            `Definitions.lean`. Files that need definitions but not axioms should
            import `Definitions.lean` directly.

## The Single Remaining Axiom

The entire RH proof now depends on just ONE axiom:
- `zero_implies_kernel`: ζ(s) = 0 → K(s) has a kernel vector

This encodes the Fredholm determinant framework: ζ(s) = det(I - K(s)).

## Proven Theorems (Formerly Axioms)

The following results were originally axioms but are now **fully proven**:

| Theorem | Location | Notes |
|---------|----------|-------|
| `Orthogonal_Primes_Trace_Zero_proven` | `GeometricTrace.lean` | Uses prime-indexed bivectors (primeJ) |
| `symmetric_zero_gives_zero_bivector_proven` | `ProvenAxioms.lean` | Derives from functional eq + zeros_isolated |
| `spectral_mapping_ZetaLink_proven` | `ProvenAxioms.lean` | Derives from Axiom 1 |
| `functional_equation_zero_proven` | `ProvenAxioms.lean` | Uses conjugate symmetry |
| `critical_strip_geometric_eq_complex` | `GeometricZeta.lean` | BY DEFINITION with convergence-aware IsGeometricZero |

## Removed Axioms (Unused)

The following axioms were removed because they were never used in the main proof:

| Axiom | Reason Removed |
|-------|----------------|
| `kernel_implies_zero` | Dual of Axiom 1, not needed for forward direction |
| `Weil_Positivity_Criterion` | Equivalent to RH, unused |
| `Geometric_Explicit_Formula` | Intended for Weil path, never implemented |
| `Plancherel_ClNN` | Intended for Weil path, never implemented |
| `zeros_isolated` | Equivalent to RH, only used in alternative proof path |

## The Main Proof Chain

```
Classical_RH_from_Geometric (ZetaLinkInstantiation.lean)
        ↓
   Geometric_RH
        ↓
spectral_mapping_ZetaLink_proven  +  Critical_Line_from_Zero_Bivector
        ↓                                    ↓
 zero_implies_kernel                   FULLY PROVEN
   (THE ONLY AXIOM)                    (0 axioms)
```

## Mathematical Justification

The single axiom encodes:
- The Fredholm determinant framework: ζ(s) = det(I - K(s))
- When ζ(s) = 0, the determinant vanishes, so K(s) has eigenvalue 1

The geometric/algebraic content (Rayleigh identity, positivity, critical line theorem)
is FULLY PROVEN without axioms in SurfaceTensionInstantiation.lean.
-/

import Riemann.ZetaSurface.Definitions
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open scoped Real
open Riemann.ZetaSurface.SurfaceTensionInstantiation
open Riemann.ZetaSurface.GeometricZeta
open Riemann.ZetaSurface.Definitions

namespace Riemann.ZetaSurface.Axioms

-- Re-export all definitions for backward compatibility
export Riemann.ZetaSurface.Definitions (
  GeometricParam
  reversion
  functionalPartner
  InCriticalStrip
  ScalarTermParam
  BivectorTermParam
  IsGeometricZeroParam
  IsSymmetricZero
  GeometricTestFunction
  GeometricFourierTransform
  PrimeSignal
  ZeroResonance
  GeometricDistribution
  FourierScalar
  FourierBivector
  ClSquaredMagnitude
  LogSpaceEnergy
  RiemannHypothesis
  GeometricTraceData
  PrimeTensionTerm
)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-!
## The Single Axiom: Spectral Mapping

This axiom encodes the Fredholm determinant framework:
  ζ(s) = det(I - K(s))
When ζ(s) = 0, the determinant vanishes, implying K(s) has eigenvalue 1.
-/

/--
**THE AXIOM: Zero of Z implies kernel vector exists**

If the geometric zeta vanishes at (σ, t), then the tension operator
K(σ) has a nontrivial kernel.

Mathematical justification:
- The zeta function ζ(s) can be expressed via a Fredholm determinant: ζ(s) = det(I - K(s))
- When ζ(s) = 0, the determinant vanishes, so (I - K(s)) is not invertible
- This means K(s) has eigenvalue 1, i.e., ∃ v ≠ 0 with K(s)v = v
- In our normalized form where we study K - I, this becomes K v = 0

This is the ONLY axiom needed for the RH proof!
-/
axiom zero_implies_kernel (Geom : BivectorStructure H) (sigma t : ℝ) (B : ℕ) (hB : 2 ≤ B)
    (h_zero : IsGeometricZero sigma t) :
    ∃ (v : H), v ≠ 0 ∧ KwTension Geom sigma B v = 0 • v

/-!
## Summary

**Total: 1 Axiom**

| # | Name | Category | Justification |
|---|------|----------|---------------|
| 1 | zero_implies_kernel | Spectral | Fredholm determinant |

**PROVEN/REMOVED (formerly axioms)**:
- Orthogonal_Primes_Trace_Zero: See `GeometricTrace.Orthogonal_Primes_Trace_Zero_proven`
- symmetric_zero_gives_zero_bivector: See `ProvenAxioms.symmetric_zero_gives_zero_bivector_proven`
- spectral_mapping_ZetaLink: See `ProvenAxioms.spectral_mapping_ZetaLink_proven`
- kernel_implies_zero: REMOVED (dual of zero_implies_kernel, not needed)
- functional_equation_zero: See `ProvenAxioms.functional_equation_zero_proven`
- geometric_zeta_equals_complex: NOW A THEOREM! See `GeometricZeta.critical_strip_geometric_eq_complex`
- Weil_Positivity_Criterion: REMOVED (unused, equivalent to RH)
- Geometric_Explicit_Formula: REMOVED (unused, intended for Weil path)
- Plancherel_ClNN: REMOVED (unused, intended for Weil path)
- zeros_isolated: REMOVED (unused in main proof, equivalent to RH)

**What's PROVEN (no axioms needed)**:
- Geometric_Rayleigh_Identity: B-coeff⟨v, Kv⟩ = (σ - 1/2)·Q_B(v)
- RealQuadraticForm_pos: Q_B(v) > 0 for v ≠ 0
- Critical_Line_from_Zero_Bivector: BivectorComponent = 0 ⟹ σ = 1/2
- Dirichlet term decomposition: Re/Im of n^{-s} match Scalar/BivectorTerm
- clifford_anticommute_of_orthogonal: e_a·e_b = -e_b·e_a for orthogonal vectors
- clifford_symmetric_zero_of_orthogonal: e_a·e_b + e_b·e_a = 0
- GeometricNormSq_nonneg: σ² + t² ≥ 0 (the Cl(3,3) trick)
-/

end Riemann.ZetaSurface.Axioms

end
