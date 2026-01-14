# Required Lean Statements

This document tracks incomplete proofs and placeholder statements in the Riemann Hypothesis formalization project. External contributors can provide solutions which will be reviewed and integrated.

**Last Updated**: 2026-01-14
**Build Status**: ✅ Passing
**Counts**: 1 sorry, 4 axioms, 12 trivial placeholders

---

## Current Status Summary

| Category | Count | Status |
|----------|-------|--------|
| Theorems with `sorry` | 1 | Blocking |
| Axioms | 4 | Structural |
| Trivial placeholders | 12 | Future work |
| Total Lean files | ~25 | Building |

---

## Priority 1: Sorry Statements (Blocking Full Verification)

### 1.1 `HR_nonempty` - Hardy Space Non-emptiness

**File**: `Riemann/ZetaSurface/SurfaceTension.lean:167`

**Current State**:
```lean
/--
HR is nonempty (contains at least non-constant functions).
-/
theorem HR_nonempty : ∃ f : HR, f ≠ 0 := by
  sorry  -- Requires showing HR has nonzero elements
```

**What's Needed**: Construct an explicit nonzero element of the Hardy space HR.

**Suggested Approach**:
1. HR is defined as a subtype of holomorphic functions on the right half-plane
2. Show that constant functions or specific analytic functions are in HR
3. Use `⟨explicit_element, proof_of_membership, proof_nonzero⟩`

---

## Priority 2: Axioms (Structural Assumptions)

These are modeling axioms for the measure completion approach. They could potentially be proven with more measure theory infrastructure.

**File**: `Riemann/ZetaSurface/CompletionMeasure.lean`

### 2.1 `Utranslate_spec`
```lean
/--
Utranslate specification: acts as corrected pullback.
-/
axiom Utranslate_spec (w : Weight) (a : ℝ) :
    ∀ f : Hw w, ∀ᵐ u ∂(μw w),
      (Utranslate w a f : ℝ → ℂ) u =
      (Real.sqrt (ENNReal.toReal (RN_deriv w a u)) : ℂ) * (f : ℝ → ℂ) (u + a)
```

### 2.2 `Utranslate_adjoint`
```lean
/--
**Key Property**: Adjoint of corrected translation is inverse translation.
(U_a)† = U_{-a}
-/
axiom Utranslate_adjoint (w : Weight) (a : ℝ) :
    (Utranslate w a).toContinuousLinearMap.adjoint =
    (Utranslate w (-a)).toContinuousLinearMap
```

### 2.3 `Utranslate_add`
```lean
/--
Utranslate forms a group action.
-/
axiom Utranslate_add (w : Weight) (a b : ℝ) :
    (Utranslate w a).comp (Utranslate w b) = Utranslate w (a + b)
```

### 2.4 `Utranslate_zero`
```lean
axiom Utranslate_zero (w : Weight) :
    Utranslate w 0 = LinearIsometry.id
```

**Context**: These axioms define properties of the corrected unitary translation operator on weighted L² spaces.

To prove these as theorems, one would need to:
1. Define `Utranslate` explicitly (not opaque)
2. Prove quasi-invariance of the weighted measure
3. Prove the Radon-Nikodym derivative properties
4. Verify the isometry and adjoint relations

---

## Priority 3: Trivial Placeholders (Future Work)

These represent theorems whose precise statements haven't been formalized. They need proper theorem statements with proofs.

### 3.1 Clifford Algebra Isomorphism
**File**: `Riemann/GA/Cl33.lean:266`
```lean
-- Placeholder for Cl(3,3) ≅ M(4,ℂ) isomorphism proof
```

### 3.2 Spectral Reality Off-Critical
**File**: `Riemann/ZetaSurface/SpectralReal.lean:166`
```lean
-- Off-critical line eigenvalue properties
```

### 3.3 Kernel Spectrum on Critical Line
**File**: `Riemann/ZetaSurface/CompletionKernelModel.lean:153`
```lean
-- spectrum(K s B) ⊆ ℝ when Re(s) = 1/2
```

### 3.4 Transfer Operator Asymmetry
**File**: `Riemann/ZetaSurface/TransferOperator.lean:175`
```lean
-- Asymmetry properties
```

### 3.5 Completion Core Spectrum
**File**: `Riemann/ZetaSurface/CompletionCore.lean:232`
```lean
-- Spectrum properties for completed model
```

### 3.6 Finite Zeta Link (6 placeholders)
**File**: `Riemann/ZetaSurface/ZetaLinkFinite.lean`
- Line 132: Finite reflection symmetry
- Line 195: Determinant-Euler approximation
- Line 205: Determinant-Euler limit
- Line 214: Zero correspondence
- Line 251: Trace-log-det identity
- Line 279: Compression convergence

**Desired Forms**:
- `Z_reflection_partial`: `Z B s = Z B (1 - s) * (correction)`
- `detLike_char_approx_euler`: `‖detLike C s B - ZInv B s‖ ≤ error_bound`
- `trace_log_det_finite`: `log(det(I - A)) = -∑ n, tr(A^n) / n`

### 3.7 Surface Tension Placeholder
**File**: `Riemann/ZetaSurface/SurfaceTension.lean:191`
```lean
-- Surface tension analysis
```

---

## Imports Available

The project uses Mathlib v4.27.0-rc1 extensively. Key imports:

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
```

---

## Contribution Guidelines

1. **Format**: Provide complete Lean 4 proof terms or tactic proofs
2. **Imports**: Note any additional imports needed
3. **Testing**: Proofs should be verified against Mathlib v4.27.0-rc1
4. **Style**: Follow Mathlib conventions, avoid simp linter warnings
5. **Priority**: Focus on Priority 1 items first

---

## Completed This Session

- [x] `rickerReal_memLp2` - L² Membership for Ricker Wavelet (AdapterQFD_Ricker.lean)
- [x] `atom_memLp2` - L² Membership for Wavelet Atoms (AdapterQFD_Ricker.lean)
- [x] `one_minus_conj_critical'` - Critical line algebraic identity
- [x] `normal_on_critical` - Normality on critical line
- [x] `rickerSubspace_dim_le` - Dimension bound
- [x] `rickerSubspace_dim_eq` - Dimension equality
- [x] `detLike_zero_implies_hasEigOne` - Eigenvalue 1 condition

---

## Development Path

### Paper → Lean Correspondence

| Paper Section | Lean Module | Status |
|--------------|-------------|--------|
| Sieve operator K(s) | `TransferOperator.lean` | Complete |
| Adjoint symmetry | `CompletionCore.lean` | Complete |
| Critical line self-adjointness | `SpectralReal.lean` | Complete |
| Compression framework | `Compression.lean` | Complete |
| Ricker wavelets | `AdapterQFD_Ricker.lean` | Complete |
| Determinant det(I-A) | `SpectralZeta.lean` | Complete |
| Euler product link | `ZetaLinkFinite.lean` | Placeholders |
| Full RH statement | Not yet | Future |

### Architecture Overview

```
Riemann/
├── GA/                    # Geometric Algebra foundations
│   ├── Cl33.lean         # Cl(3,3) Clifford algebra
│   └── Cl33Ops.lean      # Operations and spinors
├── ZetaSurface/          # Main development
│   ├── CompletionCore.lean       # Abstract operator interface
│   ├── CompletionKernelModel.lean # Concrete L² model
│   ├── CompletionMeasure.lean    # Weighted measure model
│   ├── Compression.lean          # Finite-dimensional compression
│   ├── CompressionRicker.lean    # Wavelet compression
│   ├── SpectralReal.lean         # Spectral reality proofs
│   ├── SpectralZeta.lean         # Spectral zeta functions
│   ├── TransferOperator.lean     # K(s) definition
│   ├── ZetaLinkFinite.lean       # Euler product connection
│   └── AdapterQFD_Ricker.lean    # Ricker wavelet proofs
└── Riemann.lean          # Main entry point
```
