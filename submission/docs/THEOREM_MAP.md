# Theorem Map: Paper ↔ Lean Correspondence

Copyright 2026 Tracy McSheery PhaseSpace

This document maps claims in the paper to their formal Lean 4 statements.

## Main Results

| Paper Section | Statement | Lean File | Theorem Name | Status |
|---------------|-----------|-----------|--------------|--------|
| Theorem 1.1 | Real eigenvalue ⟹ σ = 1/2 | `SpectralReal.lean:365` | `Real_Eigenvalue_Implies_Critical_of_SurfaceTension` | **PROVEN** |
| Theorem 1.2 | RH from ZetaLink + Surface Tension | `SpectralReal.lean:545` | `RH_of_ZetaLink_SurfaceTension` | **PROVEN** |
| Theorem 2.1 | Self-adjoint ⟹ real eigenvalues | `SpectralReal.lean:94` | `Eigenvalue_Real_of_SelfAdjoint` | **PROVEN** |
| Theorem 3.1 | Defect zero ⟺ critical line | `SpectralReal.lean:208` | `Defect_Zero_Iff_Critical` | **PROVEN** |
| Theorem 4.1 | Critical line from zero bivector | `SurfaceTensionInstantiation.lean:229` | `Critical_Line_from_Zero_Bivector` | **PROVEN** |
| Theorem 4.2 | Rayleigh identity | `SurfaceTensionInstantiation.lean:134` | `Geometric_Rayleigh_Identity` | **PROVEN** |
| Theorem 4.3 | Quadratic form positivity | `SurfaceTensionInstantiation.lean:182` | `RealQuadraticForm_pos` | **PROVEN** |

## Core Definitions

| Concept | Lean File | Definition Name |
|---------|-----------|-----------------|
| Riemann Hypothesis | `SpectralReal.lean:490` | `RiemannHypothesis` |
| Geometric Zero | `Definitions.lean` | `IsGeometricZero` |
| Bivector Structure | `SurfaceTensionInstantiation.lean:57` | `BivectorStructure` |
| Surface Tension Operator | `SurfaceTensionInstantiation.lean:101` | `KwTension` |
| Adjoint Defect | `SpectralReal.lean:176` | `AdjointDefect` |
| Completed Model | `CompletionCore.lean` | `CompletedModel` |

## The Single Axiom

| Paper Section | Statement | Lean File | Name | Status |
|---------------|-----------|-----------|------|--------|
| Section 5 | ζ(s)=0 ⟹ kernel exists | `Axioms.lean:125` | `zero_implies_kernel` | **AXIOM** |

## Proof Chain

The main proof proceeds as follows:

```lean
-- 1. Assume ζ(s) = 0 in critical strip
-- 2. By zero_implies_kernel (AXIOM): ∃ v ≠ 0, K(s)v = v
-- 3. Eigenvalue 1 is real
-- 4. By Real_Eigenvalue_Implies_Critical_of_SurfaceTension (PROVEN):
--    Real eigenvalue + Q_B > 0 ⟹ σ = 1/2
-- 5. Therefore RH holds
```

## Algebraic Foundations (All Proven)

| Lemma | Lean File | Name | Status |
|-------|-----------|------|--------|
| J² = -1 | `SurfaceTensionInstantiation.lean` | `BivectorStructure.sq_neg_one` | **PROVEN** |
| Prime orthogonality | `SurfaceTensionInstantiation.lean` | `BivectorStructure.e_orthogonal` | **PROVEN** |
| Diagonal structure | `DiagonalSpectral.lean:113` | `RealComponent_diagonal_on_primes` | **PROVEN** |
| Skew-adjoint → self-adjoint | `SpectralReal.lean:284` | `SkewAdjoint_to_SelfAdjoint` | **PROVEN** |

## Verification Command

To verify any specific theorem compiles:

```bash
lake build Riemann.ZetaSurface.SpectralReal
```

All theorems marked **PROVEN** have no `sorry` in their proof terms.
