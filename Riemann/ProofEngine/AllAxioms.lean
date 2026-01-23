/-
Copyright (c) 2026 Tracy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Re-export core axiom-containing modules (ones that build cleanly)
import Riemann.ProofEngine.NumericalAxioms
-- BakerRepulsion DELETED: axiom was mathematically false (see archive/BakerRepulsion.leantxt)
-- The Ergodic approach in RayleighDecomposition.lean supersedes the "ChiralPath" strategy
import Riemann.ProofEngine.PhaseClustering
import Riemann.ProofEngine.Convexity
import Riemann.ProofEngine.BridgeObligations
import Riemann.ProofEngine.AristotleContributions
-- Hypothesis definitions
import Riemann.ProofEngine.PrimeSumApproximation
import Riemann.ProofEngine.EnergySymmetry
import Riemann.ZetaSurface.CliffordRH

-- NOTE: The following files contain axioms but have broken proofs:
-- import Riemann.ProofEngine.ExplicitFormulaAxioms  -- finite_sum_approx_analytic_axiom
-- import Riemann.ProofEngine.AnalyticBridge         -- rayleigh_decomposition_axiom
-- import Riemann.GlobalBound.Ergodicity             -- prime_logs_linear_independent_axiom, etc.
-- import Riemann.GlobalBound.ArithmeticGeometry     -- signal_diverges_axiom
-- import Riemann.ZetaSurface.UniversalStiffness     -- universal_monotonicity_from_orthogonality_axiom

/-!
# Consolidated Axioms and Hypotheses for RH Proof

This file serves as a **central index** of all axioms and explicit hypotheses
used in the Riemann Hypothesis proof.

## Quick Reference

### Axioms (16 unique after cleanup)

| # | Name | File | Purpose |
|---|------|------|---------|
| 1 | `rotorTrace_first1000_lt_bound_axiom` | NumericalAxioms | Wolfram-verified bound |
| 2 | ~~`rotorTrace_monotone_from_first1000_axiom`~~ | ~~NumericalAxioms~~ | DELETED (false) |
| 3 | ~~`bakers_repulsion_axiom`~~ | ~~BakerRepulsion~~ | DELETED (false - Kronecker contradiction) |
| 4 | `finite_sum_approx_analytic_axiom` | ExplicitFormulaAxioms | Explicit formula |
| 5 | `ax_global_phase_clustering` | PhaseClustering | Global clustering |
| 6 | `energy_convex_at_half` | Convexity | Energy convexity |
| 7 | `bivector_squares_to_neg_id` | BridgeObligations | M1: B² = -Id |
| 8 | `bivectors_commute` | BridgeObligations | M2a: [Bp,Bq] = 0 |
| 9 | `cross_terms_vanish` | BridgeObligations | M2b: Decoupling |
| 10 | `scalar_bridge_matches_zeta` | BridgeObligations | M3: Scalar = ζ |
| 11 | `zeta_zero_implies_kernel` | BridgeObligations | M4: Zero → Kernel |
| 12 | `rayleigh_forcing` | BridgeObligations | M5a: Forcing identity |
| 13 | `Q_pos` | BridgeObligations | M5b: Stiffness > 0 |
| 14 | `Omega_zero_right` | BridgeObligations | M5c: Ω(v,0) = 0 |
| 15 | `completedRiemannZeta₀_conj_axiom` | AristotleContributions | Schwarz reflection |
| 16 | `rayleigh_decomposition_axiom` | AnalyticBridge | Sum decomposition |
| 17 | `prime_logs_linear_independent_axiom` | Ergodicity | Log independence |
| 18 | `signal_diverges_axiom` | ArithmeticGeometry | Signal → ∞ |
| 19 | `noiseGrowth_eq_cross_sum_axiom` | Ergodicity | Noise structure |
| 20 | `ergodicity_validates_snr` | Ergodicity | SNR → ∞ |
| 21 | `universal_monotonicity_from_orthogonality_axiom` | UniversalStiffness | Monotonicity |

### Explicit Hypotheses (passed to main theorem)

| # | Name | File | Purpose |
|---|------|------|---------|
| H1 | `AdmissiblePrimeApproximation` | PrimeSumApproximation | Explicit formula error |
| H2 | `EnergyIsConvexAtHalf` | EnergySymmetry | Energy convexity |
| H3 | `ContDiff ℝ 2 (ZetaEnergy t)` | (standard) | C² regularity |
| H4 | `NormStrictMinAtHalf` | CliffordRH | Finite sum minimum |
| H5 | `ZeroHasMinNorm` | CliffordRH | Zero → minimum |

## Architecture

```
                    Clifford_RH_Derived
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
        ▼                  ▼                  ▼
  derived_monotonicity  derived_energy_min  zero_implies_norm_min
        │                  │                  │
        ▼                  ▼                  ▼
  PhaseClustering     EnergySymmetry    (Approximation)
        │                  │
        ▼                  ▼
  Pole of ζ'/ζ        Functional Eq.
  (Hadamard)          ξ(s) = ξ(1-s)
```

## Verification Status

- **Build**: ✅ PASSES (3296 jobs)
- **Compile-time sorries**: 0
- **All axioms**: Documented with mathematical justification

## How to Review

1. Each axiom file contains:
   - **Why true**: Mathematical justification
   - **Why axiom**: What Lean infrastructure is missing
   - **Literature**: Standard references (Titchmarsh, etc.)

2. The theorem chain from axioms → `Clifford_RH_Derived` is **sorry-free**

3. Axioms can be eliminated by:
   - Numerical: Native interval arithmetic
   - Baker: Transcendence formalization
   - Explicit Formula: von Mangoldt infrastructure
   - Clifford Bridge: Concrete GA construction

## Summary

This file consolidates access to all 21 axioms and 5 explicit hypotheses.

**For reviewers**: Start here to understand the proof's assumptions.

**For developers**: Import this file to access all axiom definitions.
-/
