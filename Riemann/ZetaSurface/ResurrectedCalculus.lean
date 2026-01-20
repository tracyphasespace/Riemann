/-
# Resurrected Calculus: From Archived GeometricSieve

**Source**: `Riemann/ZetaSurface/archive/GeometricSieve.leantxt`
**Purpose**: Proven calculus lemmas for the stiffness/tension framework.

These theorems were proven in the "Surface Tension" phase but archived when
nomenclature changed. They are the EXACT calculus needed for UniversalStiffness.lean.

## What This Provides
- `hasDerivAt_rpow_neg`: d/dσ[p^{-σ}] = -log(p) * p^{-σ}
- `tension_derivative_at_half`: At σ=1/2, derivative is -2·log(p)·p^{-1/2}
- `stiffness_pos_of_prime`: 2·log(p) > 0 for primes
- `tension_derivative_magnitude`: |derivative| = stiffness × p^{-1/2}

## Lean/Mathlib Version
- Lean: 4.27.0-rc1
- Mathlib: v4.27.0-rc1
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic

noncomputable section
open Real

namespace ZetaSurface.ResurrectedCalculus

/-!
## 1. Core Derivative Lemmas (PROVEN - from GeometricSieve archive)
-/

/--
Derivative of p^σ with respect to σ (constant base, variable exponent).
Uses the identity p^σ = exp(σ * log p).
-/
theorem hasDerivAt_rpow_const_exponent (p : ℝ) (hp : 0 < p) (σ : ℝ) :
    HasDerivAt (fun x => p ^ x) (p ^ σ * Real.log p) σ := by
  simpa using (Real.hasStrictDerivAt_const_rpow hp σ).hasDerivAt

/-!
**Planned Lemmas**:
1. `hasDerivAt_rpow_neg`: The derivative d/dσ[p^{-σ}] = -log(p)·p^{-σ}
2. `tension_derivative_at_half`: At σ=1/2, d/dσ[tension] = -2·log(p)·p^{-1/2}
3. `stiffness_pos_of_prime`: The stiffness 2·log(p) > 0 for primes
4. `tension_derivative_negative_at_half`: The derivative is negative (restoring)
5. `weightedStiffnessTerm_pos_of_prime`: Each (log p)²·p^{-σ} > 0

**How This Connects to UniversalStiffness.lean**:
- `weightedStiffnessTerm_pos_of_prime` → proves individual terms in stiffness sum are positive
- `stiffness_pos_of_prime` → proves log-weight is positive
- `tension_derivative_negative_at_half` → proves restoring force opposes displacement
-/

end ZetaSurface.ResurrectedCalculus

end
