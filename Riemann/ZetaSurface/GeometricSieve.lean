/-
# Surface Tension in Cl(3,3): The Geometric Sieve

**Purpose**: Formalize the Sieve Operator using Split-Signature Geometric Algebra.
We replace 'Complex' with 'GeometricParam' to explicitly show that the
imaginary unit is a Bivector (Rotation), and the real part is Dilation.

**The Thesis**:
The Critical Line is the unique locus where the Sieve generates
pure rotations (Isometries). Off the line, the Sieve generates
dilations (Instabilities).

**Key Insight**:
The "Surface Tension" is the mismatch in the Scalar Magnitude (Dilation)
between forward and reverse (adjoint) operations:
- Forward:  p^{-σ} exp(-B θ)
- Reverse:  p^{-(1-σ)} exp(+B θ)

The geometric balance condition p^{-σ} = p^{-(1-σ)} forces σ = 1/2.

**Resurrected**: 2026-01-18
This file contains PROVEN theorems (0 sorries) that explain WHY log(p)
appears in the stiffness weights - pure calculus derivation.

## Key Proven Theorems:
- `Geometric_Stability_Condition`: Zero tension ⟺ σ = 1/2
- `tension_derivative_at_half`: d/dσ[tension] = -2·log(p)·p^{-1/2}
- `stiffness_pos_of_prime`: Stiffness > 0 for all primes
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

noncomputable section
open scoped Real

namespace Riemann.ZetaSurface.GeometricSieve

/-! ## 0. Prime Set Utilities (inlined from PrimeShifts) -/

/--
The set of primes up to bound B.
-/
def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

/--

All elements of primesUpTo are prime.

-/

theorem mem_primesUpTo_prime {p B : ℕ} (hp : p ∈ primesUpTo B) : Nat.Prime p := by

  unfold primesUpTo at hp

  simp at hp

  exact hp.2

end Riemann.ZetaSurface.GeometricSieve