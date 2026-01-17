/-
# Geometric Positivity: The Weil Criterion via Cl(n,n)

**Purpose**: Prove positivity using ONLY real Cl(n,n) structure.
**Key Insight**: Squared magnitudes are sums of squares - no imaginary numbers needed!

**The Cl(n,n) Structure**:
In Cl(n,n), the "Fourier transform" has two REAL components:
- Scalar part: ∫ φ(x) cos(tx) dx
- B-coefficient: ∫ φ(x) sin(tx) dx

The squared magnitude is:
  |φ̂(t)|² = [scalar part]² + [B-coefficient]²
           = [∫ φ cos]² + [∫ φ sin]²

This is a SUM OF SQUARES OF REAL NUMBERS - always ≥ 0!
No complex numbers, no "imaginary parts" - pure real geometric algebra.

**Note**: This file uses ONLY definitions from Definitions.lean (no axioms).
         The axiom Plancherel_ClNN is in Axioms.lean but is not needed for
         the algebraic positivity proofs here.
-/

import Riemann.ZetaSurface.Definitions
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open scoped Real
open MeasureTheory
open Riemann.ZetaSurface.Definitions

namespace Riemann.ZetaSurface.GeometricPositivity

/-!
## 1. The Geometric Norm in Cl(3,3)

In split-signature Clifford algebra, the "norm squared" of s = σ + Bt is:
  |s|² = s · s† = (σ + Bt)(σ - Bt) = σ² - B²t² = σ² + t²

Since B² = -1, this becomes a SUM OF SQUARES - unconditionally non-negative!
This is the "Cl(3,3) Trick" - positivity is algebraic, not analytic.
-/

/--
**Definition: Geometric Norm Squared**
The Cl(3,3) norm of s = σ + Bt under reversion.
|s|² = s · s† = σ² + t²
-/
def GeometricNormSq (sigma t : ℝ) : ℝ := sigma^2 + t^2

/--
**THEOREM: Geometric Norm is Non-Negative (The Cl(3,3) Trick)**
In split-signature algebra, |s|² = σ² + t² is a sum of squares.
This is UNCONDITIONALLY non-negative - no analysis required!
-/
theorem GeometricNormSq_nonneg (sigma t : ℝ) : 0 ≤ GeometricNormSq sigma t := by
  unfold GeometricNormSq
  apply add_nonneg <;> exact sq_nonneg _

/--
**THEOREM: Geometric Norm is Positive for Non-Zero Parameters**
|s|² > 0 unless σ = t = 0.
-/
theorem GeometricNormSq_pos (sigma t : ℝ) (h : sigma ≠ 0 ∨ t ≠ 0) :
    0 < GeometricNormSq sigma t := by
  unfold GeometricNormSq
  rcases h with hs | ht
  · have : 0 < sigma^2 := sq_pos_of_ne_zero hs
    linarith [sq_nonneg t]
  · have : 0 < t^2 := sq_pos_of_ne_zero ht
    linarith [sq_nonneg sigma]

/-!
## 2. The Cl(n,n) Squared Magnitude (using definitions from Axioms.lean)
-/

/--
**THEOREM: Cl(n,n) Squared Magnitude is Non-Negative**

This is TRIVIALLY true because it's a sum of squares of real numbers.
No complex analysis needed - pure real algebra!
-/
theorem ClSquaredMagnitude_nonneg (phi : GeometricTestFunction) (t : ℝ) :
    0 ≤ ClSquaredMagnitude phi t := by
  unfold ClSquaredMagnitude
  -- a² + b² ≥ 0 for any real a, b
  apply add_nonneg
  · exact sq_nonneg _
  · exact sq_nonneg _

/-!
## 3. Energy Properties
-/

/--
**Energy is Non-Negative**
-/
theorem LogSpaceEnergy_nonneg (phi : GeometricTestFunction) :
    0 ≤ LogSpaceEnergy phi := by
  unfold LogSpaceEnergy
  apply integral_nonneg
  intro x
  exact sq_nonneg _

/-!
## 4. The Prime Signal Positivity
-/

/--
**The Prime Weighting Function**
For n > 1: w(n) = log(n) · n^{-1/2}
This is ALWAYS POSITIVE for n ≥ 2.
-/
def PrimeWeight (n : ℕ) : ℝ :=
  if n > 1 then Real.log n * (n : ℝ)^(-(1/2 : ℝ)) else 0

/--
**Lemma: Prime weights are non-negative**
-/
theorem PrimeWeight_nonneg (n : ℕ) : 0 ≤ PrimeWeight n := by
  unfold PrimeWeight
  split_ifs with h
  · -- n > 1, so log(n) > 0 and n^{-1/2} > 0
    apply mul_nonneg
    · -- log(n) ≥ 0 for n ≥ 1
      apply Real.log_nonneg
      simp only [Nat.one_le_cast]
      omega
    · -- n^{-1/2} > 0
      apply Real.rpow_nonneg
      exact Nat.cast_nonneg n
  · -- n ≤ 1, weight is 0
    linarith

/--
**Lemma: Prime weights are strictly positive for n ≥ 2**
-/
theorem PrimeWeight_pos (n : ℕ) (hn : 2 ≤ n) : 0 < PrimeWeight n := by
  unfold PrimeWeight
  have h : n > 1 := by omega
  simp only [h, ↓reduceIte]
  apply mul_pos
  · -- log(n) > 0 for n ≥ 2
    apply Real.log_pos
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact this
  · -- n^{-1/2} > 0
    apply Real.rpow_pos_of_pos
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact this

/-!
## 5. The Cl(n,n) Positivity Theorem
-/

/--
**THEOREM: Prime Signal Positivity via Cl(n,n)**

The prime signal, when evaluated on squared magnitudes, gives:
  Σ_n w(n) · |φ̂(log n)|²_Cl

where:
- w(n) = log(n) · n^{-1/2} ≥ 0 (proven above)
- |φ̂(t)|²_Cl = [cos part]² + [sin part]² ≥ 0 (sum of squares!)

A sum of products of non-negative terms is non-negative.
This is PURE REAL ALGEBRA - no complex numbers!
-/
theorem Prime_Positivity_ClNN (phi : GeometricTestFunction) :
    0 ≤ ∑' (n : ℕ), PrimeWeight n * ClSquaredMagnitude phi (Real.log n) := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg
  · exact PrimeWeight_nonneg n
  · exact ClSquaredMagnitude_nonneg phi (Real.log n)

/-!
## Summary

**The Cl(n,n) Positivity Proof**:

1. **Fourier in Cl(n,n)** has two REAL parts:
   - Scalar: ∫ φ cos(tx) dx
   - B-coeff: -∫ φ sin(tx) dx

2. **Squared magnitude** is:
   |φ̂|² = [scalar]² + [B-coeff]² = sum of squares ≥ 0

3. **Prime weights** w(n) = log(n) · n^{-1/2} ≥ 0 for n ≥ 2

4. **Prime signal positivity**:
   Σ w(n) · |φ̂(log n)|² = Σ (positive) · (sum of squares) ≥ 0

**What's proven vs axiomatized**:
- PROVEN: GeometricNormSq_nonneg (σ² + t² ≥ 0, the Cl(3,3) trick)
- PROVEN: GeometricNormSq_pos (σ² + t² > 0 for non-zero parameters)
- PROVEN: ClSquaredMagnitude_nonneg (sum of squares)
- PROVEN: PrimeWeight_nonneg, PrimeWeight_pos
- PROVEN: Prime_Positivity_ClNN (sum of positives)
- PROVEN: LogSpaceEnergy_nonneg
- AXIOM (in Axioms.lean): Plancherel_ClNN (energy conservation)

**Note**: Weil_Positivity_Criterion was REMOVED (unused, equivalent to zeros_isolated).
The positivity → RH connection is now captured by zeros_isolated combined with
the functional equation.

**NO IMAGINARY NUMBERS** - everything is real sums of squares!
-/

end Riemann.ZetaSurface.GeometricPositivity

end
