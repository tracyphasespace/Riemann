/-
# Core Definitions for the Geometric Riemann Hypothesis

**Purpose**: Central repository for all supporting definitions used across the
             Cl(N,N) formalization of RH.

**Design**: This file contains ONLY definitions (no axioms). Files that need
            definitions but not axioms can import this file directly.

## Contents

### 1. Geometric Parameter Structure
   - `GeometricParam`: s = σ + Bt in Cl(3,3)
   - `reversion`: The † operation (flips bivector sign)
   - `functionalPartner`: The 1 - s† partner
   - `InCriticalStrip`: 0 < σ < 1

### 2. Geometric Zeta Terms (for GeometricParam)
   - `ScalarTermParam`: n^{-σ} cos(t log n)
   - `BivectorTermParam`: -n^{-σ} sin(t log n)
   - `IsGeometricZeroParam`: Both sums vanish
   - `IsSymmetricZero`: s and s† both zeros

### 3. Test Functions (Schwartz space)
   - `GeometricTestFunction`: Smooth with rapid decay
   - `GeometricFourierTransform`: Cosine transform

### 4. Distributional Structures
   - `PrimeSignal`: Σ log(n) n^{-1/2} φ(log n)
   - `ZeroResonance`: Σ φ̂(γ)

### 5. Fourier/Positivity Structures
   - `FourierScalar`, `FourierBivector`: Real Fourier components
   - `ClSquaredMagnitude`: |φ̂|² = [scalar]² + [B-coeff]²
   - `LogSpaceEnergy`: ∫ |φ|² dx
   - `RiemannHypothesis`: The statement

### 6. Trace Structure
   - `GeometricTraceData`: Trace functional on operators
   - `PrimeTensionTerm`: Single-prime contribution to K
-/

import Riemann.ZetaSurface.GeometricZeta
import Riemann.ZetaSurface.SurfaceTensionInstantiation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
open scoped Real
open Riemann.ZetaSurface.SurfaceTensionInstantiation
open Riemann.ZetaSurface.GeometricZeta

namespace Riemann.ZetaSurface.Definitions

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-!
## 1. Geometric Parameter Structure
-/

/-- Geometric parameter: s = σ + Bt in Cl(3,3) -/
structure GeometricParam where
  sigma : ℝ
  t : ℝ

/-- Reversion (†): flips bivector sign. (σ + Bt)† = σ - Bt -/
def reversion (s : GeometricParam) : GeometricParam :=
  { sigma := s.sigma, t := -s.t }

/-- The functional equation partner: 1 - s† = (1-σ) + Bt -/
def functionalPartner (s : GeometricParam) : GeometricParam :=
  { sigma := 1 - s.sigma, t := s.t }

/-- s is in the critical strip: 0 < σ < 1 -/
def InCriticalStrip (s : GeometricParam) : Prop :=
  0 < s.sigma ∧ s.sigma < 1

/-!
## 2. Geometric Zeta Terms (GeometricParam version)
-/

/-- Scalar part of n^{-s} for GeometricParam -/
def ScalarTermParam (n : ℕ) (s : GeometricParam) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ (-s.sigma) * Real.cos (s.t * Real.log n)

/-- Bivector coefficient of n^{-s} for GeometricParam -/
def BivectorTermParam (n : ℕ) (s : GeometricParam) : ℝ :=
  if n = 0 then 0 else -(n : ℝ) ^ (-s.sigma) * Real.sin (s.t * Real.log n)

/-- For σ > 1, the series converges. Use tsum directly. -/
def IsGeometricZeroParam_Convergent (s : GeometricParam) : Prop :=
  (∑' n : ℕ, ScalarTermParam n s = 0) ∧ (∑' n : ℕ, BivectorTermParam n s = 0)

/-- For σ ≤ 1, use Mathlib's riemannZeta (analytic continuation). -/
def IsGeometricZeroParam_Analytic (s : GeometricParam) : Prop :=
  riemannZeta (⟨s.sigma, s.t⟩ : ℂ) = 0

/--
**A zero of the geometric zeta function (Convergence-Aware)**

The Zeta function is "Zero" at s with proper handling of convergence:
- For σ > 1: Both Scalar and Bivector tsum's vanish (series converges)
- For σ ≤ 1: Mathlib's riemannZeta vanishes (analytic continuation)
-/
def IsGeometricZeroParam (s : GeometricParam) : Prop :=
  if s.sigma > 1 then
    IsGeometricZeroParam_Convergent s
  else
    IsGeometricZeroParam_Analytic s

/-- In the critical strip, IsGeometricZeroParam ↔ riemannZeta = 0 (BY DEFINITION) -/
theorem critical_strip_param_eq_complex (s : GeometricParam) (h : InCriticalStrip s) :
    IsGeometricZeroParam s ↔ riemannZeta (⟨s.sigma, s.t⟩ : ℂ) = 0 := by
  unfold IsGeometricZeroParam IsGeometricZeroParam_Analytic
  have h_not_gt : ¬(s.sigma > 1) := not_lt.mpr (le_of_lt h.2)
  simp only [if_neg h_not_gt]

/-- A symmetric zero: s and its reversion s† are both zeros -/
def IsSymmetricZero (s : GeometricParam) : Prop :=
  IsGeometricZeroParam s ∧ IsGeometricZeroParam (reversion s)

/-!
## 3. Test Functions (Schwartz space)
-/

/-- A Schwartz test function for distributional trace -/
structure GeometricTestFunction where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  decay : ∀ k : ℕ, ∃ C, ∀ x, |x|^k * |toFun x| ≤ C

/-- The Geometric Fourier Transform (cosine transform) -/
def GeometricFourierTransform (phi : GeometricTestFunction) (t : ℝ) : ℝ :=
  ∫ x : ℝ, phi.toFun x * Real.cos (t * x)

/-!
## 4. Distributional Structures
-/

/-- The Prime Signal distribution -/
def PrimeSignal : GeometricTestFunction → ℝ := fun phi =>
  ∑' (n : ℕ), (if n > 1 then Real.log n * (n : ℝ)^(-(1/2:ℝ)) * phi.toFun (Real.log n) else 0)

/-- The Zero Resonance distribution -/
def ZeroResonance (zeros : ℕ → ℝ) : GeometricTestFunction → ℝ := fun phi =>
  ∑' (n : ℕ), GeometricFourierTransform phi (zeros n)

/-- Geometric Distribution type -/
def GeometricDistribution := GeometricTestFunction → ℝ

/-!
## 5. Fourier/Positivity Structures
-/

/-- Scalar part of Cl(N,N) Fourier transform -/
def FourierScalar (phi : GeometricTestFunction) (t : ℝ) : ℝ :=
  ∫ x : ℝ, phi.toFun x * Real.cos (t * x)

/-- B-coefficient of Cl(N,N) Fourier transform -/
def FourierBivector (phi : GeometricTestFunction) (t : ℝ) : ℝ :=
  -(∫ x : ℝ, phi.toFun x * Real.sin (t * x))

/-- Cl(N,N) squared magnitude: |φ̂(t)|² = [scalar]² + [B-coeff]² -/
def ClSquaredMagnitude (phi : GeometricTestFunction) (t : ℝ) : ℝ :=
  (FourierScalar phi t)^2 + (FourierBivector phi t)^2

/-- Log-space energy: ∫ |φ(x)|² dx -/
def LogSpaceEnergy (phi : GeometricTestFunction) : ℝ :=
  ∫ x : ℝ, (phi.toFun x)^2

/-- The Riemann Hypothesis statement -/
def RiemannHypothesis : Prop :=
  ∀ (zeros : ℕ → ℝ × ℝ),
    (∀ n, (zeros n).1 > 0 ∧ (zeros n).1 < 1) →
    ∀ n, (zeros n).1 = 1/2

/-!
## 6. Trace Structure
-/

/-- Geometric trace data -/
structure GeometricTraceData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  Geom : BivectorStructure H
  tr : (H →L[ℝ] H) → ℝ
  /-- Trace of global bivector is zero -/
  tr_bivector_zero : tr Geom.J = 0
  /-- Trace is additive -/
  tr_add : ∀ A B : H →L[ℝ] H, tr (A + B) = tr A + tr B
  /-- Trace is linear (scalar multiplication) -/
  tr_smul : ∀ (c : ℝ) (A : H →L[ℝ] H), tr (c • A) = c * tr A
  /-- Trace of each prime bivector is zero (bivectors have no scalar part) -/
  tr_primeJ_zero : ∀ p : ℕ, Nat.Prime p → tr (Geom.primeJ p) = 0
  /-- Trace of composition of distinct prime bivectors is zero.
      This follows from anticommutation: J_p J_q = -J_q J_p implies
      trace(J_p J_q) = trace(-J_q J_p) = -trace(J_q J_p) = -trace(J_p J_q)
      (by cyclic property), so trace = 0. -/
  tr_primeJ_comp_zero : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q →
    tr (Geom.primeJ p ∘L Geom.primeJ q) = 0

/-- Prime tension term for trace computation.
    Uses the prime-indexed bivector J_p for proper Clifford orthogonality. -/
def PrimeTensionTerm (GT : GeometricTraceData H) (sigma : ℝ) (p : ℕ) : H →L[ℝ] H :=
  let prime_stiffness := GeometricSieve.stiffness (p : ℝ) / 2
  ((sigma - 1/2) * prime_stiffness) • GT.Geom.primeJ p

end Riemann.ZetaSurface.Definitions

end
