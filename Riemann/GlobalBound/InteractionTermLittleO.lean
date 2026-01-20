/-
# Phase 5: The Interaction Term (Signal vs Noise) - Little-o Version

This file uses the stronger `IsLittleO` hypothesis instead of `IsBigO` with exponent.
The little-o formulation: Noise = o(Signal) as t → ∞.

This is a cleaner formulation that directly captures "noise is negligible".
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Asymptotics.Defs

noncomputable section
open Real BigOperators Filter Asymptotics

namespace GlobalBound

/-!
# Phase 5: The Interaction Term (Signal vs Noise)

We explicitly model the "Interference" that standard analysis struggles with.
-/

/-- The Phase of prime p at height t -/
def theta (p : ℕ) (t : ℝ) : ℝ := t * Real.log p

/--
The "Rotor" for prime p.
In the simplified scalar projection, this is just sin(θ).
In full Cl(3,3), this is a bivector.
-/
def Rotor (p : ℕ) (t : ℝ) : ℝ := Real.sin (theta p t)

/--
The "Ideal Energy" (Signal).
This is the sum of squares (Pythagorean addition).
Corresponds to the "Stiffness" of the lattice.
-/
def IdealEnergyList (primes : List ℕ) (t : ℝ) : ℝ :=
  primes.foldl (fun acc p => acc + (Rotor p t)^2) 0

/--
The "Real Energy" (Analytic).
This is the square of the sum.
Includes constructive/destructive interference.
-/
def RealEnergyList (primes : List ℕ) (t : ℝ) : ℝ :=
  (primes.foldl (fun acc p => acc + Rotor p t) 0) ^ 2

/--
The "Interaction Term" (Noise).
Noise = Real - Ideal = Sum_{p ≠ q} sin(θ_p) sin(θ_q)
-/
def InteractionTermList (primes : List ℕ) (t : ℝ) : ℝ :=
  RealEnergyList primes t - IdealEnergyList primes t

/-!
## The Hypothesis: Asymptotic Orthogonality
This replaces the "Hand-waving" about ergodicity.
We define a structure that asserts the Noise is sub-dominant.
-/

structure PairCorrelationHypothesis (primes : List ℕ) : Prop where
  /--
  The Interaction Term grows slower than the Ideal Energy.
  Noise = o(Signal)
  -/
  noise_is_little_o :
    IsLittleO atTop (fun t => InteractionTermList primes t) (fun t => IdealEnergyList primes t)

/-!
## Key Lemmas
-/

/-- The decomposition: RealEnergy = IdealEnergy + InteractionTerm. -/
theorem real_eq_ideal_plus_interaction (primes : List ℕ) (t : ℝ) :
    RealEnergyList primes t = IdealEnergyList primes t + InteractionTermList primes t := by
  unfold InteractionTermList
  ring

/-- RealEnergy is non-negative (it's a square) -/
theorem real_energy_nonneg (primes : List ℕ) (t : ℝ) :
    0 ≤ RealEnergyList primes t := by
  unfold RealEnergyList
  exact sq_nonneg _

end GlobalBound

end
