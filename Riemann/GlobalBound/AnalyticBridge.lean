import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Riemann.GlobalBound.OrthogonalBivector

noncomputable section
open Real BigOperators GlobalBound

namespace GlobalBound

/-!
# Phase 3: The Analytic Bridge (Critique Fix)

## Addressing the Reviewer's Critique
1. **Scalar Bridge Fix:** We cannot use the scalar part of a bivector (which is 0).
   We must define a **Coefficient Extraction Functional** `Π_Spec`.
2. **Von Mangoldt Fix:** We define the Von Mangoldt operator `Λ` acting on the
   orthogonal basis, rejecting mixed states (composites).

## The Rigorous Map
Geometric Space (Cl(∞))  <-->  Analytic Space (Dirichlet Series)
      Vector v_p         <-->     Coefficient c_p
-/

/-!
## 1. The Coefficient Extraction Functional (Π_Spec)
Instead of taking a trace (which vanishes), we project onto the prime basis.
-/

/--
The Projection Operator π_p.
Extracts the component of the vector along the p-th prime axis.
-/
def project_p {S : Finset ℕ} (p : ℕ) (v : PrimeIndexedVec S) : ℝ :=
  v.coeff p

/--
**The Spectral Extraction Functional (Π_Spec)**
This is the linear map that converts the Geometric State into the Analytic Sum.
It replaces the incorrect "Scalar Part" Lemma 3.1.
-/
def spectral_extraction {S : Finset ℕ} (v : PrimeIndexedVec S) (weights : ℕ → ℝ) : ℝ :=
  S.sum (fun p => (v.coeff p) * (weights p))

/-!
## 2. The Homomorphism Theorem (Corrected Lemma 3.1)
We prove that extracting coefficients from the sum of rotors
is equivalent to summing the phases.
-/

/--
**Theorem: Linearity of Extraction**
The extraction of the total phase equals the sum of individual phases.
This restores the "Bridge" without using the incorrect scalar trace.
-/
theorem extraction_homomorphism (S : Finset ℕ) (t : ℝ) :
    spectral_extraction (sieveVec S t) (fun _ => 1) =
    S.sum (fun p => Real.sin (t * Real.log (p : ℝ))) := by
  unfold spectral_extraction sieveVec
  apply Finset.sum_congr rfl
  intro p hp
  simp only [PrimeIndexedVec.mk.injEq, mul_one, if_pos hp]

/--
**Theorem: Weighted Extraction**
Extraction with log weights gives the weighted phase sum.
-/
theorem weighted_extraction (S : Finset ℕ) (t : ℝ) :
    spectral_extraction (sieveVec S t) (fun p => Real.log (p : ℝ)) =
    S.sum (fun p => Real.sin (t * Real.log (p : ℝ)) * Real.log (p : ℝ)) := by
  unfold spectral_extraction sieveVec
  apply Finset.sum_congr rfl
  intro p hp
  simp only [PrimeIndexedVec.mk.injEq, if_pos hp]

/-!
## 3. Connection to the Orthogonal Structure
-/

/--
**Theorem: Extraction Respects Orthogonality**
The spectral extraction of an axis vector e_p with weight w gives w(p).
-/
theorem extraction_of_axis (S : Finset ℕ) (p : ℕ) (hp : p ∈ S) (weights : ℕ → ℝ) :
    spectral_extraction (axis S p hp) weights = weights p := by
  unfold spectral_extraction axis
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _hq hqp
    simp only [mul_eq_zero]
    left
    rw [if_neg hqp]
  · intro hp'
    exact (hp' hp).elim

/--
**Theorem: Energy via Extraction**
The squared magnitude equals the spectral extraction with squared coefficients.
This connects the geometric energy to the analytic sum.
-/
theorem energy_via_extraction (S : Finset ℕ) (t : ℝ) :
    magSq (sieveVec S t) =
    spectral_extraction (sieveVec S t) (fun p => (sieveVec S t).coeff p) := by
  unfold magSq innerProduct spectral_extraction
  rfl

/-!
## 4. Von Mangoldt Operator (Simplified)

For a prime p, the Von Mangoldt function Λ(p) = log p.
In our orthogonal basis, this becomes scalar multiplication.
-/

/--
**The Von Mangoldt Weight Function**
On primes, Λ(p) = log p. This is the weight in the Explicit Formula.
-/
def vonMangoldt_weight (p : ℕ) : ℝ :=
  if Nat.Prime p then Real.log (p : ℝ) else 0

/--
**Theorem: Von Mangoldt Extraction**
Extraction with von Mangoldt weights on a prime set gives the log-weighted sum.
-/
theorem vonMangoldt_extraction (S : Finset ℕ) (t : ℝ) (hpr : ∀ p ∈ S, Nat.Prime p) :
    spectral_extraction (sieveVec S t) vonMangoldt_weight =
    S.sum (fun p => Real.sin (t * Real.log (p : ℝ)) * Real.log (p : ℝ)) := by
  unfold spectral_extraction sieveVec vonMangoldt_weight
  apply Finset.sum_congr rfl
  intro p hp
  simp only [PrimeIndexedVec.mk.injEq, if_pos hp, if_pos (hpr p hp)]

end GlobalBound
