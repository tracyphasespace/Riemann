/-!
# Job 2: Rayleigh Identity
# Agent Task: Prove rayleigh_decomposition

## Context
The Rayleigh Identity shows that Im⟨v, K(s)v⟩ decomposes as a weighted sum
of local charges Q_p(v), providing the spectral mechanism for zero centering.

## What You Need To Prove
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic

noncomputable section
open Real Complex BigOperators Finsupp

namespace Job2

-- GIVEN DEFINITIONS (do not modify) --

def Primes := { n : ℕ // n.Prime }
abbrev LocalSpace := ℂ × ℂ
def GlobalHilbertSpace := Primes →₀ LocalSpace

def localBivector (v : LocalSpace) : LocalSpace := (-v.2, v.1)

def localInner (u v : LocalSpace) : ℂ :=
  conj u.1 * v.1 + conj u.2 * v.2

def Q_local (v : LocalSpace) : ℝ := 2 * (conj v.1 * v.2).im

def coeff (s : ℂ) (p : Primes) : ℂ :=
  (Real.log (p : ℕ)) / ((p : ℕ) : ℂ) ^ s

def innerProd (u v : GlobalHilbertSpace) : ℂ :=
  (u.support ∪ v.support).sum fun p => localInner (u p) (v p)

-- HELPER LEMMAS TO PROVE --

/-- The local bivector is skew-Hermitian -/
lemma localBivector_skew_hermitian (u v : LocalSpace) :
    localInner u (localBivector v) = -localInner (localBivector u) v := by
  simp only [localInner, localBivector, neg_mul, mul_neg]
  ring

/-- Inner product with bivector is purely imaginary -/
lemma localInner_bivector_imaginary (v : LocalSpace) :
    (localInner v (localBivector v)).re = 0 := by
  simp only [localInner, localBivector, neg_mul]
  -- ⟨(x,y), (-y,x)⟩ = x̄·(-y) + ȳ·x = -x̄y + ȳx
  -- Real part: Re(-x̄y) + Re(ȳx) = 0 by conjugate symmetry
  sorry -- YOUR TASK: Complete this proof

/-- The imaginary part equals the local charge -/
lemma localInner_bivector_eq_charge (v : LocalSpace) :
    (localInner v (localBivector v)).im = Q_local v / 2 := by
  simp only [localInner, localBivector, Q_local]
  sorry -- YOUR TASK: Complete this proof

/-- Coefficient is real when s is real -/
lemma coeff_real_of_real (σ : ℝ) (p : Primes) :
    (coeff σ p).im = 0 := by
  simp only [coeff]
  -- log(p) is real, p^σ is real for real σ
  sorry -- YOUR TASK: Complete this proof

-- MAIN THEOREM TO PROVE --

/--
**The Rayleigh Decomposition**
The chiral energy decomposes as a weighted sum of local charges.
-/
theorem rayleigh_decomposition (s : ℂ) (v : GlobalHilbertSpace) :
    ∃ (weights : Primes → ℝ),
    (innerProd v (v.support.sum fun p => (coeff s p) • Finsupp.single p (localBivector (v p)))).im =
    v.support.sum fun p => weights p * Q_local (v p) := by
  -- Strategy:
  -- 1. Expand innerProd definition
  -- 2. Use localInner_bivector_eq_charge to relate to Q_local
  -- 3. Extract weights as (coeff s p).re
  sorry -- YOUR TASK: Complete this proof

end Job2
