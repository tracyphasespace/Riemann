/-!
# Job 5: Bivector Technical Lemmas
# Agent Task: Prove 4 helper lemmas for spectral theory

## Context
These are foundational lemmas about the bivector operator B_p
acting on the local 2D space ℂ².
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
open Complex

namespace Job5

-- DEFINITIONS --

abbrev LocalSpace := ℂ × ℂ

def localBivector (v : LocalSpace) : LocalSpace := (-v.2, v.1)

def localInner (u v : LocalSpace) : ℂ :=
  conj u.1 * v.1 + conj u.2 * v.2

def Q_local (v : LocalSpace) : ℝ := 2 * (conj v.1 * v.2).im

def Primes := { n : ℕ // n.Prime }

def coeff (s : ℂ) (p : Primes) : ℂ :=
  (Real.log (p : ℕ)) / ((p : ℕ) : ℂ) ^ s

-- LEMMAS TO PROVE --

/-- Lemma 1: Bivector squares to negation -/
lemma localBivector_sq (v : LocalSpace) :
    localBivector (localBivector v) = (-v.1, -v.2) := by
  simp only [localBivector]
  constructor <;> ring

/-- Lemma 2: Bivector is skew-Hermitian -/
lemma localBivector_skew_hermitian (u v : LocalSpace) :
    localInner u (localBivector v) = -localInner (localBivector u) v := by
  simp only [localInner, localBivector, neg_mul, mul_neg]
  ring

/-- Lemma 3: Inner product with bivector is purely imaginary -/
lemma localInner_bivector_imaginary (v : LocalSpace) :
    (localInner v (localBivector v)).re = 0 := by
  simp only [localInner, localBivector]
  -- ⟨(x,y), (-y,x)⟩ = conj(x)*(-y) + conj(y)*x
  -- = -conj(x)*y + conj(y)*x
  -- Re part = Re(-conj(x)*y) + Re(conj(y)*x)
  -- = -Re(conj(x)*y) + Re(conj(y)*x)
  -- = -Re(conj(x)*y) + Re(conj(conj(x)*y))  [since conj(y)*x = conj(conj(x)*y)]
  -- = -Re(z) + Re(conj(z)) = 0 for any z
  sorry -- YOUR TASK: Complete using Complex.add_conj

/-- Lemma 4: Imaginary part equals local charge -/
lemma localInner_bivector_eq_charge (v : LocalSpace) :
    (localInner v (localBivector v)).im = Q_local v / 2 := by
  simp only [localInner, localBivector, Q_local]
  -- ⟨(x,y), (-y,x)⟩ = -conj(x)*y + conj(y)*x
  -- Im part = Im(-conj(x)*y + conj(y)*x)
  -- = -Im(conj(x)*y) + Im(conj(y)*x)
  -- For conj(y)*x = conj(conj(x)*y):
  -- Im(z) + Im(conj(z)) = 0, so Im(conj(y)*x) = -Im(conj(x)*y)
  -- Wait, that's not quite right...
  -- Let's compute directly:
  -- Im(-conj(x)*y) = -Im(conj(x)*y)
  -- Im(conj(y)*x) = Im(conj(y)*x)
  -- Need: -Im(conj(x)*y) + Im(conj(y)*x) = (conj(x)*y).im
  sorry -- YOUR TASK: Complete

/-- Lemma 5: Coefficient is real when s is real -/
lemma coeff_real_of_real (σ : ℝ) (p : Primes) :
    (coeff σ p).im = 0 := by
  simp only [coeff]
  -- log(p) : ℝ, so (log p : ℂ).im = 0
  -- (p : ℂ)^σ for real σ and positive p is real
  -- Division of reals is real
  have h1 : (Real.log (p : ℕ) : ℂ).im = 0 := by simp [Complex.ofReal_im]
  have h2 : ((p : ℕ) : ℂ) ^ (σ : ℂ) = ((p : ℕ) : ℝ) ^ σ := by
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg p)]
    simp
  sorry -- YOUR TASK: Complete

/-- Lemma 6: Inner product conjugate symmetry -/
lemma innerProd_conj_symm (u v : LocalSpace) :
    localInner u v = conj (localInner v u) := by
  simp only [localInner]
  -- conj(conj(v.1)*u.1 + conj(v.2)*u.2)
  -- = conj(conj(v.1)*u.1) + conj(conj(v.2)*u.2)
  -- = v.1*conj(u.1) + v.2*conj(u.2)
  -- = conj(u.1)*v.1 + conj(u.2)*v.2  [by commutativity]
  sorry -- YOUR TASK: Complete using map_add, map_mul

end Job5
