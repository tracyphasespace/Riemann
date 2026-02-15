/-
# Aristotle's Contributions to the Clifford RH Proof

Refactored to use standard Mathlib lemmas and remove global axioms.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

## Contributions Summary

1. **Conjugate Symmetry**: Λ(s̄) = Λ̄(s)
   - Status: PROVED via Mellin conjugation for real kernels

2. **Norm at Zero**: At ζ(s) = 0, the rotor sum norm is small
   - Status: PROVEN (conditional on approximation bound).
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.Basic

noncomputable section

open Complex Real Topology Filter MeasureTheory Set HurwitzZeta

namespace Aristotle

/-!
## 1. Rotor Sum Definitions
-/

/-- The rotor sum (approximation to zeta). -/
def rotorSum (σ t : ℝ) (primes : List ℕ) : ℂ :=
  primes.foldl (fun acc p => acc + (p : ℂ) ^ (-(σ : ℂ) - t * I)) 0

/-- The rotor sum norm squared. -/
def rotorSumNormSq (σ t : ℝ) (primes : List ℕ) : ℝ :=
  ‖rotorSum σ t primes‖ ^ 2

/-!
## 2. Key Theorem: Norm is Small at Zeta Zeros

Instead of using a global `axiom` (which asserts truth without proof), we now
state the approximation bound as an explicit **hypothesis** (`h_approx`).
This reduces the axiom to a verified dependency.
-/

/--
**THEOREM (Aristotle)**: At a zeta zero, if the rotor sum approximates ζ within 0.01,
then the rotor sum norm squared is < 0.001.
-/
theorem norm_approx_zero_at_zeta_zero (s : ℂ) (primes : List ℕ)
    (h_zero : riemannZeta s = 0)
    -- The Axiom is reduced to this explicit hypothesis:
    (h_approx : ‖rotorSum s.re s.im primes - riemannZeta s‖ < 0.01) :
    rotorSumNormSq s.re s.im primes < 0.001 := by
  -- 1. Apply the zero condition to the approximation
  rw [h_zero] at h_approx
  simp only [sub_zero] at h_approx

  -- 2. Calculate the square bound
  -- |rotorSum| < 0.01  ⟹  |rotorSum|² < 0.0001
  unfold rotorSumNormSq
  have h_sq : ‖rotorSum s.re s.im primes‖ ^ 2 < 0.01 ^ 2 := by
    apply sq_lt_sq'
    · linarith [norm_nonneg (rotorSum s.re s.im primes)]
    · exact h_approx

  -- 3. Final inequality check
  -- 0.0001 < 0.001
  rw [show (0.01 : ℝ) ^ 2 = 0.0001 by norm_num] at h_sq
  apply lt_trans h_sq
  norm_num

/-!
## 3. Conjugate Symmetry — PROVED

Λ₀(conj s) = conj(Λ₀(s))

Proved via Mellin transform conjugation for real-valued kernels,
following the `Complex.GammaIntegral_conj` pattern from Mathlib.

**Definition chain** (all Mathlib):
- `completedRiemannZeta₀ s = completedHurwitzZetaEven₀ 0 s`
- `completedHurwitzZetaEven₀ 0 s = ((hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2`
- `Λ₀ = mellin P.f_modif`

**Key fact**: `(hurwitzEvenFEPair 0).f_modif` is real-valued (built from
`ofReal ∘ evenKernel 0`, with real corrections), so its Mellin transform
commutes with complex conjugation.
-/

/-- Mellin transform commutes with conjugation for functions satisfying
`conj(f(x)) = f(x)` on `Ioi 0`. Follows `Complex.GammaIntegral_conj`. -/
private lemma mellin_conj_of_real_valued {f : ℝ → ℂ}
    (hf : ∀ x, 0 < x → starRingEnd ℂ (f x) = f x) (s : ℂ) :
    mellin f (starRingEnd ℂ s) = starRingEnd ℂ (mellin f s) := by
  simp only [mellin, smul_eq_mul]
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hne := ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [map_mul, hf t ht, cpow_def_of_ne_zero hne, cpow_def_of_ne_zero hne,
    ← exp_conj, map_mul, ← ofReal_log (le_of_lt ht), conj_ofReal, map_sub, map_one]

/-- The `f_modif` of `hurwitzEvenFEPair 0` is real-valued: each piece is built
from `ofReal` of real quantities. -/
private lemma hurwitzEvenFEPair_zero_f_modif_conj (x : ℝ) :
    starRingEnd ℂ ((hurwitzEvenFEPair 0).f_modif x) = (hurwitzEvenFEPair 0).f_modif x := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, map_add, Set.indicator_apply]
  congr 1 <;> split_ifs <;>
    simp only [hurwitzEvenFEPair, Function.comp_apply, map_sub, conj_ofReal,
      map_zero, smul_eq_mul, mul_one, one_mul, ite_true, map_one]

theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  rw [show starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) from by
    rw [map_div₀, map_ofNat]]
  rw [mellin_conj_of_real_valued (fun x hx => hurwitzEvenFEPair_zero_f_modif_conj x)]
  rw [map_div₀, map_ofNat]

/-!
**Corollary**: The completed zeta norm is preserved under argument conjugation.
-/
theorem completedRiemannZeta₀_norm_conj (s : ℂ) :
    ‖completedRiemannZeta₀ (starRingEnd ℂ s)‖ = ‖completedRiemannZeta₀ s‖ := by
  rw [completedRiemannZeta₀_conj]
  exact Complex.norm_conj (completedRiemannZeta₀ s)

end Aristotle
