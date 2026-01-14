/-
# Translation Operators on L²(ℝ; ℝ) with Cl(3,3) Structure

**Purpose**: Define unitary translation operators on the real Hilbert space L²(ℝ, du; ℝ).

## Architecture: Pure Cl(3,3)

The Hilbert space is **real-valued**: HR = L²(ℝ; ℝ).
The "complex" structure comes from **Cl(3,3)** via the bivector B where B² = -1.
This is mathematically equivalent to ℂ but geometrically more natural.

## Key Results

1. Translation T_a : f ↦ f(· + a) is a LinearIsometry (norm-preserving)
2. Group law: T_0 = id, T_a ∘ T_b = T_{a+b}
3. Adjoint = inverse: (T_a)† = T_{-a}

## References

- Mathlib: MeasureTheory.Function.L2Space
- Mathlib: Analysis.InnerProductSpace.Adjoint
- Riemann/GA/Cl33.lean: B_internal with B² = -1
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Real ENNReal

namespace Riemann.ZetaSurface

/-! ## 1. The Real Hilbert Space -/

/--
The base Hilbert space: L²(ℝ, du; ℝ) with Lebesgue measure.

This is **real-valued**. The "complex" structure for spectral analysis
comes from Cl(3,3) via the bivector B where B² = -1.
See `Riemann/GA/Cl33.lean` for the Clifford algebra.
-/
abbrev HR := Lp ℝ 2 (volume : Measure ℝ)

/-! ## 2. Measure Preservation -/

/--
Translation by a is measure-preserving on Lebesgue measure.
This is the geometric engine: volume is translation-invariant.
-/
theorem measurePreserving_translate (a : ℝ) :
    MeasurePreserving (fun u => u + a) (volume : Measure ℝ) volume :=
  measurePreserving_add_right volume a

/-! ## 3. The Unitary Translation Operator -/

/--
The translation operator T_a on L²(ℝ; ℝ) as a **LinearIsometry**.

Action: (T_a f)(x) = f(x + a)

Properties:
- Isometric: ‖T_a f‖ = ‖f‖ (from measure preservation)
- Unitary: (T_a)† = T_{-a}

The Cl(3,3) action provides complex structure via B where B² = -1.
-/
def L2TranslateR (a : ℝ) : HR →ₗᵢ[ℝ] HR :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun u => u + a) (measurePreserving_translate a)

/-! ## 4. Group Laws -/

/--
T_0 = id: Translation by 0 is the identity.
Proof: f(x + 0) = f(x)
-/
theorem L2TranslateR_zero : L2TranslateR 0 = LinearIsometry.id := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate 0)
  refine h.trans ?_
  filter_upwards with x
  simp only [Function.comp_apply, add_zero, LinearIsometry.id_apply]

/--
T_a ∘ T_b = T_{a+b}: Translations compose additively.
Proof: f(x + a + b) = f(x + (a + b))
-/
theorem L2TranslateR_add (a b : ℝ) :
    (L2TranslateR a).comp (L2TranslateR b) = L2TranslateR (a + b) := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  have h_Tb := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate b)
  have h_Tab := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate (a + b))
  have h_Ta := Lp.coeFn_compMeasurePreserving (L2TranslateR b f) (measurePreserving_translate a)
  refine h_Ta.trans ?_
  have qmp := (measurePreserving_translate a).quasiMeasurePreserving
  have step := qmp.ae_eq_comp h_Tb
  refine step.trans ?_
  have step2 : ((↑↑f ∘ (· + b)) ∘ (· + a)) =ᵐ[volume] (↑↑f ∘ (· + (a + b))) := by
    filter_upwards with x; simp only [Function.comp_apply]; ring_nf
  exact step2.trans h_Tab.symm

/--
Translations commute: T_a ∘ T_b = T_b ∘ T_a.
-/
theorem L2TranslateR_comm (a b : ℝ) :
    (L2TranslateR a).comp (L2TranslateR b) = (L2TranslateR b).comp (L2TranslateR a) := by
  rw [L2TranslateR_add, L2TranslateR_add, add_comm]

/-! ## 5. Adjoint Structure -/

/--
**Key Theorem**: Adjoint of translation equals inverse.

(T_a)† = T_{-a}

Proof: Change of variables in ⟨T_a f, g⟩ = ∫ f(u+a)g(u) du = ∫ f(v)g(v-a) dv = ⟨f, T_{-a} g⟩
-/
-- Define the translation as a LinearIsometryEquiv
def L2TranslateREquiv (a : ℝ) : HR ≃ₗᵢ[ℝ] HR where
  toLinearEquiv := {
    toFun := L2TranslateR a
    map_add' := (L2TranslateR a).map_add
    map_smul' := (L2TranslateR a).map_smul
    invFun := L2TranslateR (-a)
    left_inv := fun f => by
      have h : (L2TranslateR (-a)).comp (L2TranslateR a) = LinearIsometry.id := by
        rw [L2TranslateR_add, neg_add_cancel, L2TranslateR_zero]
      exact congrFun (congrArg DFunLike.coe h) f
    right_inv := fun f => by
      have h : (L2TranslateR a).comp (L2TranslateR (-a)) = LinearIsometry.id := by
        rw [L2TranslateR_add, add_neg_cancel, L2TranslateR_zero]
      exact congrFun (congrArg DFunLike.coe h) f
  }
  norm_map' := (L2TranslateR a).norm_map

theorem L2TranslateREquiv_symm (a : ℝ) :
    (L2TranslateREquiv a).symm = L2TranslateREquiv (-a) := by
  apply LinearIsometryEquiv.ext
  intro f
  apply Lp.ext
  -- symm of L2TranslateREquiv a is L2TranslateR (-a) by definition
  -- L2TranslateREquiv (-a) is L2TranslateR (-a) by definition
  rfl

theorem L2TranslateR_adjoint (a : ℝ) :
    (L2TranslateR a).toContinuousLinearMap.adjoint =
    (L2TranslateR (-a)).toContinuousLinearMap := by
  -- Use the fact that for LinearIsometryEquiv, adjoint = symm
  have h := LinearIsometryEquiv.adjoint_eq_symm (L2TranslateREquiv a)
  -- The key: L2TranslateREquiv a as ContinuousLinearMap equals L2TranslateR a
  have heq : (L2TranslateREquiv a : HR →L[ℝ] HR) = (L2TranslateR a).toContinuousLinearMap := rfl
  rw [heq] at h
  rw [h]
  -- Now show: (L2TranslateREquiv a).symm = L2TranslateR (-a) as CLMs
  rfl

/--
Unitary property: T_a† ∘ T_a = id.
-/
theorem L2TranslateR_unitary (a : ℝ) :
    (L2TranslateR a).toContinuousLinearMap.adjoint ∘L
    (L2TranslateR a).toContinuousLinearMap =
    ContinuousLinearMap.id ℝ HR := by
  rw [L2TranslateR_adjoint]
  -- Now need: L2TranslateR(-a) ∘L L2TranslateR(a) = id
  have h : (L2TranslateR (-a)).comp (L2TranslateR a) = LinearIsometry.id := by
    rw [L2TranslateR_add, neg_add_cancel, L2TranslateR_zero]
  -- ContinuousLinearMap extensionality
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  -- Show the results are ae equal (in fact equal as Lp elements)
  have step : L2TranslateR (-a) (L2TranslateR a f) = f := by
    have hs := congrFun (congrArg DFunLike.coe h) f
    simp only [LinearIsometry.comp_apply, LinearIsometry.id_apply] at hs
    exact hs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
             LinearIsometry.coe_toContinuousLinearMap, step]
  exact Filter.EventuallyEq.refl _ _

/-! ## 6. Legacy: Complex-Valued Space (for backward compatibility) -/

/--
Legacy complex Hilbert space: L²(ℝ, du; ℂ).
Prefer `HR` with Cl(3,3) structure for new code.
-/
abbrev H := Lp ℂ 2 (volume : Measure ℝ)

/--
Legacy complex translation operator.
-/
def L2Translate (a : ℝ) : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u => u + a) (measurePreserving_translate a)

theorem L2Translate_zero : L2Translate 0 = LinearIsometry.id := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate 0)
  refine h.trans ?_
  filter_upwards with x
  simp only [Function.comp_apply, add_zero, LinearIsometry.id_apply]

theorem L2Translate_add (a b : ℝ) :
    (L2Translate a).comp (L2Translate b) = L2Translate (a + b) := by
  apply LinearIsometry.ext
  intro f
  apply Lp.ext
  have h_Tb := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate b)
  have h_Tab := Lp.coeFn_compMeasurePreserving f (measurePreserving_translate (a + b))
  have h_Ta := Lp.coeFn_compMeasurePreserving (L2Translate b f) (measurePreserving_translate a)
  refine h_Ta.trans ?_
  have qmp := (measurePreserving_translate a).quasiMeasurePreserving
  have step := qmp.ae_eq_comp h_Tb
  refine step.trans ?_
  have step2 : ((↑↑f ∘ (· + b)) ∘ (· + a)) =ᵐ[volume] (↑↑f ∘ (· + (a + b))) := by
    filter_upwards with x; simp only [Function.comp_apply]; ring_nf
  exact step2.trans h_Tab.symm

theorem L2Translate_comm (a b : ℝ) :
    (L2Translate a).comp (L2Translate b) = (L2Translate b).comp (L2Translate a) := by
  rw [L2Translate_add, L2Translate_add, add_comm]

/-- Complex translation as a LinearIsometryEquiv for adjoint proof. -/
def L2TranslateEquiv (a : ℝ) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := {
    toFun := L2Translate a
    map_add' := (L2Translate a).map_add
    map_smul' := (L2Translate a).map_smul
    invFun := L2Translate (-a)
    left_inv := fun f => by
      have h : (L2Translate (-a)).comp (L2Translate a) = LinearIsometry.id := by
        rw [L2Translate_add, neg_add_cancel, L2Translate_zero]
      exact congrFun (congrArg DFunLike.coe h) f
    right_inv := fun f => by
      have h : (L2Translate a).comp (L2Translate (-a)) = LinearIsometry.id := by
        rw [L2Translate_add, add_neg_cancel, L2Translate_zero]
      exact congrFun (congrArg DFunLike.coe h) f
  }
  norm_map' := (L2Translate a).norm_map

theorem L2Translate_adjoint (a : ℝ) :
    (L2Translate a).toContinuousLinearMap.adjoint =
    (L2Translate (-a)).toContinuousLinearMap := by
  have h := LinearIsometryEquiv.adjoint_eq_symm (L2TranslateEquiv a)
  have heq : (L2TranslateEquiv a : H →L[ℂ] H) = (L2Translate a).toContinuousLinearMap := rfl
  rw [heq] at h
  rw [h]
  rfl

/-! ## Physical Summary: Cl(3,3) Unitary Group

The translation operators form a **one-parameter unitary group** on HR:

1. **Real Hilbert space**: HR = L²(ℝ; ℝ), not complex
2. **Cl(3,3) structure**: The bivector B with B² = -1 provides complex structure
3. **Unitary**: T_a is an isometry with T_a† = T_{-a}
4. **Group law**: T_a ∘ T_b = T_{a+b}, T_0 = id

This is the geometric foundation for the zeta transfer operator:
- Prime translations T_{log p} shift in log-coordinates
- The weight p^{-s} = exp(-s·log p) becomes exp(-σ·log p)·exp(-B·t·log p)
- On critical line σ = 1/2: pure rotation by B·t·log p
-/

end Riemann.ZetaSurface

end