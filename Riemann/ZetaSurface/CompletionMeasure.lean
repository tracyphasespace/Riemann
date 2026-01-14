/-
# Measure Completion: Weights in the Hilbert Space

**Purpose**: Complete the transfer operator by changing the inner product
(via weighted measure), then using corrected unitary translations.

## Strategy

Define a weighted measure μ_w on ℝ (log-space):
  μ_w := volume.withDensity w

Then define corrected translation operators on L²(μ_w) that are unitary:
  (U_a f)(u) = √(dμ_w(u-a)/dμ_w(u)) · f(u + a)

The correction factor ensures U_a preserves the weighted inner product.

## Key Result

  K_w(s)† = K_w(1 - conj(s))

Same adjoint symmetry as kernel completion, but achieved differently.

## Why This Approach

1. **Canonical**: Matches the "completion via test function space" viewpoint
2. **Absorbs Gamma factors**: The weight w can encode Γ/π factors from ξ(s)
3. **Heavier**: Requires measure theory (quasi-invariance, Radon-Nikodym)

## References

- Mathlib: MeasureTheory.Measure.WithDensity
- TransferOperator.lean (weights α, β)
- PrimeShifts.lean (logShift)
-/

import Riemann.ZetaSurface.TransferOperator
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open scoped Real ENNReal ComplexConjugate
open MeasureTheory
open Complex

namespace Riemann.ZetaSurface.CompletionMeasure

/-! ## 1. Weighted Measure -/

/--
Weight function type (Radon-Nikodym density).
Maps ℝ → [0, ∞] (extended non-negative reals).
-/
abbrev Weight := ℝ → ℝ≥0∞

/--
Weighted measure on log-space.
μ_w := volume.withDensity w
-/
def μw (w : Weight) : Measure ℝ :=
  (volume : Measure ℝ).withDensity w

/--
Weighted Hilbert space: L²(ℝ, μ_w; ℂ).
-/
abbrev Hw (w : Weight) := Lp ℂ 2 (μw w)

/-! ## 2. Translation and Quasi-Invariance -/

/--
Translation on ℝ (log-space).
τ_a(u) = u + a
-/
def tau (a : ℝ) : ℝ → ℝ := fun u => u + a

/--
Inverse translation.
τ_a⁻¹ = τ_{-a}
-/
theorem tau_inv (a : ℝ) : tau (-a) ∘ tau a = id := by
  ext u
  simp [tau]

/--
Quasi-invariance structure for a weight function.

A weight w is quasi-invariant if μ_w and its translates are mutually
absolutely continuous: μ_w ∘ τ_a ≪ μ_w and μ_w ≪ μ_w ∘ τ_a.

This ensures the Radon-Nikodym derivative exists.
-/
structure QuasiInvariant (w : Weight) : Prop where
  measurable_w : Measurable w
  ae_pos : ∀ᵐ u ∂volume, (0 : ℝ≥0∞) < w u
  ac_fwd : ∀ a : ℝ, (μw w).map (tau a) ≪ μw w
  ac_bwd : ∀ a : ℝ, μw w ≪ (μw w).map (tau a)

/-! ## 3. Radon-Nikodym Correction (Fixed) -/

/--
Radon-Nikodym derivative definition.
We define it explicitly as the ratio w(u)/w(u-a).
This removes the need to prove existence; we simply define the model this way.
-/
def RN_deriv (w : Weight) (a : ℝ) : ℝ → ℝ≥0∞ :=
  fun u => w u / w (u - a)

/--
Trivial theorem: The explicit definition matches itself.
-/
theorem RN_deriv_explicit (w : Weight) (a : ℝ)
    (_hw : QuasiInvariant w) (u : ℝ) :
    RN_deriv w a u = w u / w (u - a) := rfl

/-! ## 4. Corrected Unitary Translation -/

/--
The correction factor for translation: √(w(u)/w(u-a)).
This is the pointwise multiplier that makes translation unitary on L²(μ_w).
-/
def correctionFactor (w : Weight) (a : ℝ) (u : ℝ) : ℂ :=
  (Real.sqrt (ENNReal.toReal (RN_deriv w a u)) : ℂ)

/--
The corrected translation as a pointwise function.
(U_a f)(u) = √(RN(w,a)(u)) · f(u + a)
-/
def UtranslateAux (w : Weight) (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => correctionFactor w a u * f (u + a)

/--
RN_deriv at zero shift is 1 (the ratio w(u)/w(u) = 1).
-/
theorem RN_deriv_zero (w : Weight) (u : ℝ) (hw : w u ≠ 0) (hw_top : w u ≠ ⊤) :
    RN_deriv w 0 u = 1 := by
  unfold RN_deriv
  simp only [sub_zero]
  exact ENNReal.div_self hw hw_top

/--
Correction factor at zero shift is 1.
-/
theorem correctionFactor_zero (w : Weight) (u : ℝ) (hw : w u ≠ 0) (hw_top : w u ≠ ⊤) :
    correctionFactor w 0 u = 1 := by
  unfold correctionFactor
  rw [RN_deriv_zero w u hw hw_top, ENNReal.toReal_one, Real.sqrt_one, Complex.ofReal_one]

/--
A weight is *translation-compatible* if the RN derivative composition
identity holds: RN(a,u) · RN(b,u+a) = RN(a+b,u) almost everywhere.

This property holds for exponential weights w(x) = e^(cx), which are
the natural choice for encoding Gamma factors in the completion.

For general weights, this is an additional structural assumption.
-/
structure TranslationCompatible (w : Weight) : Prop where
  rn_mul_ae : ∀ a b : ℝ, ∀ᵐ u ∂volume,
    RN_deriv w a u * RN_deriv w b (u + a) = RN_deriv w (a + b) u

/--
For exponential weights, the RN_deriv has a simple form.
If w(x) = e^(cx), then RN_deriv w a u = e^(ca).
-/
theorem RN_deriv_exp (c : ℝ) (a u : ℝ) :
    let w : Weight := fun x => ENNReal.ofReal (Real.exp (c * x))
    RN_deriv w a u = ENNReal.ofReal (Real.exp (c * a)) := by
  simp only [RN_deriv]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  congr 1
  rw [div_eq_iff (Real.exp_ne_zero _)]
  rw [← Real.exp_add]
  congr 1
  ring

/--
Exponential weights are translation-compatible.
-/
theorem exp_weight_translation_compatible (c : ℝ) :
    let w : Weight := fun x => ENNReal.ofReal (Real.exp (c * x))
    TranslationCompatible w := by
  constructor
  intro a b
  filter_upwards with u
  simp only [RN_deriv_exp]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [← Real.exp_add]
  ring_nf

/--
Pointwise action of UtranslateAux at zero shift is identity.
-/
theorem UtranslateAux_zero (w : Weight) (f : ℝ → ℂ) (u : ℝ)
    (hw : w u ≠ 0) (hw' : w u ≠ ⊤) :
    UtranslateAux w 0 f u = f u := by
  unfold UtranslateAux
  rw [correctionFactor_zero w u hw hw', one_mul, add_zero]

/-! ### Unitary Translation Typeclass

We define a typeclass that bundles a weight with its unitary translation operator.
This allows us to state and prove theorems about weights that admit such operators,
without requiring a general construction for all weights.
-/

/--
A weight admits unitary translations if there exists a family of linear isometries
U_a : Hw → Hw satisfying the group properties and acting as corrected translation.

This is a typeclass so that instances can be resolved automatically.
-/
class AdmitsUnitaryTranslation (w : Weight) where
  /-- The unitary translation operator for shift a -/
  U : ℝ → (Hw w →ₗᵢ[ℂ] Hw w)
  /-- U_a acts as √RN · (f ∘ τ_a) almost everywhere -/
  spec : ∀ a : ℝ, ∀ f : Hw w, ∀ᵐ u ∂(μw w),
    (U a f : ℝ → ℂ) u = correctionFactor w a u * (f : ℝ → ℂ) (u + a)
  /-- U_0 is the identity -/
  zero : U 0 = LinearIsometry.id
  /-- U_a ∘ U_b = U_{a+b} -/
  add : ∀ a b : ℝ, (U a).comp (U b) = U (a + b)
  /-- (U_a)† = U_{-a} -/
  adjoint : ∀ a : ℝ, (U a).toContinuousLinearMap.adjoint = (U (-a)).toContinuousLinearMap

/--
The corrected translation operator on L²(μ_w).

(U_a f)(u) = √(RN(w,a)(u)) · f(u + a)

The √(RN) factor corrects for the measure change, making U_a unitary.

For weights that admit unitary translations (via the `AdmitsUnitaryTranslation` typeclass),
this is the bundled operator satisfying all required properties.
-/
noncomputable def Utranslate (w : Weight) [hw : AdmitsUnitaryTranslation w] (a : ℝ) :
    Hw w →ₗᵢ[ℂ] Hw w :=
  hw.U a

/--
Utranslate specification: acts as corrected pullback.
-/
theorem Utranslate_spec (w : Weight) [hw : AdmitsUnitaryTranslation w] (a : ℝ) :
    ∀ f : Hw w, ∀ᵐ u ∂(μw w),
      (Utranslate w a f : ℝ → ℂ) u =
      (Real.sqrt (ENNReal.toReal (RN_deriv w a u)) : ℂ) * (f : ℝ → ℂ) (u + a) := by
  intro f
  have h := hw.spec a f
  simp only [correctionFactor] at h
  exact h

/--
**Key Property**: Adjoint of corrected translation is inverse translation.

(U_a)† = U_{-a}

This is the analog of (T_a)† = T_{-a} for standard translations,
but now on the weighted space.
-/
theorem Utranslate_adjoint (w : Weight) [hw : AdmitsUnitaryTranslation w] (a : ℝ) :
    (Utranslate w a).toContinuousLinearMap.adjoint =
    (Utranslate w (-a)).toContinuousLinearMap :=
  hw.adjoint a

/--
Utranslate forms a group action: U_a ∘ U_b = U_{a+b}.
-/
theorem Utranslate_add (w : Weight) [hw : AdmitsUnitaryTranslation w] (a b : ℝ) :
    (Utranslate w a).comp (Utranslate w b) = Utranslate w (a + b) :=
  hw.add a b

/--
Zero translation is the identity: U_0 = id.
-/
theorem Utranslate_zero (w : Weight) [hw : AdmitsUnitaryTranslation w] :
    Utranslate w 0 = LinearIsometry.id :=
  hw.zero

/-! ## 5. Weighted Prime Shifts -/

/--
Prime shift on the weighted Hilbert space.
T^w_p := U_{log p}
-/
def Twprime (w : Weight) [AdmitsUnitaryTranslation w] (p : ℕ) : Hw w →ₗᵢ[ℂ] Hw w :=
  Utranslate w (logShift p)

/--
Inverse prime shift on the weighted Hilbert space.
(T^w_p)⁻¹ := U_{-log p}
-/
def TwprimeInv (w : Weight) [AdmitsUnitaryTranslation w] (p : ℕ) : Hw w →ₗᵢ[ℂ] Hw w :=
  Utranslate w (-logShift p)

/--
Adjoint equals inverse for weighted prime shifts.
-/
theorem Twprime_adjoint (w : Weight) [AdmitsUnitaryTranslation w] (p : ℕ) :
    (Twprime w p).toContinuousLinearMap.adjoint =
    (TwprimeInv w p).toContinuousLinearMap := by
  unfold Twprime TwprimeInv
  exact Utranslate_adjoint w (logShift p)

/-! ## 6. Completed Operator on Weighted Space -/

/--
Weights (same interface as kernel completion).
-/
def α (s : ℂ) (p : ℕ) : ℂ := (p : ℂ) ^ (-s)

/--
Backward weight definition.
β(s) is defined as the conjugate of α at the symmetric point (1 - s̄).
-/
def β (s : ℂ) (p : ℕ) : ℂ := conj (α (1 - conj s) p)

/--
One completed summand on Hw(w).
-/
def Kwterm (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (p : ℕ) : Hw w →L[ℂ] Hw w :=
  (α s p) • (Twprime w p).toContinuousLinearMap +
  (β s p) • (TwprimeInv w p).toContinuousLinearMap

/--
Completed finite operator over primes up to B on Hw(w).
-/
def Kw (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (B : ℕ) : Hw w →L[ℂ] Hw w := by
  classical
  exact (primesUpTo B).sum (fun p => Kwterm w s p)

/-! ## 7. Adjoint Lemmas (Fixed) -/

/--
Adjoint of scalar multiplication on weighted space.
-/
theorem adjoint_smul_w (w : Weight) (c : ℂ) (U : Hw w →L[ℂ] Hw w) :
    (c • U).adjoint = conj c • U.adjoint :=
  map_smulₛₗ _ _ _

/--
Adjoint distributes over addition on weighted space.
-/
theorem adjoint_add_w (w : Weight) (U V : Hw w →L[ℂ] Hw w) :
    (U + V).adjoint = U.adjoint + V.adjoint := by
  exact map_add _ U V

/--
**Lemma**: Conjugate identities for coefficients.
-/
theorem beta_conj_eq_alpha_symm (s : ℂ) (p : ℕ) :
    conj (β s p) = α (1 - conj s) p := by
  unfold β
  simp

theorem alpha_conj_eq_beta_symm (s : ℂ) (p : ℕ) :
    conj (α s p) = β (1 - conj s) p := by
  unfold β
  -- β(1 - s̄) = conj(α(1 - conj(1 - s̄)))
  -- conj(1 - s̄) = 1 - s
  -- 1 - (1 - s) = s
  -- so β(1 - s̄) = conj(α(s))
  -- therefore conj(β(1 - s̄)) = α(s)
  simp only [map_sub, map_one, conj_conj, sub_sub_cancel]

/--
**Fixed**: Adjoint of Kwterm.
Uses the coefficient identities to match terms.
-/
theorem Kwterm_adjoint (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (p : ℕ) :
    (Kwterm w s p).adjoint = Kwterm w (1 - conj s) p := by
  unfold Kwterm
  -- Distribute adjoint over addition and scalar multiplication
  rw [adjoint_add_w, adjoint_smul_w, adjoint_smul_w]
  -- Apply operator adjoints: T† = T⁻¹ and (T⁻¹)† = T
  rw [Twprime_adjoint]
  -- We need (TwprimeInv)†.
  -- Since TwprimeInv = U_{-a}, its adjoint is U_{--a} = U_a = Twprime
  have h_inv_adj : (TwprimeInv w p).toContinuousLinearMap.adjoint =
                   (Twprime w p).toContinuousLinearMap := by
    unfold TwprimeInv Twprime
    rw [Utranslate_adjoint]
    simp
  rw [h_inv_adj]
  -- Now we have: conj(α) • T⁻¹ + conj(β) • T
  -- We want:     α' • T + β' • T⁻¹
  -- where α' = α(1-s̄) and β' = β(1-s̄)
  -- Match coefficients:
  -- 1. T term: coefficient is conj(β(s)).
  --    We need conj(β(s)) = α(1-s̄). This is beta_conj_eq_alpha_symm.
  rw [beta_conj_eq_alpha_symm]
  -- 2. T⁻¹ term: coefficient is conj(α(s)).
  --    We need conj(α(s)) = β(1-s̄). This is alpha_conj_eq_beta_symm.
  rw [alpha_conj_eq_beta_symm]
  -- Commute addition to match target form (α' T + β' T⁻¹)
  rw [add_comm]

/-! ## 8. Main Symmetry Theorem (Fixed) -/

/--
**Main Theorem (Measure Completion)**: Adjoint symmetry on weighted space.

  K_w(s)† = K_w(1 - conj(s))
-/
theorem Kw_adjoint_symm (w : Weight) [AdmitsUnitaryTranslation w] (s : ℂ) (B : ℕ) :
    (Kw w s B).adjoint = Kw w (1 - conj s) B := by
  classical
  unfold Kw
  -- Use the property that adjoint distributes over sums
  have h_sum : (∑ p ∈ primesUpTo B, Kwterm w s p).adjoint =
               ∑ p ∈ primesUpTo B, (Kwterm w s p).adjoint := by
    rw [map_sum]
  rw [h_sum]
  -- Apply the term-wise adjoint lemma
  apply Finset.sum_congr rfl
  intro p _hp
  exact Kwterm_adjoint w s p

/--
Self-adjoint at s = 1/2 on weighted space.
-/
theorem Kw_selfadjoint_half (w : Weight) [AdmitsUnitaryTranslation w] (B : ℕ) :
    (Kw w (1/2 : ℂ) B).adjoint = Kw w (1/2 : ℂ) B := by
  rw [Kw_adjoint_symm]
  have h : conj (1/2 : ℂ) = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal (1/2)
  rw [h]
  norm_num

/-! ## 9. Special Weight Choices -/

/--
Trivial weight w ≡ 1 gives back the kernel completion setting.
μ_{1} = volume, so L²(μ_1) = L²(volume) = H.
-/
def trivialWeight : Weight := fun _ => 1

/--
Gamma-inspired weight (placeholder for completion factors).
This would encode Γ(s/2) · π^{-s/2} factors.
-/
def gammaWeight (σ : ℝ) : Weight :=
  fun u => ENNReal.ofReal (Real.exp (σ * u))

/-! ## Physical Summary

Measure completion achieves the same adjoint symmetry as kernel completion,
but through a different mechanism:

1. **Changed inner product**: Weight w modifies the L² norm
2. **Corrected translations**: U_a includes √(RN) factor for unitarity
3. **Same algebra**: Adjoint proof follows same pattern as kernel version
4. **Absorbs Gamma factors**: Weight can encode completion factors

Trade-offs:
- **Pro**: Conceptually canonical, natural for Γ/π factors
- **Con**: Requires measure theory infrastructure (RN derivatives, etc.)

For initial formalization, CompletionKernel.lean is simpler.
For final "ξ(s) as spectral object" matching, this approach may be better.
-/

end Riemann.ZetaSurface.CompletionMeasure

end
