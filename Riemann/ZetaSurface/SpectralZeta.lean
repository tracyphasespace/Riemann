/-
# SpectralZeta: Spectral Packaging of the Zeta-Surface Pipeline

This file records the **spectral layer** of the Riemann pipeline in a way that is
compatible with either completion strategy and any finite compression.

At this stage we stay *finite* in two senses:

* a prime cutoff `B` (so Euler products are finite), and
* a compression subspace `W` (so determinants are genuine matrix determinants).

## Core objects

* `CompletedModel` (CompletionCore.lean): an operator family `Op(s,B)` with
  adjoint symmetry `Op(s,B)† = Op(1 - conj(s),B)`.

* `CompressionData` (Compression.lean): a finite-dimensional compression giving
  the concrete determinant

    det_C(s,B) := det(I - A_C(s,B)).

This determinant is the "spectral inverse zeta" at finite level.

## What this file provides

1. A common reflection map `reflect(s) = 1 - conj(s)` and its fixed set.
2. Definitions of compressed spectral zeta (`zetaInvC`, `zeroSet`).
3. Re-exports of the *critical line reality* lemma (already in Compression.lean).
4. A clean hypothesis interface (`DetSymm`, `BridgeToEuler`) so the remaining
   hard steps can be proved as the project matures.
5. Operator-level spectral theory (`CharacteristicEq`, `RH_Spectral_Version`).

The RH-bearing content is expected to enter through:

* proving `DetSymm` from `CompletedModel.adjoint_symm` + matrix lemmas, and
* proving `BridgeToEuler` as compression quality improves (ZetaLinkFinite.lean).
-/

import Riemann.ZetaSurface
import Riemann.ZetaSurface.CompletionCore
import Riemann.ZetaSurface.SpectralReal
import Riemann.ZetaSurface.Compression
import Riemann.ZetaSurface.ZetaLinkFinite

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section
open scoped Real ComplexConjugate
open Complex

namespace Riemann.ZetaSurface.SpectralZeta

/-! ## 1. Reflection map -/

/-- The functional-equation involution: `s ↦ 1 - conj(s)`. -/
def reflect (s : ℂ) : ℂ := (1 : ℂ) - conj s

@[simp] theorem reflect_def (s : ℂ) : reflect s = (1 : ℂ) - conj s := rfl

/-- `reflect` is an involution. -/
@[simp] theorem reflect_involutive (s : ℂ) : reflect (reflect s) = s := by
  simp [reflect]

/-- The critical line is pointwise fixed by `reflect`. -/
theorem reflect_criticalLine (t : ℝ) : reflect (criticalLine t) = criticalLine t := by
  simpa [reflect, criticalLine, s_param] using (critical_fixed t)

/-! ## 2. Operator-Level Spectral Theory -/

variable (M : CompletedModel)

/--
The Characteristic Equation.
The zeta zeros correspond to singularities in the resolvent,
which map to eigenvalue 1 of the sieve operator.

CharacteristicEq(s) := ∃ v ≠ 0, Op(s,B) v = v
-/
def CharacteristicEq (s : ℂ) (B : ℕ) : Prop :=
  ∃ v : M.H, v ≠ 0 ∧ M.Op s B v = v

/--
Equivalently: 1 is in the point spectrum of Op(s, B).
-/
def HasEigenvalueOne (s : ℂ) (B : ℕ) : Prop :=
  ∃ v : M.H, v ≠ 0 ∧ M.Op s B v = (1 : ℂ) • v

theorem CharacteristicEq_iff_EigenvalueOne (s : ℂ) (B : ℕ) :
    CharacteristicEq M s B ↔ HasEigenvalueOne M s B := by
  unfold CharacteristicEq HasEigenvalueOne
  constructor <;> intro ⟨v, hv_ne, hv_eq⟩ <;> exact ⟨v, hv_ne, by simp [hv_eq]⟩

/--
On the critical line, Op(s) is self-adjoint.
Self-adjoint operators have real spectrum.
-/
theorem critical_selfadjoint (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (M.Op s B).adjoint = M.Op s B :=
  M.selfadjoint_critical t B

/--
**Key Observation**: Off the critical line, Op(s) is NOT self-adjoint.

If Re(s) ≠ 1/2, then Op(s)† = Op(1 - conj(s)) ≠ Op(s).
-/
theorem not_selfadjoint_off_critical (σ t : ℝ) (B : ℕ) (hσ : σ ≠ 1 / 2)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    (M.Op ((σ : ℂ) + (t : ℂ) * I) B).adjoint ≠ M.Op ((σ : ℂ) + (t : ℂ) * I) B := by
  intro h_eq
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs_def
  have h_adj := M.adjoint_symm s B
  rw [h_eq] at h_adj
  have h_s_eq : s = 1 - conj s := h_inj s (1 - conj s) h_adj
  have hs_re : s.re = σ := by
    simp only [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
               Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero]
  have h1_re : (1 - conj s).re = 1 - σ := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hs_re]
  have h_re : s.re = (1 - conj s).re := congrArg Complex.re h_s_eq
  rw [hs_re, h1_re] at h_re
  have : σ = 1/2 := by linarith
  exact hσ this

/--
**RH via Spectral Methods** (Conditional Version):

Given the spectral correspondence hypothesis and stability requirement,
the zero must lie on the critical line.
-/
theorem RH_Spectral_Version (s : ℂ) (B : ℕ)
    (_h_char : CharacteristicEq M s B)
    (h_stable : (M.Op s B).adjoint = M.Op s B)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    s.re = 1/2 := by
  have h_adj := M.adjoint_symm s B
  rw [h_stable] at h_adj
  have h_s_eq : s = 1 - conj s := h_inj s (1 - conj s) h_adj
  have h_re : s.re = (1 - conj s).re := congrArg Complex.re h_s_eq
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h_re
  linarith

/-! ## 3. Spectral zeta at finite cutoff and finite compression -/

variable {M : CompletedModel} (C : CompressionData M)

/-- The finite-compression, finite-cutoff "spectral inverse zeta". -/
def zetaInvC (s : ℂ) (B : ℕ) : ℂ :=
  CompressionData.detLike C s B

/-- Formal reciprocal (useful for notation; zeros are studied via `zetaInvC`). -/
def zetaC (s : ℂ) (B : ℕ) : ℂ := (zetaInvC C s B)⁻¹

/-- The zero set of the compressed spectral inverse zeta at cutoff `B`. -/
def zeroSet (B : ℕ) : Set ℂ := { s | zetaInvC C s B = 0 }

@[simp] theorem mem_zeroSet {B : ℕ} {s : ℂ} :
    s ∈ zeroSet C B ↔ zetaInvC C s B = 0 := Iff.rfl

/-! ## 4. Reality on the critical line -/

/-- On the critical line, the compressed determinant is real-valued. -/
theorem zetaInvC_real_on_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    (zetaInvC C s B).im = 0 := by
  intro s
  exact CompressionData.detLike_real_critical C t B

/-! ## 5. Symmetry hypotheses (interfaces) -/

/--
Compressed functional-equation symmetry for the determinant:

`conj(det_C(s,B)) = det_C(reflect(s),B)`.

This is the determinant-level reflection that should follow from
`CompletedModel.adjoint_symm` once the matrix-adjoint bookkeeping is completed.
-/
def DetSymm : Prop :=
  ∀ (s : ℂ) (B : ℕ),
    conj (zetaInvC C s B) = zetaInvC C (reflect s) B

/--
If `DetSymm` holds, then zeros occur in reflected pairs.
-/
theorem zeroSet_reflect_of_DetSymm {B : ℕ} (h : DetSymm C) {s : ℂ}
    (hs : s ∈ zeroSet C B) :
    reflect s ∈ zeroSet C B := by
  have hs0 : zetaInvC C s B = 0 := hs
  have h0 : zetaInvC C (reflect s) B = 0 := by
    simpa [hs0] using (h s B).symm
  exact h0

/--
Bridge hypothesis: the compressed determinant matches the finite Euler product.

At present this is staged as a *goal interface*; ZetaLinkFinite.lean contains the
finite objects (`ZInv`) and the program to prove convergence/accuracy.
-/
def BridgeToEuler : Prop :=
  ∀ (s : ℂ) (B : ℕ), zetaInvC C s B = ZInv B s

/-- Under the bridge hypothesis, zeros of the compressed determinant are zeros of `ZInv`. -/
theorem zeroSet_subset_ZInv_zeros {B : ℕ} (h : BridgeToEuler C) :
    zeroSet C B ⊆ { s | ZInv B s = 0 } := by
  intro s hs
  have : zetaInvC C s B = 0 := hs
  simpa [h s B] using this

/-! ## 6. A finite RH statement (at cutoff B, compression C) -/

/--
Finite RH predicate for the compressed determinant at cutoff `B`:
all zeros have real part `1/2`.
-/
def FiniteRH (B : ℕ) : Prop :=
  ∀ (s : ℂ), zetaInvC C s B = 0 → s.re = (1/2 : ℝ)

/-- `FiniteRH` implies the zero set is contained in the critical line. -/
theorem zeroSet_subset_criticalLine {B : ℕ} (h : FiniteRH C B) :
    zeroSet C B ⊆ { s | s.re = (1/2 : ℝ) } := by
  intro s hs
  exact h s hs

/-! ## 7. Spectral interpretation (eigenvalue 1 condition) -/

/-- An eigenvalue-1 condition for the compressed matrix `A = mat(s,B)`. -/
def hasEigOne (s : ℂ) (B : ℕ) : Prop :=
  ∃ v : C.ι → ℂ, v ≠ 0 ∧ (CompressionData.mat C s B).mulVec v = v

/--
`det(I - A) = 0` implies `A` has eigenvalue 1.

This is standard finite-dimensional linear algebra (singularity ↔ nontrivial kernel).
-/
theorem detLike_zero_implies_hasEigOne (s : ℂ) (B : ℕ) :
    zetaInvC C s B = 0 → hasEigOne C s B := by
  classical
  intro hz
  -- zetaInvC = det(charMat) = det(I - A)
  unfold zetaInvC CompressionData.detLike at hz
  -- det(charMat) = 0 implies ∃ v ≠ 0, charMat *ᵥ v = 0
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hz
  obtain ⟨v, hv_ne, hv_eq⟩ := hz
  -- charMat = 1 - mat, so (1 - mat) *ᵥ v = 0 means v - mat *ᵥ v = 0, i.e., mat *ᵥ v = v
  unfold hasEigOne
  use v, hv_ne
  unfold CompressionData.charMat at hv_eq
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec] at hv_eq
  -- hv_eq : v - mat *ᵥ v = 0, so mat *ᵥ v = v
  exact (sub_eq_zero.mp hv_eq).symm

/--
On the critical line, the matrix `A` is Hermitian, so its spectrum is real.
-/
theorem spectrum_real_on_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * I
    Matrix.conjTranspose (CompressionData.mat C s B) = CompressionData.mat C s B :=
  CompressionData.mat_hermitian_critical C t B

/-! ## Physical Summary: The Spectral Bridge

The spectral approach to RH:

1. **Operator Construction**: K(s) = Σ_p [α(s,p)·T_p + β(s,p)·T_p⁻¹]
2. **Adjoint Symmetry**: K(s)† = K(1 - conj(s))
3. **Critical Fixed Point**: s ↦ 1 - conj(s) fixes exactly Re(s) = 1/2
4. **Self-Adjoint on Critical**: K(s)† = K(s) when Re(s) = 1/2
5. **Spectral Reality**: Self-adjoint ⇒ real eigenvalues
6. **Zeta Correspondence**: ζ(s) = 0 ↔ 1 ∈ spectrum(K(s))
7. **Stability Argument**: Non-self-adjoint ⇒ unstable ⇒ no zeros

At the compression level:
- `zetaInvC = det(I - A_C)` is the finite spectral invariant
- `DetSymm` captures functional equation symmetry
- `BridgeToEuler` links to finite Euler product
- `FiniteRH` is the finite-level RH statement

The critical line emerges as the unique locus where the operator
dynamics are "balanced" (self-adjoint), allowing stable zeros.
-/

end Riemann.ZetaSurface.SpectralZeta

end
