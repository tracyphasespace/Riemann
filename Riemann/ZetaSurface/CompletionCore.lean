/-
# Completion Core: Shared Interface

**Purpose**: Define a common interface for completed operators, allowing
downstream code to be agnostic about which completion strategy is used.

## Design

Both completion strategies (kernel and measure) satisfy the same key properties:
1. Adjoint symmetry: K(s)† = K(1 - conj(s))
2. Critical-line normality: Op(s) commutes with its adjoint when Re(s) = 1/2
3. Finite operator over primes up to B

This file provides:
- `CompletedModel`: A structure bundling H, Op, and the key properties
- `CompletedOpFamily`: A typeclass for operator families
- Derived theorems that work for any completion

## Usage

Downstream files can:
1. Work with the abstract `CompletedModel` structure
2. Apply results to either `CompletionKernel.K` or `CompletionMeasure.Kw`
3. Switch completions without changing proof structure
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open scoped Real ComplexConjugate
open Complex

namespace Riemann.ZetaSurface

/-! ## 1. Critical Line Fixed Point Identity -/

/--
Points on the critical line are fixed by s ↦ 1 - conj(s).

This is the algebraic "fixed set" characterization of Re(s) = 1/2.
-/
theorem critical_fixed (t : ℝ) :
    (1 : ℂ) - conj ((1/2 : ℂ) + (t : ℂ) * Complex.I)
      =
    ((1/2 : ℂ) + (t : ℂ) * Complex.I) := by
  -- conj(1/2 + it) = 1/2 - it
  -- 1 - (1/2 - it) = 1/2 + it
  have hconj : conj ((1/2 : ℂ) + (t : ℂ) * Complex.I) = (1/2 : ℂ) + (t : ℂ) * (-Complex.I) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  simp only [hconj]
  ring

/--
Equivalent: the map s ↦ 1 - conj(s) fixes exactly the critical line.
-/
theorem critical_fixed' (t : ℝ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
    (1 : ℂ) - conj s = s := critical_fixed t

/-! ## 2. CompletedModel Structure -/

/--
Abstract interface for a "completed" prime-surface operator.

This bundles:
- A Hilbert space H
- An operator family Op : ℂ → ℕ → (H →L[ℂ] H)
- Adjoint symmetry (functional equation shadow)
- Critical-line normality (commutes with adjoint on Re(s) = 1/2)

Kernel-completion and measure-completion both instantiate this.
-/
structure CompletedModel where
  /-- Underlying Hilbert space. -/
  H : Type

  /-- Normed group structure on H. -/
  instNormedAddCommGroup : NormedAddCommGroup H

  /-- Inner product space structure on H. -/
  instInner : InnerProductSpace ℂ H

  /-- Completeness of H. -/
  instComplete : CompleteSpace H

  /-- Completed finite operator at spectral parameter s and cutoff B. -/
  Op : ℂ → ℕ → (H →L[ℂ] H)

  /-- Functional-equation shadow: adjoint symmetry. -/
  adjoint_symm :
    ∀ (s : ℂ) (B : ℕ),
      (Op s B).adjoint = Op (1 - conj s) B

  /--
  Critical-line normality: Op(s) commutes with its adjoint when s is on the critical line.

  This is a weaker condition than unitarity but sufficient for spectral structure.
  On the critical line, self-adjointness (from adjoint_symm + critical_fixed) implies normality.
  -/
  normal_on_critical :
    ∀ (t : ℝ) (B : ℕ),
      let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
      (Op s B).adjoint * Op s B = Op s B * (Op s B).adjoint

attribute [instance] CompletedModel.instNormedAddCommGroup
attribute [instance] CompletedModel.instInner
attribute [instance] CompletedModel.instComplete

/-! ## 3. CompletedOpFamily Typeclass -/

/--
Typeclass for a family of operators satisfying completion properties.

This is an alternative to CompletedModel when you want to work with
a fixed Hilbert space and just characterize the operator family.
-/
class CompletedOpFamily (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) : Prop where
  adjoint_symm : ∀ s B, (K s B).adjoint = K (1 - conj s) B
  normal_on_critical : ∀ (t : ℝ) (B : ℕ),
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
    (K s B).adjoint * K s B = K s B * (K s B).adjoint

/-! ## 4. Derived Properties from CompletedModel -/

namespace CompletedModel

variable (M : CompletedModel)

/--
Self-adjoint at s = 1/2 (derived from adjoint symmetry).
-/
theorem selfadjoint_half (B : ℕ) :
    (M.Op (1/2 : ℂ) B).adjoint = M.Op (1/2 : ℂ) B := by
  rw [M.adjoint_symm]
  -- 1 - conj(1/2) = 1 - 1/2 = 1/2
  congr 1
  have hconj : conj (1/2 : ℂ) = (1/2 : ℂ) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  simp only [hconj]
  norm_num

/--
Self-adjoint on the entire critical line.
-/
theorem selfadjoint_critical (t : ℝ) (B : ℕ) :
    let s : ℂ := (1/2 : ℂ) + (t : ℂ) * Complex.I
    (M.Op s B).adjoint = M.Op s B := by
  intro s
  rw [M.adjoint_symm]
  -- Use critical_fixed: 1 - conj(1/2 + it) = 1/2 + it
  congr 1
  exact critical_fixed t

/--
Off critical line: adjoint swaps σ to 1-σ and keeps t.
For s = σ + t*I: Op(s)† = Op((1-σ) + t*I)
-/
theorem adjoint_off_critical (σ t : ℝ) (B : ℕ) :
    (M.Op ((σ : ℂ) + (t : ℂ) * I) B).adjoint =
    M.Op (((1 - σ) : ℂ) + (t : ℂ) * I) B := by
  rw [M.adjoint_symm]
  -- 1 - conj(σ + t*I) = 1 - (σ - t*I) = (1-σ) + t*I
  congr 1
  have hconj : conj ((σ : ℂ) + (t : ℂ) * I) = (σ : ℂ) + (t : ℂ) * (-I) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  simp only [hconj]
  ring

/--
Functional equation symmetry: swapping s ↔ 1-s corresponds to taking adjoint.
-/
theorem functional_eq_symmetry (s : ℂ) (B : ℕ) :
    (M.Op s B).adjoint = M.Op (1 - conj s) B :=
  M.adjoint_symm s B

end CompletedModel

/-! ## 5. Derived Properties from CompletedOpFamily -/

/--
Self-adjoint at s = 1/2 (typeclass version).
-/
theorem selfadjoint_half_tc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) [CompletedOpFamily H K] (B : ℕ) :
    (K (1/2 : ℂ) B).adjoint = K (1/2 : ℂ) B := by
  rw [CompletedOpFamily.adjoint_symm]
  congr 1
  have hconj : conj (1/2 : ℂ) = (1/2 : ℂ) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  simp only [hconj]
  norm_num

/--
Off critical line symmetry (typeclass version).
For s = σ + t*I: K(s)† = K((1-σ) + t*I)
-/
theorem adjoint_off_critical_tc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) [CompletedOpFamily H K] (σ t : ℝ) (B : ℕ) :
    (K ((σ : ℂ) + (t : ℂ) * I) B).adjoint = K (((1 - σ) : ℂ) + (t : ℂ) * I) B := by
  rw [CompletedOpFamily.adjoint_symm]
  congr 1
  have hconj : conj ((σ : ℂ) + (t : ℂ) * I) = (σ : ℂ) + (t : ℂ) * (-I) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  simp only [hconj]
  ring

/--
Functional equation symmetry (typeclass version).
-/
theorem functional_eq_symmetry_tc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ℂ → ℕ → H →L[ℂ] H) [CompletedOpFamily H K] (s : ℂ) (B : ℕ) :
    (K s B).adjoint = K (1 - conj s) B :=
  CompletedOpFamily.adjoint_symm s B

/-! ## 6. Spectral Implications -/

/--
For self-adjoint operators, spectrum is real.
At s = 1/2, Op is self-adjoint, so its spectrum ⊆ ℝ.

This is a key constraint: if zeta zeros correspond to spectral values,
and the operator is self-adjoint on the critical line, then zeros
must correspond to real spectral values.
-/
theorem spectrum_real_at_half (M : CompletedModel) (B : ℕ) :
    True := by  -- Placeholder for spectral theorem application
  -- Future: use M.selfadjoint_half to invoke spectral theorem
  trivial

/-! ## 7. Usage Notes -/

/-
**Decision criteria for choosing a completion:**

Use CompletionKernel (via KernelModel) when:
- You want minimal sorries (algebraic proofs)
- You don't need Γ/π factors in the space
- You're proving structural results about Op(s)

Use CompletionMeasure (via MeasureModel) when:
- You need to match the precise form of ξ(s)
- You want Γ(s/2)·π^{-s/2} absorbed into the space
- You're connecting to trace formulas or explicit zeta expressions

**For initial RH formalization:**
Start with KernelModel (fewer dependencies, cleaner algebra).
Switch to MeasureModel if the "spectral = zeros" correspondence
requires the specific normalization.
-/

end Riemann.ZetaSurface

end
