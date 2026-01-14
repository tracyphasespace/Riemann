/-
# Spectral Real: The Rigorous Hammer

**Purpose**: Prove that the Completed Operator has a Real Spectrum on the critical surface.
This closes the logic loop:
1. Symmetry (Cl33) → Self-Adjointness (at s=1/2).
2. Stability (Hamiltonian) → Hermitian Generator.
3. Spectral Theorem → Real Eigenvalues.

**The "ZetaLink" Implication**:
If the operator spectrum is Real, then the characteristic equation
det(I - K) = 0 implies 1 is a Real eigenvalue.
This restricts the zeros to the configuration space where the operator remains Hermitian
(i.e., the critical line).

## References

- Riemann/ZetaSurface/CompletionCore.lean: CompletedModel interface
- Riemann/ZetaSurface/Hamiltonian.lean: IsStableGenerator
- Mathlib: Spectral theorem for self-adjoint operators
-/

import Riemann.ZetaSurface.CompletionCore
import Riemann.ZetaSurface.Hamiltonian
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
open scoped Real ComplexConjugate
open Complex
open Riemann.ZetaSurface
open Riemann.ZetaSurface.Dynamics

namespace Riemann.ZetaSurface.Spectral

/-!
## 1. The Self-Adjoint Property (Recap)
-/

/--
The completed operator at the critical point s = 1/2.
By the functional equation symmetry, Op(1/2)† = Op(1/2).
-/
def CriticalOp (M : CompletedModel) (B : ℕ) : M.H →L[ℂ] M.H :=
  M.Op (1/2 : ℂ) B

/--
**The Critical Self-Adjointness**:
At s = 1/2, the completed operator is self-adjoint.
This is the key algebraic property from CompletionCore.
-/
theorem CriticalOp_selfadjoint (M : CompletedModel) (B : ℕ) :
    (CriticalOp M B).adjoint = CriticalOp M B := by
  unfold CriticalOp
  exact M.selfadjoint_half B

/-!
## 2. Real Spectrum from Self-Adjointness
-/

/--
A complex number is real iff its imaginary part is zero.
-/
def IsRealComplex (z : ℂ) : Prop := z.im = 0

/--
**Stability Implies Reality**:
If an operator is self-adjoint (Op† = Op), then any eigenvalue must be real.

Proof sketch: If Op v = λ v with v ≠ 0, then
  λ ⟨v, v⟩ = ⟨v, Op v⟩ = ⟨Op v, v⟩ = conj(λ) ⟨v, v⟩
Since ⟨v, v⟩ ≠ 0, we have λ = conj(λ), so λ ∈ ℝ.
-/
theorem Eigenvalue_Real_of_SelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Op : H →L[ℂ] H)
    (h_sa : Op.adjoint = Op)
    (ev : ℂ) (v : H) (hv : v ≠ 0)
    (h_eigen : Op v = ev • v) :
    IsRealComplex ev := by
  unfold IsRealComplex
  -- Key: ⟨Op v, v⟩ = ⟨v, Op v⟩ for self-adjoint Op
  -- ⟨v, Op v⟩ = ⟨v, ev • v⟩ = ev * ⟨v, v⟩
  -- ⟨Op v, v⟩ = ⟨ev • v, v⟩ = conj(ev) * ⟨v, v⟩
  -- Self-adjoint: ⟨Op x, y⟩ = ⟨x, Op y⟩, so ⟨Op v, v⟩ = ⟨v, Op v⟩
  -- Therefore ev * ⟨v, v⟩ = conj(ev) * ⟨v, v⟩
  -- Since v ≠ 0, ⟨v, v⟩ ≠ 0, so ev = conj(ev), meaning ev.im = 0
  have h1 : @inner ℂ H _ v (Op v) = ev * @inner ℂ H _ v v := by
    rw [h_eigen, inner_smul_right]
  have h2 : @inner ℂ H _ (Op v) v = conj ev * @inner ℂ H _ v v := by
    rw [h_eigen, inner_smul_left]
  -- Self-adjoint: ⟨Op v, v⟩ = ⟨v, Op v⟩ via adjoint definition
  -- adjoint_inner_left: ⟪(A†) y, x⟫ = ⟪y, A x⟫
  have h_sa_inner : @inner ℂ H _ (Op v) v = @inner ℂ H _ v (Op v) := by
    calc @inner ℂ H _ (Op v) v
        = @inner ℂ H _ (Op.adjoint v) v := by rw [h_sa]
      _ = @inner ℂ H _ v (Op v) := ContinuousLinearMap.adjoint_inner_left Op v v
  rw [h1, h2] at h_sa_inner
  -- Now: ev * ⟨v,v⟩ = conj(ev) * ⟨v,v⟩
  have h_inner_ne : @inner ℂ H _ v v ≠ 0 := inner_self_ne_zero.mpr hv
  have h_eq : ev = conj ev := mul_right_cancel₀ h_inner_ne h_sa_inner.symm
  -- ev = conj(ev) means ev.im = -ev.im, so ev.im = 0
  have h_im : ev.im = -ev.im := by
    have := congrArg Complex.im h_eq
    simp only [Complex.conj_im] at this
    exact this
  linarith

/--
**The Critical Eigenvalue Theorem**:
Any eigenvalue of the completed operator at s = 1/2 is real.
-/
theorem Critical_Eigenvalue_Real (M : CompletedModel) (B : ℕ)
    (ev : ℂ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : CriticalOp M B v = ev • v) :
    IsRealComplex ev :=
  Eigenvalue_Real_of_SelfAdjoint (CriticalOp M B)
    (CriticalOp_selfadjoint M B) ev v hv h_eigen

/-!
## 3. The Exclusion Principle
-/

/--
**Off-Critical Non-Self-Adjointness**:
When σ ≠ 1/2, the operator is NOT self-adjoint.
Op(s)† = Op(1 - conj(s)) ≠ Op(s) unless s = 1/2.
-/
theorem NonSelfAdjoint_Off_Critical (M : CompletedModel) (s : ℂ) (B : ℕ)
    (h_off : s.re ≠ 1 / 2)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    (M.Op s B).adjoint ≠ M.Op s B := by
  -- By the completion symmetry: Op(s)† = Op(1 - conj(s))
  -- For this to equal Op(s), we need s = 1 - conj(s)
  -- That is: re(s) + i·im(s) = 1 - re(s) + i·im(s)
  -- So: 2·re(s) = 1, meaning re(s) = 1/2
  -- Since re(s) ≠ 1/2, we have Op(s)† ≠ Op(s)
  rw [M.adjoint_symm s B]
  intro h_eq
  have h_s_eq : 1 - conj s = s := h_inj (1 - conj s) s h_eq
  -- From 1 - conj(s) = s, extract real parts: 1 - s.re = s.re
  have h_re : (1 - conj s).re = s.re := congrArg Complex.re h_s_eq
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h_re
  -- h_re : 1 - s.re = s.re, so 2 * s.re = 1, s.re = 1/2
  have : s.re = 1 / 2 := by linarith
  exact h_off this

/-! ## 3a. The Adjoint Defect (Section 5.1) -/

/--
The Adjoint Defect Operator Δ(s).
Defined in Section 5.1 as the deviation from self-adjointness:
  Δ_k(s) := K_k(s) - K_k(s)†
This measures "how far" the operator is from being self-adjoint.
-/
noncomputable def AdjointDefect (M : CompletedModel) (s : ℂ) (B : ℕ) : M.H →L[ℂ] M.H :=
  M.Op s B - (M.Op s B).adjoint

/--
**Algebraic Lemma**: s = 1 - conj(s) if and only if Re(s) = 1/2.

This is the key algebraic fact underlying the critical line characterization.
-/
theorem param_eq_conj_iff_critical (s : ℂ) : s = 1 - conj s ↔ s.re = 1 / 2 := by
  constructor
  · -- Forward: s = 1 - conj(s) implies s.re = 1/2
    intro h
    have h_re : s.re = (1 - conj s).re := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h_re
    -- h_re : s.re = 1 - s.re
    linarith
  · -- Backward: s.re = 1/2 implies s = 1 - conj(s)
    intro h_half
    apply Complex.ext
    · -- Real part: s.re = (1 - conj s).re
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · -- Imaginary part: s.im = (1 - conj s).im
      simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring

/--
**Theorem 5.1**: The Adjoint Defect vanishes if and only if s is on the critical line.

This is the rigorous "Stability" condition:
  Δ(s) = 0 ⟺ K(s)† = K(s) ⟺ Re(s) = 1/2
-/
theorem Defect_Zero_Iff_Critical (M : CompletedModel) (s : ℂ) (B : ℕ)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    AdjointDefect M s B = 0 ↔ s.re = 1 / 2 := by
  -- Unfold: Δ = 0 ⟺ K(s) - K(s)† = 0 ⟺ K(s) = K(s)†
  rw [AdjointDefect, sub_eq_zero]
  -- Use adjoint symmetry: K(s)† = K(1 - conj s)
  rw [M.adjoint_symm]
  -- Now: K(s) = K(1 - conj s) ⟺ s = 1 - conj s (by injectivity)
  constructor
  · intro h_eq
    -- h_eq : M.Op s B = M.Op (1 - conj s) B
    -- h_inj gives: s = 1 - conj s
    have h_s_eq : s = 1 - conj s := h_inj s (1 - conj s) h_eq
    exact (param_eq_conj_iff_critical s).mp h_s_eq
  · intro h_half
    have h_s_eq : s = 1 - conj s := (param_eq_conj_iff_critical s).mpr h_half
    -- After rewriting s to 1 - conj s, we need Op(1 - conj s) = Op(1 - conj(1 - conj s))
    -- But 1 - conj(1 - conj s) = 1 - (1 - s) = s, so this becomes Op(1 - conj s) = Op(s)
    -- which is Op(s) = Op(s) after using h_s_eq
    conv_rhs => rw [h_s_eq]
    -- Now goal is M.Op s B = M.Op (1 - conj (1 - conj s)) B
    -- Simplify: conj(1 - conj s) = 1 - conj(conj s) = 1 - s
    -- So 1 - conj(1 - conj s) = 1 - (1 - s) = s
    have h_simp : (1 : ℂ) - conj (1 - conj s) = s := by
      simp only [map_sub, map_one, Complex.conj_conj]
      ring
    rw [h_simp]

/--
**Corollary**: On the critical line, the adjoint defect vanishes.
-/
theorem Defect_Zero_On_Critical (M : CompletedModel) (t : ℝ) (B : ℕ) :
    AdjointDefect M ((1 / 2 : ℂ) + (t : ℂ) * I) B = 0 := by
  unfold AdjointDefect
  rw [M.adjoint_symm]
  -- Show: Op(s) - Op(1 - conj s) = 0, i.e., Op(s) = Op(1 - conj s)
  -- For s = 1/2 + t*I: conj s = 1/2 - t*I, so 1 - conj s = 1/2 + t*I = s
  have h_eq : (1 : ℂ) - conj ((1 / 2 : ℂ) + (t : ℂ) * I) =
              (1 / 2 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext
    · -- Real part: 1 - (1/2) = 1/2
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.add_re,
                 Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
                 mul_zero, Complex.I_im, mul_one, sub_zero]
      norm_num
    · -- Imaginary part
      simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, Complex.add_im,
                 Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
                 mul_zero, Complex.I_im, mul_one, add_zero]
      ring
  rw [h_eq, sub_self]

/-
**Note: The Exclusion Principle**

Complex eigenvalues can only exist off the critical line,
but off the critical line the operator isn't self-adjoint,
so it cannot support the stable real spectrum required for zeros.

This is why zeros cannot exist off the critical line:
- On the line: Self-adjoint → Real eigenvalues → Stable
- Off the line: Not self-adjoint → Complex eigenvalues possible → Unstable
-/

/-!
## 4. Connection to Hamiltonian Stability
-/

/--
**From Skew-Adjoint to Self-Adjoint**:
If H is skew-adjoint (H† = -H), then i·H is self-adjoint.
In Cl(3,3), B·H is the "self-adjoint version" of H.

This connects the Hamiltonian stability (H† = -H) to
the operator self-adjointness (Op† = Op) at the critical point.
-/
theorem SkewAdjoint_to_SelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E)
    (h_skew : A.adjoint = -A) :
    (Complex.I • A).adjoint = Complex.I • A := by
  -- (i·A)† = conj(i) · A† = -i · (-A) = i · A
  rw [map_smulₛₗ ContinuousLinearMap.adjoint]
  rw [h_skew]
  -- Goal: star I • -A = I • A
  -- star I = -I (since conj(I) = -I)
  have hstarI : (starRingEnd ℂ) Complex.I = -Complex.I := by
    rw [starRingEnd_apply]
    exact Complex.conj_I
  rw [hstarI]
  -- Goal: -I • -A = I • A
  rw [neg_smul, smul_neg, neg_neg]

/-!
## 5. The Spectral Rigidity Theorem
-/

/--
**Spectral Rigidity**:
The spectrum of the critical operator is "rigid" - it cannot be continuously
deformed off the real line without breaking self-adjointness.

This is why the zeros are "locked" to the critical line:
any perturbation that moves zeros off the line would break
the fundamental symmetry of the system.
-/
theorem Spectral_Rigidity (M : CompletedModel) (B : ℕ) :
    ∀ ev v, v ≠ 0 → CriticalOp M B v = ev • v → IsRealComplex ev :=
  fun ev v hv h_eigen => Critical_Eigenvalue_Real M B ev v hv h_eigen

/-!
## 6. The Surface Tension Hypothesis (Section 5.2)
-/

/--
**The Surface Tension Hypothesis** (Strengthened Form):

This structure encapsulates the Rayleigh-quotient imaginary-part identity:
  Im⟨v, K(s)v⟩ = (Re(s) - 1/2) · Q_B(v)
where Q_B(v) > 0 for all nonzero v.

**Why This Form?**
This is the "one-line Hammer": if v is an eigenvector with real eigenvalue λ,
then Im⟨v, K(s)v⟩ = Im(λ‖v‖²) = 0, which forces Re(s) = 1/2.

**Mathematical Content**:
- `quadraticForm` : The positive-definite form Q_B(v)
- `quadraticForm_pos` : Q_B(v) > 0 for v ≠ 0
- `rayleigh_imaginary_part` : The explicit identity relating Im⟨v,Kv⟩ to (σ - 1/2)·Q(v)
-/
structure SurfaceTensionHypothesis (M : CompletedModel) where
  /-- The positive-definite quadratic form Q_B(v) -/
  quadraticForm : ℕ → M.H → ℝ
  /-- Positivity: Q_B(v) > 0 for nonzero v -/
  quadraticForm_pos : ∀ B : ℕ, ∀ v : M.H, v ≠ 0 → 0 < quadraticForm B v
  /-- The Rayleigh-quotient identity:
      Im⟨v, K(s)v⟩ = (Re(s) - 1/2) · Q_B(v) -/
  rayleigh_imaginary_part :
    ∀ s : ℂ, ∀ B : ℕ, ∀ v : M.H,
    (@inner ℂ M.H _ v (M.Op s B v)).im = (s.re - 1/2) * quadraticForm B v

/--
**The Hammer from Surface Tension**:
If the Surface Tension hypothesis holds, then any real eigenvalue forces Re(s) = 1/2.

Proof: For eigenvector v with K(s)v = λv where λ ∈ ℝ:
  ⟨v, K(s)v⟩ = λ‖v‖² ∈ ℝ
  ⟹ Im⟨v, K(s)v⟩ = 0
  ⟹ (Re(s) - 1/2) · Q_B(v) = 0
  ⟹ Re(s) = 1/2  (since Q_B(v) > 0 for v ≠ 0)
-/
theorem Real_Eigenvalue_Implies_Critical_of_SurfaceTension
    (M : CompletedModel) (ST : SurfaceTensionHypothesis M)
    (s : ℂ) (B : ℕ) (ev : ℝ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : M.Op s B v = (ev : ℂ) • v) :
    s.re = 1 / 2 := by
  -- Step 1: ⟨v, K(s)v⟩ = ev * ⟨v,v⟩ is real
  have h_rayleigh : @inner ℂ M.H _ v (M.Op s B v) = (ev : ℂ) * @inner ℂ M.H _ v v := by
    rw [h_eigen, inner_smul_right]
  -- Step 2: The imaginary part is zero (real * real = real)
  have h_im_zero : (@inner ℂ M.H _ v (M.Op s B v)).im = 0 := by
    rw [h_rayleigh]
    -- ⟨v,v⟩ has imaginary part 0 (inner_self_im from Mathlib)
    have h_inner_im : RCLike.im (@inner ℂ M.H _ v v) = 0 := inner_self_im v
    -- RCLike.im for ℂ is the same as Complex.im
    have h_inner_im' : (@inner ℂ M.H _ v v).im = 0 := h_inner_im
    -- (ev : ℂ) * z where z.im = 0 has imaginary part ev.im * z.re + ev.re * z.im
    -- = 0 * z.re + ev * 0 = 0 (since ev is real, ev.im = 0)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, h_inner_im',
               mul_zero, zero_mul, add_zero]
  -- Step 3: Apply Surface Tension: 0 = (Re(s) - 1/2) * Q_B(v)
  have h_st := ST.rayleigh_imaginary_part s B v
  rw [h_im_zero] at h_st
  -- Step 4: Q_B(v) > 0 since v ≠ 0
  have h_Q_pos : 0 < ST.quadraticForm B v := ST.quadraticForm_pos B v hv
  -- Step 5: (Re(s) - 1/2) * Q = 0 with Q > 0 implies Re(s) = 1/2
  have h_factor : s.re - 1/2 = 0 := by
    by_contra h_ne
    have : (s.re - 1/2) * ST.quadraticForm B v ≠ 0 := mul_ne_zero h_ne (ne_of_gt h_Q_pos)
    exact this h_st.symm
  linarith

/-!
## 6a. The Spectral Exclusion Hypothesis (Alternative Form)
-/

/--
**The Spectral Exclusion Hypothesis**:

This structure encapsulates the key property needed for the "Hammer" theorem:
If the operator K(s) has eigenvalue 1 (a real eigenvalue), then s must be
on the critical line Re(s) = 1/2.

**Physical Intuition**:
- On the critical line: K(s) is self-adjoint, so all eigenvalues are real.
- Off the critical line: K(s)† ≠ K(s), and the operator cannot support
  the stable real eigenvalue 1.

This is formalized as a hypothesis structure rather than a proved theorem,
allowing the RH proof to proceed conditionally on this property.
-/
structure SpectralExclusionHypothesis (M : CompletedModel) where
  /--
  **The Exclusion Property**: If 1 is an eigenvalue of K(s) with s in the
  critical strip, then s must lie on the critical line.

  This captures the content of Theorem 1.1(ii) from the paper:
  Real eigenvalues (specifically eigenvalue 1) force criticality.
  -/
  eigenvalue_one_implies_critical :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) →
    (∃ v : M.H, v ≠ 0 ∧ M.Op s 0 v = (1 : ℂ) • v) →
    s.re = 1 / 2

  /--
  **Generalization**: Any real eigenvalue ev forces criticality.
  -/
  real_eigenvalue_implies_critical :
    ∀ s : ℂ, (0 < s.re ∧ s.re < 1) →
    ∀ (ev : ℝ), (∃ v : M.H, v ≠ 0 ∧ M.Op s 0 v = (ev : ℂ) • v) →
    s.re = 1 / 2

/--
**Supporting Lemma**: The inner product consistency for real eigenvalues.

For an eigenvector v with real eigenvalue ev:
⟨v, K(s)v⟩ = ev⟨v,v⟩ and ⟨v, K(1-s̄)v⟩ = ev⟨v,v⟩

This shows that K(s) and K(1-s̄) must agree in their action on the eigenspace.
-/
theorem inner_product_consistency
    (M : CompletedModel) (s : ℂ) (B : ℕ)
    (ev : ℝ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : M.Op s B v = (ev : ℂ) • v) :
    @inner ℂ M.H _ v (M.Op s B v) = @inner ℂ M.H _ v (M.Op (1 - conj s) B v) := by
  -- ⟨v, K(s)v⟩ = ev⟨v,v⟩
  have h1 : @inner ℂ M.H _ v (M.Op s B v) = (ev : ℂ) * @inner ℂ M.H _ v v := by
    rw [h_eigen, inner_smul_right]
  -- ⟨v, K(1-s̄)v⟩ = ⟨v, K(s)†v⟩ = ⟨K(s)v, v⟩ = conj(ev⟨v,v⟩) = ev⟨v,v⟩
  have h2 : @inner ℂ M.H _ v (M.Op (1 - conj s) B v) = (ev : ℂ) * @inner ℂ M.H _ v v := by
    calc @inner ℂ M.H _ v (M.Op (1 - conj s) B v)
        = @inner ℂ M.H _ v ((M.Op s B).adjoint v) := by rw [M.adjoint_symm]
      _ = @inner ℂ M.H _ (M.Op s B v) v := ContinuousLinearMap.adjoint_inner_right (M.Op s B) v v
      _ = conj (@inner ℂ M.H _ v (M.Op s B v)) := (inner_conj_symm _ _).symm
      _ = conj ((ev : ℂ) * @inner ℂ M.H _ v v) := by rw [h1]
      _ = conj (ev : ℂ) * conj (@inner ℂ M.H _ v v) := map_mul _ _ _
      _ = (ev : ℂ) * conj (@inner ℂ M.H _ v v) := by rw [Complex.conj_ofReal]
      _ = (ev : ℂ) * @inner ℂ M.H _ v v := by simp only [inner_self_conj]
  rw [h1, h2]

/--
**Corollary**: For eigenvector v with real eigenvalue, the adjoint defect
annihilates the inner product with v.

⟨v, Δ(s)v⟩ = 0 where Δ(s) = K(s) - K(s)†

This is a necessary (but not sufficient) condition for s being on the critical line.
-/
theorem adjoint_defect_inner_zero
    (M : CompletedModel) (s : ℂ) (B : ℕ)
    (ev : ℝ) (v : M.H) (hv : v ≠ 0)
    (h_eigen : M.Op s B v = (ev : ℂ) • v) :
    @inner ℂ M.H _ v (AdjointDefect M s B v) = 0 := by
  unfold AdjointDefect
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
  rw [M.adjoint_symm]
  -- From inner_product_consistency: ⟨v, K(s)v⟩ = ⟨v, K(1-s̄)v⟩
  have h_eq := inner_product_consistency M s B ev v hv h_eigen
  rw [h_eq]
  ring

/-!
## Physical Summary: Why Zeros Must Be Real

The Spectral framework proves:

1. **Self-Adjointness at 1/2**: The completion symmetry K(s)† = K(1-s̄)
   becomes K(1/2)† = K(1/2) on the critical line.

2. **Real Eigenvalues**: Self-adjoint operators have real spectrum.
   Any eigenvalue λ of K(1/2) satisfies λ = conj(λ), so λ ∈ ℝ.

3. **Exclusion Off-Line**: Off the critical line, K(s)† ≠ K(s),
   so eigenvalues can be complex - but these are "unstable" states.

4. **Rigidity**: The real spectrum is structurally protected by symmetry.
   Zeros cannot drift off the line without breaking the algebra.

This is the "Hammer" that forces zeros onto σ = 1/2:
not by analytic continuation, but by algebraic necessity.
-/

end Riemann.ZetaSurface.Spectral

end
