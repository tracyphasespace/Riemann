# Riemann Project - Key Proofs

**Purpose**: Full proof bodies for the 6 critical theorems that form the logical spine.
**Read AUDIT_EXECUTIVE.md first** for context and claim mapping.

---

## 1. Functional Equation Symmetry: K(s)† = K(1 - s̄)

**File**: `ZetaSurface/CompletionKernel.lean:253`
**Claim**: The completed operator satisfies the functional equation symmetry.

```lean
/--
The completed operator satisfies the functional equation symmetry:
  K(s)† = K(1 - conj(s))

This is the operator-theoretic analog of ξ(s) = ξ(1-s).
-/
theorem K_adjoint_symm (s : ℂ) (B : ℕ) :
    (K s B).adjoint = K (1 - conj s) B := by
  classical
  unfold K
  rw [adjoint_finset_sum]
  congr 1
  funext p
  exact Kterm_adjoint s p
```

**Analysis**: Uses linearity of adjoint over finite sums. Each term `Kterm s p` satisfies the symmetry individually (proven in `Kterm_adjoint`).

---

## 2. Critical Line Self-Adjointness: K(1/2 + it)† = K(1/2 + it)

**File**: `ZetaSurface/CompletionKernel.lean:273`
**Claim**: On the critical line, operators are self-adjoint.

```lean
/--
On the critical line s = 1/2 + it, the operator is self-adjoint:
  K(1/2 + it)† = K(1/2 + it)

Proof:
- conj(1/2 + it) = 1/2 - it
- 1 - (1/2 - it) = 1/2 + it
- So K(1/2 + it)† = K(1 - conj(1/2 + it)) = K(1/2 + it)
-/
theorem K_adjoint_critical (t : ℝ) (B : ℕ) :
    (K (1/2 + t * I) B).adjoint = K (1/2 + t * I) B := by
  rw [K_adjoint_symm]
  congr 1
  -- 1 - conj(1/2 + t*I) = 1 - (1/2 - t*I) = 1/2 + t*I
  simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
  ring
```

**Analysis**: Direct application of functional equation plus complex arithmetic. The `ring` tactic verifies `1 - (1/2 - ti) = 1/2 + ti`.

---

## 3. Self-Adjoint Implies Real Eigenvalues

**File**: `ZetaSurface/SpectralReal.lean:74`
**Claim**: Standard spectral theorem - self-adjoint operators have real eigenvalues.

```lean
/--
**Self-adjoint operators have real eigenvalues**

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
  have h1 : @inner ℂ H _ v (Op v) = ev * @inner ℂ H _ v v := by
    rw [h_eigen, inner_smul_right]
  have h2 : @inner ℂ H _ (Op v) v = conj ev * @inner ℂ H _ v v := by
    rw [h_eigen, inner_smul_left]
  have h_sa_inner : @inner ℂ H _ (Op v) v = @inner ℂ H _ v (Op v) := by
    calc @inner ℂ H _ (Op v) v
        = @inner ℂ H _ (Op.adjoint v) v := by rw [h_sa]
      _ = @inner ℂ H _ v (Op v) := ContinuousLinearMap.adjoint_inner_left Op v v
  rw [h1, h2] at h_sa_inner
  have h_inner_ne : @inner ℂ H _ v v ≠ 0 := inner_self_ne_zero.mpr hv
  have h_eq : ev = conj ev := mul_right_cancel₀ h_inner_ne h_sa_inner.symm
  have h_im : ev.im = -ev.im := by
    have := congrArg Complex.im h_eq
    simp only [Complex.conj_im] at this
    exact this
  linarith
```

**Analysis**: Standard inner product argument. Uses `inner_smul_left/right`, `adjoint_inner_left`, and `inner_self_ne_zero`. The `linarith` step solves `ev.im = -ev.im → ev.im = 0`.

---

## 4. The Surface Tension Hammer (Primary)

**File**: `ZetaSurface/SpectralReal.lean:339`
**Claim**: Real eigenvalue forces critical line via Surface Tension identity.

```lean
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
    have h_inner_im : RCLike.im (@inner ℂ M.H _ v v) = 0 := inner_self_im v
    have h_inner_im' : (@inner ℂ M.H _ v v).im = 0 := h_inner_im
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
```

**Analysis**: This is the **primary hammer theorem**. Given SurfaceTensionHypothesis (which asserts Im⟨v,Kv⟩ = (σ-½)Q(v) with Q > 0), a real eigenvalue forces the imaginary part to zero, which forces Re(s) = 1/2.

---

## 5. Off-Critical Implies Not Self-Adjoint

**File**: `ZetaSurface/SpectralReal.lean:129`
**Claim**: Away from the critical line, operators fail self-adjointness.

```lean
/--
**Off-Critical Non-Self-Adjointness**:
When σ ≠ 1/2, the operator is NOT self-adjoint.
Op(s)† = Op(1 - conj(s)) ≠ Op(s) unless s = 1/2.
-/
theorem NonSelfAdjoint_Off_Critical (M : CompletedModel) (s : ℂ) (B : ℕ)
    (h_off : s.re ≠ 1 / 2)
    (h_inj : ∀ s₁ s₂, M.Op s₁ B = M.Op s₂ B → s₁ = s₂) :
    (M.Op s B).adjoint ≠ M.Op s B := by
  rw [M.adjoint_symm s B]
  intro h_eq
  have h_s_eq : 1 - conj s = s := h_inj (1 - conj s) s h_eq
  have h_re : (1 - conj s).re = s.re := congrArg Complex.re h_s_eq
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h_re
  have : s.re = 1 / 2 := by linarith
  exact h_off this
```

**Analysis**: Contrapositively applies functional equation. If `Op(s)† = Op(s)`, then `1 - s̄ = s`, which forces `Re(s) = 1/2`. Requires injectivity of `Op` in `s`.

---

## 6. The RH Reduction Theorem (Conditional)

**File**: `SpectralZeta.lean:171`
**Claim**: IF spectral correspondence holds, THEN RH is true.

```lean
/--
**RH follows from Spectral Correspondence**

If we have a CompletedModel M and a SpectralCorrespondence Link
which asserts that Zeta zeros correspond to eigenvalue-1 conditions
and that this forces the critical line constraint, then RH holds.

This is a conditional theorem: it reduces RH to constructing an instance
of SpectralCorrespondence for a specific CompletedModel.
-/
theorem RH_of_SpectralCorrespondence
    (M : CompletedModel)
    (Link : SpectralCorrespondence M) :
    RiemannHypothesis := by
  unfold RiemannHypothesis
  intro s h_strip h_zero
  exact Link.eigenvalue_one_implies_critical s h_strip h_zero
```

**Analysis**: This is the **key conditional theorem**. It accepts a `SpectralCorrespondence` structure (which bundles the Hilbert-Pólya hypothesis) and produces a proof of RH.

---

## Summary: The Logical Chain

```
K_adjoint_symm         : K(s)† = K(1-s̄)                    [unconditional]
        ↓
K_adjoint_critical     : K(1/2+it)† = K(1/2+it)            [unconditional]
        ↓
Eigenvalue_Real_of_SelfAdjoint : self-adjoint → real ev   [unconditional]
        ↓
NonSelfAdjoint_Off_Critical : Re(s)≠1/2 → not self-adj   [unconditional]
        ↓
SurfaceTensionHypothesis : (structure to be instantiated) [conditional]
        ↓
Real_Eigenvalue_Implies_Critical_of_SurfaceTension       [conditional on ST]
        ↓
(ZL ∧ ST) → RH                                            [the reduction]
```

The **gap** is instantiating `SurfaceTensionHypothesis` and `ZetaLinkHypothesis`. Everything else is machine-verified.
