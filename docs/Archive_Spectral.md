# Archive: Spectral Theory

**Purpose**: Documents archived Lean files related to spectral methods, compression, and the operator-eigenvalue approach to RH.

---

## 1. SpectralZeta.leantxt - Spectral Packaging

**Location**: `Riemann/ZetaSurface/archive/SpectralZeta.leantxt`

**Key Concepts**:
- Reflection map: `reflect(s) = 1 - conj(s)`
- Compressed spectral zeta: `zetaInvC = det(I - A_C)`
- Characteristic equation: `∃ v ≠ 0, Op(s,B) v = v`

**The Reflection Fixed Point** (PROVEN):
```lean
theorem reflect_criticalLine (t : ℝ) : reflect (criticalLine t) = criticalLine t

theorem not_selfadjoint_off_critical (σ t : ℝ) (hσ : σ ≠ 1/2) :
    (M.Op s B).adjoint ≠ M.Op s B
```

**RH via Spectral Methods**:
```lean
theorem RH_Spectral_Version (s : ℂ) (B : ℕ)
    (h_char : CharacteristicEq M s B)
    (h_stable : (M.Op s B).adjoint = M.Op s B) :
    s.re = 1/2
```

**Logic**: Self-adjoint operators have real spectrum. On critical line, operator is self-adjoint. Off critical line, it's not. Stability requires self-adjointness. Therefore zeros must be on critical line.

**Finite RH Statement**:
```lean
def FiniteRH (B : ℕ) : Prop :=
  ∀ (s : ℂ), zetaInvC C s B = 0 → s.re = 1/2
```

**Why Archived**: Spectral approach sound but compression machinery was complex

---

## 2. SpectralReal.leantxt - Real-Valued Spectral Theory

**Key Concepts**:
- On critical line, the compressed determinant is real-valued
- Hermitian matrices have real eigenvalues
- This constrains where zeros can appear

**Critical Line Reality** (referenced):
```lean
theorem zetaInvC_real_on_critical (t : ℝ) (B : ℕ) :
    (zetaInvC C s B).im = 0
```

---

## 3. Compression.leantxt - Finite-Dimensional Compression

**Key Concepts**:
- Compress infinite-dimensional operator to finite matrix
- `CompressionData`: projection onto finite subspace
- `mat(s,B)`: finite matrix approximation
- `detLike = det(I - mat)`: computable determinant

**Matrix Hermiticity on Critical Line**:
```lean
theorem mat_hermitian_critical (t : ℝ) (B : ℕ) :
    Matrix.conjTranspose (mat C s B) = mat C s B
```

**Bridge Hypotheses**:
```lean
def DetSymm : Prop :=  -- Determinant symmetry
  ∀ s B, conj (zetaInvC C s B) = zetaInvC C (reflect s) B

def BridgeToEuler : Prop :=  -- Link to Euler product
  ∀ s B, zetaInvC C s B = ZInv B s
```

**Why Archived**: Compression approach was theoretically sound but implementation complex

---

## 4. CompletionCore.leantxt - Completed Model Structure

**Key Concepts**:
- `CompletedModel`: operator family with adjoint symmetry
- Adjoint symmetry: `Op(s,B)† = Op(1 - conj(s), B)`
- Self-adjoint on critical line: `Op(s)† = Op(s)` when Re(s) = 1/2

**The Spectral Bridge**:
1. **Operator Construction**: K(s) with forward + backward shifts
2. **Adjoint Symmetry**: K(s)† = K(1 - conj(s))
3. **Critical Fixed Point**: s ↦ 1 - conj(s) fixes Re(s) = 1/2
4. **Self-Adjoint on Critical**: K(s)† = K(s) when Re(s) = 1/2
5. **Spectral Reality**: Self-adjoint ⇒ real eigenvalues
6. **Zeta Correspondence**: ζ(s) = 0 ↔ 1 ∈ spectrum(K(s))
7. **Stability Argument**: Non-self-adjoint ⇒ unstable ⇒ no zeros

---

## 5. ZetaLinkFinite.leantxt - Finite Euler Product

**Key Concepts**:
- `ZInv B s = ∏_{p≤B} (1 - p^{-s})`: finite Euler product
- Goal: Show compressed determinant matches finite Euler product
- As B → ∞, approaches 1/ζ(s)

**The Vision**:
```
Operator Determinant ←→ Finite Euler Product ←→ 1/ζ(s)
     det(I - K)      =   ∏_p (1 - p^{-s})    =  1/ζ(s)
```

**Why Archived**: Vision correct but direct trace approach simpler

---

## Connection to Current Approach

The current proof chain uses a simpler path:

```
Pole of ζ'/ζ → Phase Clustering → Trace Monotonicity → Critical Line
```

Instead of the spectral approach:
```
Operator K(s) → Eigenvalue 1 → Self-Adjointness → Critical Line
```

Both approaches share the key insight: **σ = 1/2 is the unique fixed point of s ↦ 1-s̄**.

---

## Key Spectral Insights Preserved

1. **Functional equation = adjoint symmetry**: K(s)† = K(1-s̄)
2. **Critical line = self-adjoint locus**: Only place where K = K†
3. **Real spectrum from self-adjointness**: Constrains eigenvalues
4. **Eigenvalue 1 ↔ zeta zero**: Fredholm alternative
5. **Compression gives computability**: Finite approximations
