# Archive: Clifford Algebra Foundations

**Purpose**: Documents archived Lean files related to Clifford algebra constructions.

---

## 1. Cl33.leantxt - The Core Cl(3,3) Algebra

**Location**: `Riemann/ZetaSurface/archive/Cl33.leantxt`

**Key Concepts**:
- Split-signature Clifford algebra Cl(3,3) with signature (+++)---)
- Internal bivector `B_internal = γ₄·γ₅` satisfying `B² = -1`
- `Cl33Complex`: Embedding of complex numbers via `a + b·B`
- Reversal operation (Clifford conjugation): `reverse(B) = -B`

**Key Definitions**:
```lean
def B_internal : Cl33  -- The bivector with B² = -1
def Cl33Complex (a b : ℝ) : Cl33 := algebraMap ℝ Cl33 a + b • B_internal
theorem B_internal_sq : B_internal * B_internal = -1
theorem reverse_B_internal : reverse B_internal = -B_internal
```

**Why Archived**: Core definitions moved to active `Riemann/GA/Cl33.lean`

---

## 2. Cl33Ops.leantxt - Clifford Operations

**Location**: `Riemann/ZetaSurface/archive/Cl33Ops.leantxt`

**Key Concepts**:
- Spectral parameter `s = σ + B·t` (geometric replacement for complex)
- Exponential map `exp_B θ = cos θ + B·sin θ`
- Critical line definition: `σ = 1/2`
- Functional equation partner: `s ↦ 1 - s†`

**Key Definitions**:
```lean
structure SpectralParam where
  sigma : ℝ  -- Dilation (real part)
  t : ℝ      -- Rotation (imaginary part)

def exp_B (θ : ℝ) : Cl33 := Cl33Complex (Real.cos θ) (Real.sin θ)
def criticalLine (t : ℝ) : SpectralParam := ⟨1/2, t⟩
```

**Why Archived**: Moved to active `Riemann/GA/Cl33Ops.lean`

---

## 3. CliffordEuler.leantxt - Euler's Formula in Cl(3,3)

**Location**: `Riemann/ZetaSurface/archive/CliffordEuler.leantxt`

**Key Concepts**:
- **PROVEN**: `exp(B·θ) = cos θ + B·sin θ` from Taylor series
- Power cycle: `B⁰=1, B¹=B, B²=-1, B³=-B, B⁴=1, ...`
- `B^{2k} = (-1)^k` and `B^{2k+1} = (-1)^k · B`
- Rotor unitarity: `R(θ)·R(-θ) = 1`

**Proven Theorems** (no axioms needed):
```lean
theorem B_pow_even (k : ℕ) : B_internal ^ (2 * k) = (-1 : Cl33) ^ k
theorem B_pow_odd (k : ℕ) : B_internal ^ (2 * k + 1) = (-1 : Cl33) ^ k * B_internal
theorem CliffordExp_add (θ φ : ℝ) : CliffordExp (θ + φ) = CliffordExp θ * CliffordExp φ
theorem CliffordExp_norm_sq (θ : ℝ) : reverse (CliffordExp θ) * CliffordExp θ = 1
```

**Key Insight**: The Taylor series derivation uses ONLY `B² = -1`. No analysis axioms needed beyond convergence. This is pure algebra.

**Application to Dirichlet Terms**:
```
n^{-s} = n^{-σ} · exp(-B·t·log n)
       = n^{-σ} · (cos(t·log n) - B·sin(t·log n))
```

**Why Archived**: Mathematical content complete; superseded by simpler direct definitions

---

## 4. PrimeClifford.leantxt - Prime-Indexed Clifford Algebra

**Location**: `Riemann/ZetaSurface/archive/PrimeClifford.leantxt`

**Key Concepts**:
- Each prime p gets its own orthogonal direction `γ_p` in Cl(0, π(B))
- `γ_p² = -1` for each prime (timelike signature)
- `γ_p γ_q = -γ_q γ_p` for distinct primes (anticommutation)
- Orthogonality is DEFINITIONAL from Clifford structure

**Key Theorems** (PROVEN):
```lean
theorem prime_generator_sq : (ιPrime B (basisPrime p))² = algebraMap ℝ (ClPrime B) (-1)
theorem prime_generators_anticommute (h_ne : p ≠ q) :
    γ_p * γ_q + γ_q * γ_p = 0
```

**Determinant Factorization** (the Euler product structure):
```
det(I - K) = det(I - Σ_p K_p) = ∏_p det(I - K_p)
```
Cross-terms vanish by anticommutation!

**Connection to Current Work**:
- This is the foundation for `PrimeRotor.lean` (orthogonal prime axes)
- The stiffness sum `Σ (log p)²` comes from this orthogonal structure
- `UniversalStiffness.lean` builds on these ideas

**Why Archived**: Evolved into simpler `PrimeRotor.lean` approach

---

## 5. Axioms.leantxt - Original Axiom Set

**Location**: `Riemann/ZetaSurface/archive/Axioms.leantxt`

**Historical Axioms** (most now removed or proven):
1. `zero_implies_kernel` - Zeta zero implies kernel vector exists
2. `Orthogonal_Primes_Trace_Zero` - **PROVEN** in GeometricTrace.lean
3. Various functional equation axioms

**Current Status**: Only 2 axioms remain in `ProofEngine/Axioms.lean`:
- `ax_analytic_stiffness_pos`
- `ax_finite_sum_approx_analytic`

---

## Connections to Current Codebase

| Archived Concept | Current Location | Status |
|------------------|------------------|--------|
| Cl(3,3) bivector B | `Riemann/GA/Cl33.lean` | Active |
| SpectralParam | `Riemann/GA/Cl33Ops.lean` | Active |
| Prime orthogonality | `GlobalBound/PrimeRotor.lean` | Active |
| Stiffness constant | `ZetaSurface/UniversalStiffness.lean` | Active |
| Euler's formula | Implicitly used | Proven |

---

## Key Insight: Why Clifford Algebra?

The Clifford framework provides:
1. **Automatic orthogonality** - Primes anticommute, killing cross-terms
2. **Geometric meaning** - `B² = -1` is rotation, not abstract "imaginary"
3. **Determinant factorization** - Euler product from algebra structure
4. **Real formulation** - Everything is geometrically real (no complex numbers needed)

The critical line `σ = 1/2` emerges as the unique fixed point of the functional equation involution `s ↦ 1 - s†`.
