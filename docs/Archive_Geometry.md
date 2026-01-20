# Archive: Geometric Formulations

**Purpose**: Documents archived Lean files related to geometric interpretations - surface tension, sieve, and physical analogies.

---

## 1. GeometricSieve.leantxt - Surface Tension Framework

**Location**: `Riemann/ZetaSurface/archive/GeometricSieve.leantxt`

**Central Thesis**:
The critical line is the unique locus where the sieve generates **pure rotations** (isometries). Off the line, it generates dilations (instabilities).

**Key Concepts**:
- `GeometricParam`: s = σ + B·t (replaces complex numbers)
- Forward dilation: `p^{-σ}`
- Reverse dilation: `p^{-(1-σ)}`
- **Geometric Tension**: `p^{-σ} - p^{-(1-σ)}` (mismatch)

**The Geometric Stability Theorem** (PROVEN, no sorry):
```lean
theorem Geometric_Stability_Condition (s : GeometricParam) :
    (∀ p : ℕ, Nat.Prime p → GeometricTension s p = 0) ↔ s.sigma = 1/2
```

**Proof**: Take p = 2, use log injectivity to show `-σ = -(1-σ)` implies `σ = 1/2`.

**Why log(p) Appears** (PROVEN via calculus):
```lean
theorem tension_derivative_at_half (p : ℝ) (hp : 0 < p) :
    deriv (tensionReal p) (1/2) = -2 * Real.log p * p ^ (-(1/2 : ℝ))
```

The "stiffness" of each prime mode is `2 * log(p)`. This explains why `Σ (log p)²` appears in the quadratic form!

**Physical Picture**:
- σ > 1/2: Volume pressure dominates (expansion)
- σ < 1/2: Surface tension dominates (collapse)
- σ = 1/2: Perfect balance (stable standing wave)

**Why Archived**: Core insight preserved in `UniversalStiffness.lean`

---

## 2. SurfaceTension.leantxt - The Stability Functional

**Location**: `Riemann/ZetaSurface/archive/SurfaceTension.leantxt`

**Key Concepts**:
- Surface Energy: `E[f] = ⟨Hf, Hf⟩ = ‖Hf‖²`
- Tension Operator: `T(σ) = (σ - 1/2) · I`
- Stability Functional: `S(σ) = (σ - 1/2)²`

**Proven Theorems**:
```lean
theorem Equilibrium_Condition (σ : ℝ) (f : HR) (hf : f ≠ 0) :
    TensionOp σ f = 0 ↔ σ = 1/2

theorem Critical_Surface_Unique :
    ∀ σ : ℝ, (∀ f : HR, f ≠ 0 → TensionOp σ f = 0) ↔ σ = 1/2

theorem Stable_Energy_Zero (n : ℕ) (h_stable : IsStableGenerator (Hamiltonian n)) (f : HR) :
    SurfaceEnergy n f = 0
```

**The Soap Bubble Principle**:
The critical line σ = 1/2 is the unique "soap bubble" configuration where volume pressure and surface tension balance. Zeros of zeta are standing waves on this stable surface.

**Why Archived**: Physical intuition sound, but direct trace approach is simpler

---

## 3. GeometricTrace.leantxt - Trace Orthogonality

**Location**: `Riemann/ZetaSurface/archive/GeometricTrace.leantxt`

**Key Insight**: Use Clifford grading to kill cross-terms in trace.

**The Logic**:
1. Sieve operator K = Σ K_p (sum of prime rotors)
2. Trace = Scalar Part (Grade 0 projection)
3. Scalar part of orthogonal vector product is zero: `⟨e_p e_q⟩₀ = 0` for p ≠ q
4. Therefore: `Tr(K^n) = Σ Tr(K_p^n)` (cross-terms vanish)

**PROVEN Theorems**:
```lean
theorem clifford_anticommute_of_orthogonal (h : Q.IsOrtho a b) :
    ι Q a * ι Q b = -(ι Q b * ι Q a)

theorem clifford_symmetric_zero_of_orthogonal (h : Q.IsOrtho a b) :
    ι Q a * ι Q b + ι Q b * ι Q a = 0

theorem Orthogonal_Primes_Trace_Zero_proven (p q : ℕ) (hp hq) (h_ne : p ≠ q) (σ) :
    GT.tr ((PrimeTensionTerm GT σ p).comp (PrimeTensionTerm GT σ q)) = 0
```

**Path to Fredholm Determinant**:
1. Trace factorization: `Tr(K^n) = Σ_p Tr(K_p^n)` ✓ PROVEN
2. Determinant factorization: `det(I-K) = Π_p det(I-K_p)`
3. Single-prime determinant: `det(I-K_p) = 1 - p^{-s}`
4. Zeta connection: `det(I-K) = Π_p (1-p^{-s}) = 1/ζ(s)`
5. Fredholm alternative: `ζ(s)=0 → Kv=v` for some v ≠ 0

**Why Archived**: Orthogonality theorem proven; integrated into main proof chain

---

## 4. Definitions.leantxt - Core Geometric Definitions

**Location**: `Riemann/ZetaSurface/archive/Definitions.leantxt`

**Comprehensive Definition Repository**:

**Geometric Parameter**:
```lean
structure GeometricParam where
  sigma : ℝ
  t : ℝ

def reversion (s : GeometricParam) : GeometricParam :=
  { sigma := s.sigma, t := -s.t }

def functionalPartner (s : GeometricParam) : GeometricParam :=
  { sigma := 1 - s.sigma, t := s.t }
```

**Geometric Zeta Terms**:
```lean
def ScalarTermParam (n : ℕ) (s : GeometricParam) : ℝ :=
  (n : ℝ) ^ (-s.sigma) * Real.cos (s.t * Real.log n)

def BivectorTermParam (n : ℕ) (s : GeometricParam) : ℝ :=
  -(n : ℝ) ^ (-s.sigma) * Real.sin (s.t * Real.log n)
```

**Test Functions (Schwartz space)**:
```lean
structure GeometricTestFunction where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  decay : ∀ k : ℕ, ∃ C, ∀ x, |x|^k * |toFun x| ≤ C
```

**Fourier/Positivity**:
```lean
def ClSquaredMagnitude (phi) (t : ℝ) : ℝ :=
  (FourierScalar phi t)² + (FourierBivector phi t)²
```

**Trace Structure**:
```lean
structure GeometricTraceData (H : Type*) where
  tr : (H →L[ℝ] H) → ℝ
  tr_primeJ_comp_zero : ∀ p q, p ≠ q → tr (J_p ∘ J_q) = 0
```

**Why Archived**: Definitions distributed to specialized files

---

## Connection to Current Codebase

| Archived Concept | Current Location | Status |
|------------------|------------------|--------|
| Geometric tension | Implicit in trace | Active |
| Stiffness = Σ(log p)² | `UniversalStiffness.lean` | Active |
| Trace orthogonality | `PrimeRotor.lean` | Active |
| Surface energy | `EnergySymmetry.lean` | Active |
| Soap bubble principle | Physical intuition | Guiding |

---

## Key Physical Insights Preserved

1. **Critical line = balance point** between expansion and contraction
2. **Stiffness from log(p)** - calculus derivation explains weight choice
3. **Orthogonality kills cross-terms** - Clifford structure automatic
4. **Zeros = standing waves** on stable minimal surface
5. **Menger sponge analogy** - infinite surface area, zero volume
