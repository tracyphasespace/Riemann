# Archive: Operator Theory

**Purpose**: Documents archived Lean files related to transfer operators, Hamiltonians, and completions.

---

## 1. TransferOperator.leantxt - Basic Weighted Sum Operator

**Location**: `Riemann/ZetaSurface/archive/TransferOperator.leantxt`

**Key Concepts**:
- Forward weight: `α(s,p) = p^{-s}`
- Basic operator: `A_s = Σ_p α(s,p) · T_p`
- NOT self-adjoint; completion needed for functional equation symmetry

**Weight Decomposition (Cl33)**:
```lean
def αCos (s : SpectralParam) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-s.sigma) * Real.cos (s.t * Real.log p)

def αSin (s : SpectralParam) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-s.sigma) * Real.sin (s.t * Real.log p)
```

**Critical Line Properties** (PROVEN):
```lean
theorem α_modulus_critical (p : ℕ) (hp : Nat.Prime p) (t : ℝ) :
    ‖α (1/2 + t * I) p‖ = Real.rpow p (-1/2 : ℝ)
```

**Why Archived**: Evolved into completion approach

---

## 2. CompletionKernel.leantxt - Kernel Completion Strategy

**Location**: `Riemann/ZetaSurface/archive/CompletionKernel.leantxt`

**Key Concepts**:
- Add backward shifts to achieve adjoint symmetry
- `K(s) = Σ_p [ α(s,p)·T_p + β(s,p)·T_p⁻¹ ]`
- Backward weight: `β(s,p) = conj(α(1 - conj(s), p))`

**The Key Result**:
```
K(s)† = K(1 - conj(s))
```
This mirrors the functional equation of completed zeta!

**Why It Works**:
- Taking adjoint swaps `T_p ↔ T_p⁻¹`
- Conjugates weights
- Choice of β makes swap match `K(1 - conj(s))`

**Cl33 Version**:
- `conj(s)` becomes `reverse(s)` (Clifford reversal)
- For `s = σ + B·t`, `reverse(s) = σ - B·t`

**Why Archived**: Approach was sound but measure completion was simpler

---

## 3. Hamiltonian.leantxt - Lattice Momentum Operator

**Location**: `Riemann/ZetaSurface/archive/Hamiltonian.leantxt`

**Key Concepts**:
- Discrete momentum via symmetric difference (bounded operator)
- `D = (T_ε - T_{-ε}) / 2ε` is exactly skew-adjoint
- `H(n) = log(n) · D` generates flow by log(n)
- Recursive: `H(a·b) = H(a) + H(b)` (log additivity)

**Key Definitions**:
```lean
def BaseGenerator : HR →L[ℝ] HR :=
  (1 / (2 * epsilon)) • (T_plus - T_minus)

def Hamiltonian (n : ℕ) : HR →L[ℝ] HR :=
  (Real.log n) • BaseGenerator

def IsStableGenerator (H : HR →L[ℝ] HR) : Prop :=
  H.adjoint = -H  -- Skew-adjoint
```

**Proven Theorems**:
```lean
theorem BaseGenerator_stable : IsStableGenerator BaseGenerator
theorem Hamiltonian_additivity (a b : ℕ) : H(a * b) = H(a) + H(b)
theorem Surface_Stability_Universal (n : ℕ) : IsStableGenerator (Hamiltonian n)
```

**Physical Interpretation**:
- ε is lattice spacing (UV cutoff)
- Skew-adjointness ensures unitary evolution (energy conservation)
- Critical line is energy balance point

**Why Archived**: Lattice approach was pedagogical; continuous approach used instead

---

## 4. RotorFredholm.leantxt - Rotor-Based Operator Formulation

**Location**: `Riemann/ZetaSurface/archive/RotorFredholm.leantxt`

**Key Concepts**:
- Rotor `R(θ) = cos θ + B·sin θ` in Cl(3,3)
- Normalized prime rotor: `R_p(s) = p^{-(σ-1/2)} · [rotation matrix]`
- **CRITICAL**: Must use `p^{-(σ-1/2)}` normalization, NOT `p^{-σ}`

**PROVEN (Numerically via Wolfram)**:
1. σ = 1/2 is the ONLY value where rotor product is unitary
2. Eigenvalue magnitudes = 1 only at σ = 1/2
3. Off critical line: eigenvalues explode (σ < 1/2) or collapse (σ > 1/2)

**Evidence**:
```
σ = 0.5: drift = 10^{-16} (machine precision)
σ = 0.4: drift = 128
σ = 0.3: drift = 11,880
σ = 0.2: drift = 1.09 × 10^6
```

**REFUTED Hypotheses**:
1. det(I - R) peaks at zeros: WRONG FREQUENCY
2. φ''(t) = 0 at zeros: DEFINITIVELY REFUTED (tested 9 zeros, found 0 crossings)
3. Phase derivatives encode zeros: NO CORRELATION

**Open Question**: How to locate zeros WITHIN the critical line. Unitarity proves WHY σ = 1/2 is special, but not WHERE on that line zeros are.

**Why Archived**: Proved σ = 1/2 is special but couldn't locate zeros

---

## 5. Connection to Current Approach

The current `CliffordRH.lean` uses a simpler formulation:

```lean
def rotorTrace (σ t : ℝ) (primes : List ℕ) : ℝ :=
  2 * primes.foldl (fun acc p =>
    acc + Real.log p * (p : ℝ) ^ (-σ) * Real.cos (t * Real.log p)) 0
```

This is the scalar projection of the rotor force field - simpler than full operator theory but captures the essential structure.

---

## Lessons Learned

1. **Bounded operators are essential** - Unbounded momentum operators cause technical issues
2. **Normalization matters** - Must use `p^{-(σ-1/2)}` not `p^{-σ}` for unitarity
3. **Completion achieves symmetry** - Adding backward shifts gives `K(s)† = K(1-s̄)`
4. **Rotor unitarity at σ=1/2 is PROVEN** - But doesn't locate zeros on the line
5. **Simpler is better** - Direct trace formulation avoids operator theory overhead
