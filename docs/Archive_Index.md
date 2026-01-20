# Lean Archive Index

**Created**: 2026-01-18
**Purpose**: Master index for all archived Lean code and abandoned approaches.

---

## Archive Documents

| Document | Contents | Key Insights |
|----------|----------|--------------|
| [Archive_Clifford_Algebra.md](Archive_Clifford_Algebra.md) | Cl(3,3), Euler's formula, prime-indexed Clifford | B²=-1 is rotation; primes anticommute |
| [Archive_Operators.md](Archive_Operators.md) | Transfer, completion, Hamiltonian, Fredholm | K(s)†=K(1-s̄); unitarity at σ=1/2 |
| [Archive_Geometry.md](Archive_Geometry.md) | Surface tension, sieve, trace orthogonality | Stiffness from log(p); cross-terms vanish |
| [Archive_Spectral.md](Archive_Spectral.md) | Spectral zeta, compression, eigenvalues | Self-adjoint on critical line |
| [Archive_Failed_Approaches.md](Archive_Failed_Approaches.md) | Dead ends, refuted hypotheses, removed axioms | What NOT to repeat |

---

## Quick Reference: Concepts We've Already Tried

### Approaches That WORKED (now in active code)
- Horizontal pole approach: `Residues.lean`
- Orthogonal prime structure: `PrimeRotor.lean`
- Stiffness divergence: `UniversalStiffness.lean`
- Ergodic flow: `Ergodicity.lean`, `ErgodicSNR.lean`
- Taylor expansion via dslope: `AnalyticBasics.lean`

### Approaches That FAILED (don't repeat)
- Vertical approach to poles (Re[1/(iδ)] = 0)
- Phase derivatives marking zeros (refuted for 9 zeros)
- det(I-R) peaks at zeros (wrong frequency)
- zeros_isolated axiom (circular)
- Direct trace convexity (Lean elaboration issues)

### Approaches NEVER COMPLETED (could revisit)
- Weil explicit formula path
- Full Cl(∞) prime-indexed algebra
- Berry phase / spectral flow

---

## Archived File Locations

```
Riemann/ZetaSurface/archive/
├── Axioms.leantxt           # Original axiom set
├── Cl33.leantxt             # Core Cl(3,3) definitions
├── Cl33Ops.leantxt          # Clifford operations
├── CliffordEuler.leantxt    # Euler's formula (PROVEN)
├── CompletionKernel.leantxt # Kernel completion
├── CompletionMeasure.leantxt
├── Compression.leantxt
├── CompletionCore.leantxt
├── Definitions.leantxt      # All definitions
├── GeometricSieve.leantxt   # Surface tension (PROVEN)
├── GeometricTrace.leantxt   # Trace orthogonality (PROVEN)
├── GeometricZeta.leantxt
├── Hamiltonian.leantxt      # Lattice momentum
├── PrimeClifford.leantxt    # Prime-indexed Cl(N,N)
├── PrimeShifts.leantxt
├── RemovedAxioms.lean.txt   # Historical axioms
├── RotorFredholm.leantxt    # Rotor formulation
├── SpectralReal.leantxt
├── SpectralZeta.leantxt
├── SurfaceTension.leantxt
├── TraceConvexity.WrongPath.leantxt
├── Translations.leantxt
├── TransferOperator.leantxt
└── ZetaLinkFinite.leantxt
```

---

## Concepts That Keep Recurring

These ideas appear in multiple places - understanding them is key:

### 1. The Functional Equation Involution
```
s ↦ 1 - conj(s)    [complex form]
s ↦ 1 - s†         [Clifford form]
```
**Fixed point**: σ = 1/2 (the critical line)

### 2. Orthogonality of Primes
- In Clifford: γ_p γ_q = -γ_q γ_p
- In trace: Tr(K_p K_q) = 0 for p ≠ q
- Result: Euler product factorization

### 3. The Stiffness Sum
```
k = Σ (log p)²
```
- Appears as: spring constant, curvature, restoring force
- Diverges as more primes included
- Forces monotonicity via "rigid beam" theorem

### 4. Pole Behavior at Zeros
```
ζ'/ζ(s) ≈ 1/(s-ρ) + h(s)   near zero ρ
```
- Re[1/(s-ρ)] → +∞ on horizontal approach
- This dominates bounded finite sums
- Forces phase clustering

---

## Current Proof Architecture vs Archived Approaches

### Current (Active)
```
FTA → prime_logs_independent → Ergodicity → SNR → Stiffness → Monotonicity
         (AXIOM)                ↓
                           PairCorrelation
                                ↓
                        Phase Clustering ← Pole Domination
                                ↓
                          Trace Monotonic
                                ↓
                            σ = 1/2
```

### Archived (Spectral)
```
CompletedModel → Adjoint Symmetry → Self-Adjoint at σ=1/2
                        ↓
              Eigenvalue 1 ↔ ζ(s)=0
                        ↓
                Stability → σ = 1/2
```

### Archived (Weil)
```
Explicit Formula → Positivity → RH
    (never implemented)
```

---

## Lessons Learned

1. **Simpler is better**: Direct trace beats operator theory
2. **Horizontal, not vertical**: Approach poles from the side
3. **Numerical tests first**: Many ideas refuted by computation
4. **Avoid circular axioms**: zeros_isolated encoded RH
5. **Clifford gives orthogonality for free**: Use the algebra structure
6. **Functional equation is key**: Everything flows from s ↦ 1-s̄
