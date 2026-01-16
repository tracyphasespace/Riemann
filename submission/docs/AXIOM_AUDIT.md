# Axiom Audit

Copyright (c) 2026 Tracy McSheery PhaseSpace

This document provides mathematical justification for the single axiom used in the formalization.

## The Axiom

**Location**: `Riemann/ZetaSurface/Axioms.lean:125`

```lean
axiom zero_implies_kernel (Geom : BivectorStructure H) (sigma t : ℝ) (B : ℕ) (hB : 2 ≤ B)
    (h_zero : IsGeometricZero sigma t) :
    ∃ (v : H), v ≠ 0 ∧ KwTension Geom sigma B v = 0 • v
```

## English Statement

If ζ(s) = 0 (where s = σ + it), then the geometric tension operator K(s) has a non-trivial kernel.

## Mathematical Content

This axiom encodes the **Fredholm determinant interpretation** of the zeta function:

```
ζ(s) = det(I - K(s))⁻¹
```

where K(s) is a trace-class operator. The key property of Fredholm determinants:

```
det(I - K) = 0  ⟺  1 ∈ Spectrum(K)  ⟺  ∃ v ≠ 0, Kv = v
```

## Why This Cannot Be Proven in Current Mathlib

Proving this axiom would require:

1. **Formal Fredholm Theory**: Defining det(I - K) for trace-class operators (partial Mathlib support)
2. **Zeta = Determinant**: Proving ζ(s) = det(I - K(s)) via Euler product
3. **Spectral Theory**: det = 0 ⟹ not invertible ⟹ kernel exists

The gap is primarily step 2: connecting the analytic continuation of ζ(s) to the operator determinant. Zeros in the critical strip emerge from **analytic continuation**, not from any single Euler factor vanishing.

## The Prime-Zero Duality

The operator K(s) is diagonal in the prime basis {e_p}:

```
K(s) = Σ_p K_p(s)  (orthogonal sum over primes)
```

But zeros correspond to the **frequency basis** (eigenvectors of the Laplacian):

```
Prime Basis {e_p}  ←──Fourier──→  Zero Basis {ρ_k}
```

This duality is the **Explicit Formula** of analytic number theory. The axiom encapsulates this deep relationship.

## What The Axiom Does NOT Assume

- Does NOT assume RH
- Does NOT assume anything about the location of zeros
- Only asserts that zeros correspond to kernel vectors

## Potential Path to Elimination

See `Riemann/ZetaSurface/FredholmTheory.lean` for a stub outlining the formalization path:

1. Define finite Fredholm determinants
2. Prove the Euler product connection
3. Take limits and apply spectral theory

This would require significant Mathlib development in trace-class operators and Fredholm theory.

## References

- Simon, B. "Trace Ideals and Their Applications" (2005)
- Connes, A. "Trace formula in noncommutative geometry" (1999)
- Berry & Keating, "The Riemann zeros and eigenvalue asymptotics" (1999)
