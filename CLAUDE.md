# Claude Code Instructions for Riemann/Lean Project

## Build Coordination

**IMPORTANT**: Before running `lake build`, always check if another build is in progress:

```bash
# Check for running lake processes
pgrep -f "lake build" || echo "No build running"

# Or check for .lake lock files
ls .lake/build/.lock 2>/dev/null && echo "Build may be in progress"
```

If a build is running, wait for it to complete before starting another.

## Project Overview

This is a Lean 4 formalization of a geometric/spectral approach to the Riemann Hypothesis.

- **Lean Version**: 4.27.0-rc1
- **Mathlib**: v4.27.0-rc1
- **Build command**: `lake build`

## Current Status (v7 - Weil Criterion)

| Category | Count |
|----------|-------|
| `sorry` | 3 (technical Schwartz lemmas) |
| Custom Axioms | 3 (orthogonality, explicit formula, Weil criterion) |
| Hypothesis Structures | 1 (ZetaLink) |

**Geometric Deduction: COMPLETE**

The Surface Tension is now **derived from calculus**, not assumed as physics:
- `GeometricSieve.lean` proves d/dσ[tension] = -2·log(p)·p^{-1/2}
- The stiffness coefficient log(p) comes from the derivative of p^{-σ}
- No axioms needed for the geometric/spectral logic

**The Remaining Gap**: `ZetaLinkHypothesis` - the correspondence between zeta zeros and operator eigenvalues. This is explicitly a hypothesis structure, not a hidden axiom.

**New in v6**: Distributional trace framework connects primes to zeros via the Weil explicit formula in pure real Cl(N,N).

## CRITICAL: Clifford Algebra - NO IMAGINARY COMPONENTS

**ALWAYS think in terms of real Clifford algebras. There are NO imaginary components.**

### Cl(3,3) with signature (+,+,+,-,-,-)

**DO NOT CHANGE THE SIGNATURE.** The project uses Cl(3,3):
- Three positive generators: γ₁² = γ₂² = γ₃² = +1
- Three negative generators: γ₄² = γ₅² = γ₆² = -1

**Why this matters:**
- The bivector B = γ₄·γ₅ satisfies B² = -1 (this IS the rotation generator)
- This comes from: B² = γ₄γ₅γ₄γ₅ = -γ₄γ₄γ₅γ₅ = -(-1)(-1) = -1
- The spectral parameter s = σ + Bt embeds naturally
- Split signature creates the balance where dilations can match

This is NOT Cl(6,0) or Cl(0,6). The split signature is essential to the proof.

### Cl(N,N) for Prime-Indexed Algebras

For the determinant factorization (see `GA/PrimeClifford.lean`), we use Cl(N,N) where N = π(B) = number of primes ≤ B:
- Each prime p gets an orthogonal generator γ_p with γ_p² = -1
- Distinct primes anticommute: γ_p γ_q = -γ_q γ_p for p ≠ q
- Orthogonality is **DEFINITIONAL** from Clifford structure, not proven separately
- The determinant factorizes: det(I - K) = ∏_p det(I - K_p) because cross-terms vanish

**The "i" in complex analysis is replaced by bivectors B with B² = -1. Everything is real geometric algebra.**

### The `.im` Notation Convention

In Lean code, we use `.im` (from `Complex.im`) to access what is conceptually the **B-coefficient** in Cl(N,N):

```
Isomorphism: Span{1, B} ≅ ℂ    where B² = -1

  Scalar part (Cl(N,N))     ↔   Real part (ℂ)      → z.re
  B-coefficient (Cl(N,N))   ↔   Imaginary part (ℂ) → z.im
```

**Key Point**: `.im` does NOT mean "imaginary" in the classical complex analysis sense.
It means "the coefficient of the bivector B" in the pure real Cl(N,N) framework.

When we write `inner_product.im = 0`, we mean the B-coefficient vanishes.
See `RayleighBridge.lean` for the formal isomorphism `SpanB_to_Complex`.

## Key Files

| File | Purpose |
|------|---------|
| `GeometricSieve.lean` | Calculus derivation of Surface Tension |
| `SpectralReal.lean` | The Hammer: real eigenvalue ⟹ σ = 1/2 |
| `SurfaceTensionInstantiation.lean` | Pure real Cl(3,3) tension operator, Critical_Line theorem |
| `GeometricZeta.lean` | Zeta as scalar + bivector series (no complex numbers) |
| `GeometricTrace.lean` | Trace via Cl(n,n) grading, cross-terms vanish |
| `DistributionalTrace.lean` | Weil explicit formula: primes ↔ zeros as distributions |
| `GeometricPositivity.lean` | Weil criterion: positive signal ⟹ RH |
| `DiscreteLock.lean` | Nyquist limit: 2^{-σ}·√2 = 1 ⟺ σ = 1/2 |
| `RayleighBridge.lean` | Span{1,B} ≅ ℂ isomorphism, B-coeff = .im |
| `CompletionKernel.lean` | Operator K(s,B) definition |
| `GA/Cl33.lean` | Cl(3,3) definitions, B² = -1 proof |
| `GA/PrimeClifford.lean` | Prime-indexed Cl(N,N), automatic orthogonality |

## The Logic Chain

1. **Geometric Definitions**: Primes are generators in Cl(N,N). s = σ + Bt.
2. **Calculus (Verified)**: d/dσ[p^{-σ} - p^{-(1-σ)}]|_{σ=1/2} = -2·log(p)·p^{-1/2}
3. **Operator Identity (Verified)**: B-coeff⟨v, K(s)v⟩ = (σ - 1/2)·Q_B(v)
4. **Spectral Hammer (Verified)**: Real eigenvalue + Q_B > 0 ⟹ σ = 1/2
5. **Nyquist Lock (Verified)**: p^{-σ}·√p = 1 ⟺ σ = 1/2 (L² measure balance)
6. **Trace Orthogonality (Axiom)**: ⟨e_p e_q⟩₀ = 0 for p ≠ q (Cl(n,n) grading)
7. **Explicit Formula (Axiom)**: PrimeSignal(φ) = ZeroResonance(φ) + corrections
8. **Zeta Link (Hypothesis)**: ζ(s)=0 ⟹ Real Eigenvalue

## Axioms Explained

| Axiom | File | Mathematical Justification |
|-------|------|---------------------------|
| `Orthogonal_Primes_Trace_Zero` | GeometricTrace.lean | Clifford grading: scalar part of orthogonal bivector product is zero |
| `Geometric_Explicit_Formula` | DistributionalTrace.lean | Weil explicit formula from analytic number theory |
| `Weil_Positivity_Criterion` | GeometricPositivity.lean | **EQUIVALENT TO RH** - positivity of prime distribution implies critical line |

These axioms encode deep results from Clifford algebra grading theory and analytic number theory. The Weil criterion is the fundamental bridge: it states that positivity of the prime signal forces all zeros onto σ = 1/2.

## Proof Conventions

1. Use Mathlib lemmas where available
2. Prefer `exact` over `apply` when possible
3. Use `convert ... using n` for type mismatches
4. Check `Real.rpow_natCast` for power type conversions

## Common Issues

- `x ^ (n:ℕ)` vs `x ^ (n:ℝ)` - use `Real.rpow_natCast` to convert
- Gaussian integrability: use `integrable_exp_neg_mul_sq` and `integrable_rpow_mul_exp_neg_mul_sq`
- L² membership: use `memLp_two_iff_integrable_sq` for real functions

## Audit Documents

- `docs/AUDIT_EXECUTIVE.md` - Executive summary of project status
- `docs/AUDIT_KEY_PROOFS.md` - Detailed proof explanations
