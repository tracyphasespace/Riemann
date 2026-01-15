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

## Current Status (v5 - Geometric Closure)

| Category | Count |
|----------|-------|
| `sorry` | 0 ✅ |
| Custom Axioms | 0 ✅ |
| Hypothesis Structures | 1 (ZetaLink) |

**Geometric Deduction: COMPLETE**

The Surface Tension is now **derived from calculus**, not assumed as physics:
- `GeometricSieve.lean` proves d/dσ[tension] = -2·log(p)·p^{-1/2}
- The stiffness coefficient log(p) comes from the derivative of p^{-σ}
- No axioms needed for the geometric/spectral logic

**The Remaining Gap**: `ZetaLinkHypothesis` - the correspondence between zeta zeros and operator eigenvalues. This is explicitly a hypothesis structure, not a hidden axiom.

## CRITICAL: Cl(3,3) Signature

**DO NOT CHANGE THE SIGNATURE.** The project uses Cl(3,3) with signature (+,+,+,-,-,-):
- Three positive generators: γ₁² = γ₂² = γ₃² = +1
- Three negative generators: γ₄² = γ₅² = γ₆² = -1

**Why this matters:**
- The bivector B = γ₄·γ₅ satisfies B² = -1 (acts like imaginary unit)
- This comes from: B² = γ₄γ₅γ₄γ₅ = -γ₄γ₄γ₅γ₅ = -(-1)(-1) = -1
- The spectral parameter s = σ + Bt embeds naturally
- Split signature creates the balance where dilations can match

This is NOT Cl(6,0) or Cl(0,6). The split signature is essential to the proof.

## Key Files

| File | Purpose |
|------|---------|
| `GeometricSieve.lean` | Calculus derivation of Surface Tension |
| `SpectralReal.lean` | The Hammer: real eigenvalue ⟹ σ = 1/2 |
| `SurfaceTensionInstantiation.lean` | Connects calculus to operator |
| `CompletionKernel.lean` | Operator K(s,B) definition |
| `GA/Cl33.lean` | Cl(3,3) definitions, B² = -1 proof |

## The Logic Chain

1. **Geometric Definitions**: Primes are generators in Cl(3,3). s = σ + Bt.
2. **Calculus (Verified)**: d/dσ[p^{-σ} - p^{-(1-σ)}]|_{σ=1/2} = -2·log(p)·p^{-1/2}
3. **Operator Identity (Verified)**: Im⟨v, K(s)v⟩ = (σ - 1/2)·Q_B(v)
4. **Spectral Hammer (Verified)**: Real eigenvalue + Q_B > 0 ⟹ σ = 1/2
5. **Zeta Link (Hypothesis)**: ζ(s)=0 ⟹ Real Eigenvalue

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
