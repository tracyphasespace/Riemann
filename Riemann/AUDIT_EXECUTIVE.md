# Riemann Project - Executive Audit Summary

**Generated**: 2026-01-14
**Project**: Spectral/Geometric approach to the Riemann Hypothesis
**Language**: Lean 4.27.0-rc1 + Mathlib v4.27.0-rc1

---

## Build & Integrity Status

```
Files:        21 Lean files
Total Lines:  6,201
Build:        SUCCESS (lake build)
sorry:        0
axiom:        1 (rayleigh_identity_kernel - documented analytical bridge)
native_decide: 0
unsafe:       0
trivial:      0
```

**The single axiom** (`rayleigh_identity_kernel` in SurfaceTensionInstantiation.lean:100) is the analytical bridge requiring complex analysis proof. It states:
```
Im⟨v, K(s,B)v⟩ = (σ - 1/2) · Q_B(v)
```
All other files are axiom-free.

**Verification commands used:**
```bash
lake build                                    # SUCCESS
grep -rn "sorry$" --include="*.lean"          # 0 hits
grep -rn ":= sorry" --include="*.lean"        # 0 hits
grep -rn "^axiom " --include="*.lean"         # 1 hit (documented above)
grep -rn ": True :=" --include="*.lean"       # 0 hits
grep -rn "native_decide" --include="*.lean"   # 0 hits
grep -rn "\bunsafe\b" --include="*.lean"      # 0 hits
```

---

## Project Claim (What This Formalizes)

**Central Thesis**: The Riemann Hypothesis can be reduced to a spectral property of certain operators on L²(ℝ).

**The Primary Reduction: (ZL ∧ ST) → RH**

| Component | Structure | Role |
|-----------|-----------|------|
| **ZL** | `ZetaLinkHypothesis` | ζ(s) = 0 implies eigenvalue 1 exists |
| **ST** | `SurfaceTensionHypothesis` | Real eigenvalue forces Re(s) = 1/2 |
| **Combined** | ZL ∧ ST | ζ(s) = 0 → Re(s) = 1/2 **(RH)** |

---

## Notation Mapping

| Paper/Math | Lean Identifier | Notes |
|------------|-----------------|-------|
| ζ(s) | `riemannZeta s` | Mathlib's Riemann zeta function |
| K(s), S(s) | `M.Op s B` | Completed operator family |
| K(s)† | `(M.Op s B).adjoint` | Hilbert adjoint |
| Re(s) = 1/2 | `s.re = 1/2` | Critical line condition |
| ⟨v, w⟩ | `@inner ℂ H _ v w` | Complex inner product |

---

## Claim → Theorem Mapping (Key Results)

| Claim | Theorem | File:Line |
|-------|---------|-----------|
| K(s)† = K(1-s̄) | `K_adjoint_symm` | CompletionKernel.lean:253 |
| Critical line ⟹ self-adjoint | `K_adjoint_critical` | CompletionKernel.lean:273 |
| Self-adjoint ⟹ real eigenvalues | `Eigenvalue_Real_of_SelfAdjoint` | SpectralReal.lean:74 |
| Off-critical ⟹ not self-adjoint | `NonSelfAdjoint_Off_Critical` | SpectralReal.lean:129 |
| **Real ev ⟹ critical (Hammer)** | `Real_Eigenvalue_Implies_Critical_of_SurfaceTension` | SpectralReal.lean:339 |
| RH reduction (conditional) | `RH_of_SpectralCorrespondence` | SpectralZeta.lean:171 |
| det(1-A) real on critical line | `detLike_real_on_critical` | Compression.lean:283 |

---

## Architecture: Dependency Spine

```
Foundation Layer:
  GA/Cl33.lean ─────────────────┐
  GA/Cl33Ops.lean ──────────────┤
                                ▼
Operator Layer:
  ZetaSurface/Translations.lean ─────┐
  ZetaSurface/PrimeShifts.lean ──────┤
  ZetaSurface/Hamiltonian.lean ──────┤
                                     ▼
Completion Layer:
  ZetaSurface/CompletionCore.lean ───────────┐
  ZetaSurface/CompletionKernel.lean ─────────┤
  ZetaSurface/CompletionKernelModel.lean ────┤
  ZetaSurface/CompletionMeasure.lean ────────┤
  ZetaSurface/CompletionMeasureModel.lean ───┤
                                             ▼
Spectral Layer:
  ZetaSurface/SpectralReal.lean ─────────────┐
  ZetaSurface/SpectralZeta.lean ─────────────┤
  ZetaSurface/TransferOperator.lean ─────────┤
                                             ▼
Application Layer:
  ZetaSurface/Compression.lean ──────────────┐
  ZetaSurface/CompressionRicker.lean ────────┤
  ZetaSurface/ZetaLinkFinite.lean ───────────┤
  ZetaSurface/SurfaceTension.lean ───────────┤
  ZetaSurface/SurfaceTensionInstantiation.lean ─┤ (1 axiom)
  ZetaSurface/SurfaceTensionMeasure.lean ────┤
  SpectralZeta.lean (RH theorem) ────────────┘
```

---

## Critical Structures (Conditional Axiom Bundles)

These structures bundle hypotheses. Theorems using them are **conditionally proven**.

| Structure | Purpose | Status |
|-----------|---------|--------|
| `CompletedModel` | Interface for L² + operator family | **Instantiated** (KernelModel) |
| `SurfaceTensionHypothesis` | Im⟨v,Kv⟩ = (σ-½)Q(v), Q > 0 | **Instantiated** (via 1 axiom) |
| `ZetaLinkHypothesis` | ζ(s)=0 → eigenvalue 1 exists | Conditional (not instantiated) |
| `SpectralExclusionHypothesis` | Real eigenvalue → critical line | Conditional (alternate) |
| `SpectralCorrespondence` | Full zeta-eigenvalue link | Conditional |
| `TraceLogDetLink` | Trace series ↔ log-det identity | Conditional |

**Key Point**: The project proves **"IF (ZL ∧ ST) THEN RH"**.
The structures document exactly what remains to be proven.

---

## The Two-Interface Architecture

### Interface 1: Zeta Link (ZL)
Connects zeta zeros to spectral conditions:
- ζ(s) = 0 in critical strip → eigenvalue 1 of K(s)

### Interface 2: Surface Tension (ST)
Provides geometric rigidity:
- Im⟨v, K(s)v⟩ = (Re(s) - 1/2) · Q_B(v)
- Q_B(v) > 0 for v ≠ 0
- Real eigenvalue → Im⟨v, K(s)v⟩ = 0 → Re(s) = 1/2

### The Hammer Theorem
```
Real_Eigenvalue_Implies_Critical_of_SurfaceTension:
  (ST : SurfaceTensionHypothesis) →
  (ev : ℝ) → (K(s)v = ev·v) → (v ≠ 0) →
  Re(s) = 1/2
```

---

## How to Review This Project

### For LLMs / Automated Review:

1. **Read this file first** (AUDIT_EXECUTIVE.md)
2. **Read AUDIT_SIGNATURES.md** - all theorem/def signatures, no proof bodies
3. **Read AUDIT_KEY_PROOFS.md** - the 6 critical proofs in full
4. For deep dives, read individual files from the dependency spine (bottom to top)

### For Human Skeptics:

1. Verify build: `cd Riemann/Lean && lake build`
2. Run all integrity checks from "Verification commands" above
3. Review the conditional structures - these are the "axiom bundles"
4. Trace `Real_Eigenvalue_Implies_Critical_of_SurfaceTension` as the primary hammer

### Red Flags to Check:

- [ ] Any `sorry` in proof bodies (should be 0)
- [ ] Any `axiom` declarations (should be 0)
- [ ] Any `: True :=` trivial placeholders (should be 0)
- [ ] Any `native_decide` or `unsafe` (should be 0)
- [ ] Structures with no instances that are used as if proven

---

## Summary

**What is proven unconditionally:**
- Functional equation symmetry K(s)† = K(1-s̄)
- Self-adjointness on critical line
- Real eigenvalues for self-adjoint operators
- Non-self-adjointness off critical line
- KernelModel instantiates CompletedModel
- Q_B positivity for KernelModel (KernelQuadraticForm_pos)

**What is proven with 1 axiom:**
- SurfaceTensionHypothesis instantiated for KernelModel
- The Hammer: real eigenvalue → Re(s) = 1/2
- RH_for_KernelModel (given ZetaLink)

**What remains (future work):**
- Bridge `rayleigh_identity_kernel` axiom (Cl(3,3) → Hilbert space, NOT complex analysis)
  - GeometricSieve.lean already proves the math using real Cl(3,3) algebra
  - Remaining work: connect to Hilbert space inner product
- Instantiate ZetaLinkHypothesis (connect zeta zeros to eigenvalue 1)
