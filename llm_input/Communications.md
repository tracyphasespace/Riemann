# AI2 Direct Work Instructions

**Last Updated**: 2026-01-22
**Build Status**: PASSING
**Sorry Count**: 15 total

---

## WORK MODE: DIRECT (NO AGENTS)

**AI2**: Work on sorries directly. Do NOT spawn agents - they cause lockups.

### Workflow:
1. Pick ONE sorry from the priority list below
2. Read the file to understand context
3. Search Mathlib for relevant lemmas (Grep/Glob)
4. Edit the file with your proof attempt
5. If blocked, document the blocker and move to next sorry
6. **DO NOT run `lake build`** - AI1 handles builds

### After each attempt:
- Update this file with your result
- Move to the next sorry
- Commit progress periodically

---

## Current Sorries (15 total)

### HIGH PRIORITY - Ready to attempt

#### 1. CalculusAxioms:21 - taylor_second_order
**File**: `Riemann/ProofEngine/CalculusAxioms.lean`
**Status**: Structure done, needs conversion
```
Proof structure is in place using taylor_mean_remainder_lagrange_iteratedDeriv.
Remaining: convert taylorWithinEval to explicit form (f x₀ + deriv f x₀ * (x - x₀))
Key: iteratedDeriv 2 f = deriv (deriv f) via iteratedDeriv_succ
```

#### 2. EnergySymmetry:263 - symmetry_and_convexity_imply_local_min
**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
**Status**: Second derivative test
```
Given: E'(1/2) = 0 (proven), E''(1/2) > 0 (hypothesis)
Use: strictMonoOn_of_deriv_pos to show E' strictly increasing
Then: E'(σ) < 0 for σ < 1/2, E'(σ) > 0 for σ > 1/2
Conclude: E(σ) > E(1/2) for σ ≠ 1/2
```

#### 3. CalculusAxioms:55 - effective_convex_implies_min_proven
**File**: `Riemann/ProofEngine/CalculusAxioms.lean`
**Status**: Uses taylor_second_order
```
Once taylor_second_order is proven, this follows by:
- Taylor expansion at 1/2
- Second order term dominates first order (given ε < δ|σ-1/2|/2)
```

### MEDIUM PRIORITY - Need axioms or helpers

#### 4-5. EnergySymmetry:101,109 - riemannXi_zero_iff_zeta_zero
**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
**Status**: NEEDS AXIOM
```
BLOCKER: Mathlib lacks completedRiemannZeta₀ decomposition.

Needed axiom (add to Axioms.lean if not in Mathlib):
  axiom completedRiemannZeta₀_eq (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta₀ s = completedRiemannZeta s + s⁻¹ + (1 - s)⁻¹

With this axiom, both directions follow algebraically:
- Forward: Xi=0 → s(1-s)Λ₀=1 → s(1-s)Λ=0 → Λ=0 → ζ=0
- Backward: ζ=0 → Λ=0 → Λ₀=1/(s(1-s)) → Xi=0
```

#### 6-7. ClusterBound:83,102
**File**: `Riemann/ProofEngine/ClusterBound.lean`
**Status**: NEEDS HELPER
```
Need c2_stability_transfer helper lemma first.
If |f-g| < ε and g has strict min with g'' > 2ε, then f has strict min too.
```

### LOWER PRIORITY

#### 8-10. TraceAtFirstZero:77,143,153
**File**: `Riemann/ProofEngine/TraceAtFirstZero.lean`
```
Line 77: Interval arithmetic mem_mul - needs 16-way sign case splits
Line 143: first_zero_trace_pos - numerical bound
Line 153: trace_derivative_pos - positivity
```

#### 11. EnergySymmetry:305 - convexity_implies_norm_strict_min
```
C2 approximation transfer - depends on ClusterBound helpers
```

#### 12-15. Other files
- AnalyticAxioms:320 - Explicit Formula (hard, skip for now)
- AristotleContributions:101
- Convexity:104 (not critical path)
- NumericalAxioms:23,32

---

## Rosetta Stone Technique Summary

**What works:** Pure calculus/analysis proofs
- Use abstract Mathlib lemmas like `strictMonoOn_of_deriv_pos`, `tendsto_inv_nhdsGT_zero`
- Decompose: normSq = re² + im², then use `Differentiable.pow`

**What needs axioms:** Zeta-specific facts
- `completedRiemannZeta₀` decomposition not in Mathlib
- Add as axiom with clear mathematical justification

---

## Techniques Reference

```lean
-- Taylor (Mathlib)
taylor_mean_remainder_lagrange_iteratedDeriv
iteratedDeriv_succ : iteratedDeriv (n+1) f = deriv (iteratedDeriv n f)

-- Monotonicity from derivative
strictMonoOn_of_deriv_pos : Convex D → ContinuousOn f D →
  (∀ x ∈ interior D, 0 < deriv f x) → StrictMonoOn f D

-- Differentiability of normSq
have h_eq : (fun x => normSq (f x)) = (fun x => (f x).re^2 + (f x).im^2) := by
  ext x; rw [Complex.normSq_apply]; ring
exact (h_re.pow 2).add (h_im.pow 2)
```

---

## Session Progress

| Sorry | Status | Notes |
|-------|--------|-------|
| CalculusAxioms:21 | IN_PROGRESS | Structure done |
| EnergySymmetry:209 | PROVEN | re²+im² decomposition |
| EnergySymmetry:101,109 | BLOCKED | Need axiom |
| ClusterBound:83,102 | BLOCKED | Need helper |

---

*AI1 runs builds. AI2 works directly on proofs.*
