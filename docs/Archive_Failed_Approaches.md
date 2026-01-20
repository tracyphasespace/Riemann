# Archive: Failed Approaches & Removed Axioms

**Purpose**: Documents approaches that were tried and failed, hypotheses that were refuted, and axioms that were removed. This is crucial for avoiding repeated work.

---

## 1. TraceConvexity.WrongPath.leantxt - The Convexity Dead End

**Location**: `Riemann/ZetaSurface/archive/TraceConvexity.WrongPath.leantxt`

**The Attempted Approach**:
Prove `TraceStrictMinAtHalf` by showing trace is strictly convex on (0,1).

**What Was Proven**:
```lean
lemma rpow_neg_deriv (p : ℕ) (hp : 1 < p) (σ : ℝ) :
    HasDerivAt (fun σ => (p : ℝ) ^ (-σ)) (-Real.log p * (p : ℝ) ^ (-σ)) σ

lemma hasDerivAt_traceTerm (p : ℕ) (hp : 1 < p) (t σ : ℝ) :
    HasDerivAt (traceTerm p t) (-(Real.log p)² * p^{-σ} * cos(...)) σ
```

**Why It Failed**:
1. **Lean 4 elaboration issues**: List coercions created monadic `do` forms that didn't match lemmas
2. **Technical sorries accumulated**: `traceInnerSum_cons`, `traceInnerDerivSum_cons`
3. **The approach is mathematically incomplete**: Convexity of trace doesn't directly imply minimum at 1/2

**Lesson**: Direct calculus proofs on foldl sums are technically painful in Lean 4. The functional equation approach is cleaner.

---

## 2. RemovedAxioms.lean.txt - Historical Axiom Graveyard

**Location**: `Riemann/ZetaSurface/archive/RemovedAxioms.lean.txt`

### Axiom: Geometric_Explicit_Formula (NEVER USED)
```lean
-- axiom Geometric_Explicit_Formula (phi : GeometricTestFunction) (zeros : ℕ → ℝ) :
--   PrimeSignal phi = ZeroResonance zeros phi + corrections
```
The Weil explicit formula in Cl(N,N) language. Would require `Weil_Positivity_Criterion` to complete.

### Axiom: Plancherel_ClNN (NEVER USED)
```lean
-- axiom Plancherel_ClNN (phi : GeometricTestFunction) :
--     LogSpaceEnergy phi = (1 / 2π) * ∫ ClSquaredMagnitude phi t
```
Connects log-space energy to phase-space. Never implemented.

### Axiom: zeros_isolated (REMOVED)
```lean
-- axiom zeros_isolated (s₁ s₂ : GeometricParam)
--     (h_same_t : s₁.t = s₂.t) : s₁.sigma = s₂.sigma
```

**CRITICAL**: This is NOT the standard "isolated zeros" theorem!

Standard: Zeros of analytic functions are topologically isolated (can't accumulate).

This axiom: Zeros are unique per horizontal line (much stronger).

**Why it encodes RH**: Combined with functional equation (which pairs (σ,t) and (1-σ,t)):
1. If ζ(σ+it)=0, then ζ((1-σ)+it)=0
2. Both have same t
3. By axiom: σ = 1-σ, hence σ = 1/2

This was **circular** - it assumed RH in disguised form.

### Axiom: Weil_Positivity_Criterion (NEVER USED)
```lean
-- axiom Weil_Positivity_Criterion (zeros) (h_explicit) : RiemannHypothesis
```
This axiom directly states RH. It was intended for an alternative proof path that was never completed.

---

## 3. RotorFredholm.leantxt - Refuted Hypotheses

**Location**: `Riemann/ZetaSurface/archive/RotorFredholm.leantxt`

### REFUTED: det(I - R) peaks at zeros
**Test**: Compared det(I-R) oscillations to zeta zero locations
**Result**: WRONG FREQUENCY
- det(I-R) oscillates rapidly (~period 2-3 in t)
- Zeta zeros are spaced further apart
- No correlation in overlay plots

### REFUTED: φ'(t) extrema at zeros
**Test**: Visual plots seemed promising
**Result**: INSUFFICIENT
- Quantitative tests showed no reliable correlation
- Visual correlation was misleading

### DEFINITIVELY REFUTED: φ''(t) = 0 at zeros
**Test**: Checked 9 zeta zeros for phase inflection points
**Result**: Found ZERO crossings near any zero
- Mean distance to nearest crossing: ∞
- This hypothesis is completely wrong

### REFUTED: Curvature operator K_curv
**Definition**: K_curv := Im[d/dt Tr(R⁻¹ R')]
**Result**: Equivalent to φ''(t), already tested and failed

---

## 4. Alternative Proof Paths (Never Completed)

### Path 1: Current (Spectral) - ACTIVE
```
zero_implies_kernel → spectral_mapping → Critical_Line → σ = 1/2
```

### Path 2: Weil Positivity - ABANDONED
```
Geometric_Explicit_Formula + Plancherel_ClNN + Weil_Positivity_Criterion → RH
```
**Why abandoned**: Required deep analytic number theory not in Mathlib.

### Path 3: Functional Equation + Isolation - ABANDONED
```
functional_equation_zero + zeros_isolated → σ = 1/2
```
**Why abandoned**: `zeros_isolated` was circular (encoded RH).

---

## 5. LogDerivativePole.lean - The Vertical Approach Dead End

**Status**: File was DELETED from codebase

**The Mistake**: Tried to approach zero ρ vertically (keeping σ = ρ.re fixed, varying t).

**Why It Failed**: On the vertical line through ρ:
```
Re[1/(s-ρ)] = Re[1/(iδt)] = 0
```
The real part of the pole is ZERO on vertical approach! The pole structure vanishes.

**The Fix**: Use horizontal approach (σ → ρ.re⁺ with t = ρ.im fixed).
```
Re[1/(s-ρ)] = Re[1/(δσ)] = 1/δσ → +∞
```
This is now in `Residues.lean`.

---

## 6. Concepts That Seemed Promising But Weren't

### Menger Sponge Analogy
- **Idea**: Prime sieve is like Menger sponge (zero volume, infinite surface)
- **Status**: Poetic but not mathematically useful
- **Lesson**: Analogies guide intuition but don't prove theorems

### Berry Phase / Spectral Flow
- **Idea**: Track eigenspace rotation as t varies
- **Status**: Never implemented
- **Lesson**: Would require significant new infrastructure

### Higher-dimensional Cl(n,n)
- **Idea**: Full prime-indexed Clifford algebra reveals more structure
- **Status**: `PrimeClifford.leantxt` was developed but simplified to `PrimeRotor.lean`
- **Lesson**: Simpler finite-dimensional approximations suffice

---

## Summary: What NOT to Do

| Approach | Why It Failed |
|----------|---------------|
| Direct trace convexity | Lean 4 foldl elaboration issues |
| zeros_isolated axiom | Circular - encodes RH |
| Vertical approach to poles | Re[1/(iδ)] = 0, pole vanishes |
| Phase derivative zeros | Quantitatively refuted |
| det(I-R) at zeros | Wrong oscillation frequency |
| Weil explicit formula | Requires unimplemented theory |

---

## What DID Work (Preserved in Active Code)

1. **Horizontal pole approach**: Re[1/δσ] → +∞ ✓
2. **Orthogonal prime structure**: Cross-terms vanish ✓
3. **Stiffness divergence**: Σ(log p)² → ∞ ✓
4. **Functional equation symmetry**: s ↦ 1-s̄ fixes σ=1/2 ✓
5. **Rotor unitarity at σ=1/2**: Numerically verified ✓
