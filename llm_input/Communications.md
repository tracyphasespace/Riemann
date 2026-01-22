# AI Agent Communications Hub

**Last Updated**: 2026-01-22
**Build Status**: PASSING (3293 jobs)
**Sorry Count**: 17 total

---

## AGENT RULES (CRITICAL)

### DO NOT:
- **NEVER run `lake build`** - Only AI1 runs builds
- **NEVER spawn sub-agents**
- **NEVER modify files outside your assigned target**
- **NEVER run indefinitely** - Complete ONE task and return

### DO:
- Read files to understand context
- Search with Grep/Glob for API patterns
- Write a SINGLE proof attempt
- Return your result (success, failure, or strategy)
- Use max 10 tool calls per task

### Return Format:
```
STATUS: [PROVEN | FAILED | NEEDS_WORK]
FILE: path/to/file.lean
LINE: XX
TECHNIQUE: brief description
CODE: (if proven, the working proof)
BLOCKER: (if failed, what's missing)
```

---

## Current Sorries (17 total)

### Priority 1: CalculusAxioms (3 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 28 | contDiff_two_of_differentiable_deriv | BLOCKED - hypothesis too weak |
| 63 | taylor_case_2 | MVT argument needed |
| 125 | taylor_case_3 | x < x₀ case, reflection |

### Priority 2: EnergySymmetry (4 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 87 | riemannXi_zero_iff_zeta_zero | Gamma factors nonzero in strip |
| 193 | energy_deriv_zero_at_half | ZetaEnergy differentiability (ξ entire, normSq smooth) |
| 223 | symmetry_and_convexity_imply_local_min | Second derivative test |
| 242 | convexity_implies_norm_strict_min | C2 approximation transfer |

### Priority 3: TraceAtFirstZero (3 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 77 | interval_bound | Interval arithmetic |
| 143 | first_zero_trace_pos | Numerical bound |
| 153 | trace_derivative_pos | Positivity argument |

### Priority 4: Other Files
| File | Line | Lemma |
|------|------|-------|
| AnalyticAxioms.lean | 320 | filter extraction |
| AristotleContributions.lean | 101 | contributed lemma |
| ClusterBound.lean | 83, 102 | cluster bounds |
| Convexity.lean | 103 | second_deriv_normSq |
| NumericalAxioms.lean | 23, 32 | numerical bounds |

---

## CRITICAL: Proof Strategies

### 1. Rosetta Stone Technique
**Use abstract Mathlib lemmas, NOT domain-specific reasoning.**

```lean
-- BAD: Trying to prove zeta-specific facts directly
theorem zeta_thing : ... := by
  -- "zeta has a pole at s=1" - no Mathlib support!
  sorry

-- GOOD: Find abstract Mathlib lemma that applies
theorem zeta_thing : ... := by
  -- Use: tendsto_inv_nhdsGT_zero (abstract: 1/x → ∞ as x → 0⁺)
  -- Use: Tendsto.comp to compose with translation
  exact tendsto_inv_nhdsGT_zero.comp h_translation
```

The Mathlib lemma is the "Rosetta Stone" - it translates your domain problem into pure math that Lean already knows.

### 2. ALWAYS Use Small Helper Lemmas
**Lake struggles with deeply nested proofs. Decompose into atomic helpers.**

```lean
-- BAD: Complex nested proof
theorem big_theorem : P := by
  have step1 : A := by
    have substep : X := by long_proof  -- Lake timeout!
    exact use_substep substep
  exact final step1

-- GOOD: Separate helper lemmas
lemma helper_substep : X := by simple_proof
lemma helper_step1 : A := use_substep helper_substep
theorem big_theorem : P := final helper_step1
```

**Rules:**
- Max 3-4 tactics per proof
- Each helper proves ONE fact
- Name helpers descriptively: `pole_term_pos`, `sum_nonneg`
- If proof needs `have` inside `have`, extract to helper

---

## Techniques Reference

```lean
-- Filter nhdsWithin restriction
exact hcont.mono_left nhdsWithin_le_nhds

-- Punctured neighborhood
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within

-- Int case analysis
cases k with
| ofNat n => ...
| negSucc n => ...

-- Symmetry → zero derivative
deriv_comp_const_sub  -- for f(1-x) symmetry

-- Complex.re extraction
Complex.continuous_re.continuousAt.tendsto.comp
```

---

## Completed This Session

| Target | Status | Commit |
|--------|--------|--------|
| GeometricAxioms:17 frequency_incommensurability | PROVEN | e2a4d57 |
| GeometricAxioms:117 energy_persistence_proven | PROVEN | e2a4d57 |
| PhaseClustering:131 log_deriv_neg_divergence | PROVEN | e2a4d57 |
| ArithmeticAxioms:21 prime_pow_unique | PROVEN | e2a4d57 |

---

## AI2: EnergySymmetry Agent Assignments

**File**: `Riemann/ProofEngine/EnergySymmetry.lean`

Launch 4 agents (one per sorry):

### Agent ES-1: Line 87 - riemannXi_zero_iff_zeta_zero
```
In critical strip, Xi zero ↔ Zeta zero.
- s ≠ 0 and s ≠ 1 already proven (lines 83-86)
- Need: Gamma factors nonzero, completedZeta decomposition
- Search: riemannZeta, completedRiemannZeta₀, Gamma_ne_zero
```

### Agent ES-2: Line 193 - energy_deriv_zero_at_half
```
ZetaEnergy is differentiable (to apply deriv_zero_of_symmetric).
- ZetaEnergy t σ = normSq (riemannXi (σ + t*I))
- ξ is entire (analytic everywhere) → differentiable
- normSq is smooth (polynomial in re, im)
- Use: Differentiable.comp, Complex.differentiable_normSq
```

### Agent ES-3: Line 223 - symmetry_and_convexity_imply_local_min
```
Second derivative test: E'(1/2)=0, E''(1/2)>0 → strict local min.
- energy_deriv_zero_at_half gives E'(1/2) = 0
- h_convex : EnergyIsConvexAtHalf t gives E''(1/2) > 0
- Search: IsLocalMin, second_deriv_pos, Taylor
```

### Agent ES-4: Line 242 - convexity_implies_norm_strict_min
```
Bridge analytic energy to finite rotor sum.
- May require approximation bounds from ClusterBound
- Likely needs axiom or extensive setup
- If blocked, return NEEDS_WORK with analysis
```

---

*AI1 is build coordinator. Agents report results here.*
