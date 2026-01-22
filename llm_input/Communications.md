# AI Agent Communications Hub

**Last Updated**: 2026-01-22 (Batch D)
**Build Status**: PASSING
**Sorry Count**: 15 total

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

## Current Sorries (15 total)

### Priority 1: EnergySymmetry (3 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 101, 109 | riemannXi_zero_iff_zeta_zero | Two directions; needs Mathlib completedZeta/Gamma API |
| 263 | symmetry_and_convexity_imply_local_min | Second derivative test, needs C² |
| 305 | convexity_implies_norm_strict_min | C2 approximation transfer |

### Priority 2: CalculusAxioms (2 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 16 | taylor_second_order | Taylor with remainder |
| 25 | effective_convex_implies_min_proven | Uses taylor_second_order |

### Priority 3: TraceAtFirstZero (3 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 77 | interval_bound | Interval arithmetic |
| 143 | first_zero_trace_pos | Numerical bound |
| 153 | trace_derivative_pos | Positivity argument |

### Priority 4: Other Files
| File | Line | Lemma |
|------|------|-------|
| AnalyticAxioms.lean | 320 | finite_sum_approx_analytic |
| AristotleContributions.lean | 101 | contributed lemma |
| ClusterBound.lean | 83, 102 | cluster bounds |
| Convexity.lean | 104 | second_deriv_normSq (OK to skip - not critical path) |
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

### 2. ALWAYS Use Small Helper Lemmas
**Max 3-4 tactics per proof. Decompose into atomic helpers.**

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

---

## Batch D: Agent Assignments (5 agents)

### Agent D1: CalculusAxioms taylor_second_order (Line 16)
**File**: `Riemann/ProofEngine/CalculusAxioms.lean`
```
Prove Taylor's theorem with second-order remainder.
- Search: taylor_mean_remainder, Mathlib Taylor API
- May need: ContDiff assumption instead of just Differentiable
- Return exact Mathlib lemma name if found
```

### Agent D2: EnergySymmetry riemannXi_zero_iff_zeta_zero FORWARD (Line 101)
**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
```
Prove: Xi(s) = 0 → Zeta(s) = 0 in critical strip.
- s(1-s) ≠ 0 in strip (already have hs_ne_zero, hs_ne_one)
- Need: completedRiemannZeta₀ decomposition
- Search: completedRiemannZeta, riemannXi
```

### Agent D3: EnergySymmetry riemannXi_zero_iff_zeta_zero BACKWARD (Line 109)
**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
```
Prove: Zeta(s) = 0 → Xi(s) = 0 in critical strip.
- If ζ(s) = 0, then completedRiemannZeta s = 0
- Need: relationship between completedRiemannZeta₀ and completedRiemannZeta
- Key: 1/s + 1/(1-s) = 1/(s(1-s)) simplifies with s(1-s) factor
```

### Agent D4: EnergySymmetry symmetry_and_convexity_imply_local_min (Line 263)
**File**: `Riemann/ProofEngine/EnergySymmetry.lean`
```
Second derivative test: E'(1/2)=0 ∧ E''(1/2)>0 → strict local min.
- energy_deriv_zero_at_half gives first condition (PROVEN)
- h_convex hypothesis gives second condition
- Search: IsLocalMin, strictConvexOn, taylor
- May need MVT or Taylor expansion
```

### Agent D5: ClusterBound sorries (Lines 83, 102)
**File**: `Riemann/ProofEngine/ClusterBound.lean`
```
Two sorries in cluster bound proofs.
- Read the file to understand context
- These may require approximation bounds
- If blocked, document what's needed
```

---

## Completed This Session

| Target | Status | Notes |
|--------|--------|-------|
| GeometricAxioms:17 frequency_incommensurability | PROVEN | e2a4d57 |
| GeometricAxioms:117 energy_persistence_proven | PROVEN | e2a4d57 |
| PhaseClustering:131 log_deriv_neg_divergence | PROVEN | e2a4d57 |
| ArithmeticAxioms:21 prime_pow_unique | PROVEN | e2a4d57 |
| Convexity:103 second_deriv_normSq_eq | PROVEN | Batch B |
| **EnergySymmetry:209 energy_deriv_zero_at_half** | **PROVEN** | Batch D - re²+im² decomp |

---

## Techniques Reference

```lean
-- Filter nhdsWithin restriction
exact hcont.mono_left nhdsWithin_le_nhds

-- Punctured neighborhood
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within

-- Symmetry → zero derivative
deriv_comp_const_sub  -- for f(1-x) symmetry

-- Complex.re extraction
Complex.continuous_re.continuousAt.tendsto.comp

-- Differentiability of normSq composition
-- Decompose: normSq = re² + im²
have h_eq : f = (fun x => g(x).re^2 + g(x).im^2) := by
  ext x; simp [Complex.normSq_apply]; ring
exact (h_re.pow 2).add (h_im.pow 2)
```

---

*AI1 is build coordinator. Agents report results here.*
