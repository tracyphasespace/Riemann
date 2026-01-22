# AI Agent Communications Hub

**Last Updated**: 2026-01-22 (Batch D - Updated)
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

## HANDLING NEEDS_WORK (FOR AI2)

When an agent returns **NEEDS_WORK**, follow this process:

### 1. If BLOCKER is "missing Mathlib lemma":
- Search Mathlib docs for the lemma name
- If lemma exists: re-dispatch agent with exact lemma name
- If lemma doesn't exist: **ADD AS AXIOM** with clear documentation

### 2. If BLOCKER is "signature mismatch":
- AI1 will fix the signature (already done for taylor_second_order)
- Re-dispatch agent with updated signature

### 3. If BLOCKER is "needs helper lemma":
- **CREATE THE HELPER LEMMA** first
- Add it to the file BEFORE the main theorem
- Then re-dispatch agent for main theorem

### 4. If BLOCKER is "algebraic complexity":
- Break into 2-3 smaller lemmas
- Each lemma: max 3-4 tactics
- Dispatch agents for each helper, then main theorem

**EXAMPLE - Handling D2/D3 blocker:**
```
D2/D3 need: completedRiemannZeta₀_eq (decomposition)

Option A: Search Mathlib for existing lemma
  → Grep for "completedRiemannZeta₀" in .lake/packages/mathlib

Option B: If not found, add axiom:
  axiom completedRiemannZeta₀_eq (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta₀ s = completedRiemannZeta s + s⁻¹ + (1 - s)⁻¹

Option C: Prove from definitions (if tractable)
```

---

## Current Sorries (15 total)

### Priority 1: EnergySymmetry (3 sorries)
| Line | Lemma | Notes |
|------|-------|-------|
| 101, 109 | riemannXi_zero_iff_zeta_zero | Two directions; needs completedZeta decomposition |
| 263 | symmetry_and_convexity_imply_local_min | Second derivative test |
| 305 | convexity_implies_norm_strict_min | C2 approximation transfer |

### Priority 2: CalculusAxioms (2 sorries) - SIGNATURE FIXED
| Line | Lemma | Notes |
|------|-------|-------|
| 21 | taylor_second_order | **NOW: `ContDiff ℝ 2 f`** - search `taylor_mean_remainder` |
| 32 | effective_convex_implies_min_proven | Uses taylor_second_order |

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
| Convexity.lean | 104 | second_deriv_normSq (OK to skip) |
| NumericalAxioms.lean | 23, 32 | numerical bounds |

---

## Batch D Status

| Agent | Task | Status | Next Action |
|-------|------|--------|-------------|
| D1 | taylor_second_order | NEEDS_WORK | **SIGNATURE FIXED** - re-dispatch with `ContDiff ℝ 2 f` |
| D2 | riemannXi forward | NEEDS_WORK | Search Mathlib for decomposition lemma, or add axiom |
| D3 | riemannXi backward | NEEDS_WORK | Same as D2 |
| D4 | local_min | RUNNING | Wait for completion |
| D5 | ClusterBound | NEEDS_WORK | Add `c2_stability_transfer` helper first |

### Batch D Blockers Resolved:
- [x] D1: `taylor_second_order` signature changed to `ContDiff ℝ 2 f`

### Batch D Blockers Pending:
- [ ] D2/D3: Need `completedRiemannZeta₀_eq` decomposition
- [ ] D5: Need `c2_stability_transfer` helper lemma

---

## CRITICAL: Proof Strategies

### 1. Rosetta Stone Technique
**Use abstract Mathlib lemmas, NOT domain-specific reasoning.**

```lean
-- GOOD: Find abstract Mathlib lemma that applies
theorem zeta_thing : ... := by
  exact tendsto_inv_nhdsGT_zero.comp h_translation
```

### 2. ALWAYS Use Small Helper Lemmas
**Max 3-4 tactics per proof. Decompose into atomic helpers.**

```lean
-- GOOD: Separate helper lemmas
lemma helper_substep : X := by simple_proof
lemma helper_step1 : A := use_substep helper_substep
theorem big_theorem : P := final helper_step1
```

---

## Techniques Reference

```lean
-- Taylor with ContDiff
-- Search: taylor_mean_remainder_lagrange, taylor_mean_remainder_bound
-- Requires: ContDiff ℝ n f or ContDiffOn

-- Filter nhdsWithin restriction
exact hcont.mono_left nhdsWithin_le_nhds

-- Differentiability of normSq composition (PROVEN pattern)
have h_eq : f = (fun x => g(x).re^2 + g(x).im^2) := by
  ext x; simp [Complex.normSq_apply]; ring
exact (h_re.pow 2).add (h_im.pow 2)
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
| **EnergySymmetry:209 energy_deriv_zero_at_half** | **PROVEN** | Batch D |

---

*AI1 is build coordinator. Agents report results here.*
