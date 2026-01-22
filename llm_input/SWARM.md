# Agent Swarm Dispatch Guide

**Version**: Batch D
**Coordinator**: AI1
**Build System**: Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
**Current Sorries**: 15

---

## AGENT CONSTRAINTS (MANDATORY - INCLUDE IN EVERY PROMPT)

```
## CONSTRAINTS (CRITICAL - VIOLATION = IMMEDIATE TERMINATION)

1. NEVER run `lake build` - AI1 handles ALL builds
2. NEVER spawn sub-agents or Task calls
3. NEVER modify files outside your ONE assigned target
4. NEVER exceed 10 tool calls - return with status after that
5. TIMEOUT after 5 minutes - if no result, return immediately
6. ALWAYS return structured result (see format below)
7. ONE proof attempt per agent - do not retry indefinitely
8. USE OPUS ONLY - Haiku is worthless for Lean 4.27 API

WORKFLOW:
1. Read the target file to understand context (1-2 tool calls)
2. Search Mathlib for relevant lemmas if needed (1-3 tool calls)
3. Edit the file with ONE proof attempt (1 tool call)
4. Return result immediately

RETURN FORMAT:
STATUS: [PROVEN | FAILED | NEEDS_WORK]
FILE: [path]
LINE: [number]
TECHNIQUE: [brief description]
CODE: [working proof if PROVEN]
BLOCKER: [what's missing if FAILED]
```

---

## Batch D Targets (5 agents)

### D1: CalculusAxioms taylor_second_order (Line 16)
```
File: Riemann/ProofEngine/CalculusAxioms.lean
Taylor's theorem with second-order remainder.
Search: taylor_mean_remainder, Mathlib Taylor API
May need ContDiff assumption instead of just Differentiable
```

### D2: EnergySymmetry Xi→Zeta FORWARD (Line 101)
```
File: Riemann/ProofEngine/EnergySymmetry.lean
Prove: Xi(s) = 0 → Zeta(s) = 0 in critical strip.
hs_ne_zero and hs_ne_one are already in context
Search: completedRiemannZeta, riemannXi
```

### D3: EnergySymmetry Zeta→Xi BACKWARD (Line 109)
```
File: Riemann/ProofEngine/EnergySymmetry.lean
Prove: Zeta(s) = 0 → Xi(s) = 0 in critical strip.
Key: completedRiemannZeta relationship, 1/(s(1-s)) simplification
```

### D4: EnergySymmetry local_min (Line 263)
```
File: Riemann/ProofEngine/EnergySymmetry.lean
Second derivative test: E'(1/2)=0 ∧ E''(1/2)>0 → strict local min
energy_deriv_zero_at_half is PROVEN (first condition)
h_convex hypothesis gives second condition
Search: IsLocalMin, strictConvexOn, taylor
```

### D5: ClusterBound sorries (Lines 83, 102)
```
File: Riemann/ProofEngine/ClusterBound.lean
Two sorries in cluster bound proofs
May require approximation bounds
Document blockers if stuck
```

---

## Current Sorries (15 total)

### Priority 1: EnergySymmetry (3 sorries)
| Line | Lemma | Hints |
|------|-------|-------|
| 101, 109 | riemannXi_zero_iff_zeta_zero | Two directions; needs completedZeta/Gamma API |
| 263 | symmetry_and_convexity_imply_local_min | Second deriv test |
| 305 | convexity_implies_norm_strict_min | Approximation transfer |

### Priority 2: CalculusAxioms (2 sorries)
| Line | Lemma | Hints |
|------|-------|-------|
| 16 | taylor_second_order | Taylor with remainder |
| 25 | effective_convex_implies_min | Uses taylor |

### Priority 3: TraceAtFirstZero (3 sorries)
| Line | Lemma | Hints |
|------|-------|-------|
| 77 | interval_bound | Interval arithmetic, first zero ≈ 14.134725 |
| 143 | first_zero_trace_pos | Numerical bound |
| 153 | trace_derivative_pos | Positivity argument |

### Priority 4: Other Files (7 sorries)
| File:Line | Lemma |
|-----------|-------|
| AnalyticAxioms:320 | finite_sum_approx_analytic (Explicit Formula - hard) |
| AristotleContributions:101 | contributed lemma |
| ClusterBound:83, 102 | cluster bounds |
| Convexity:104 | second_deriv_normSq (not critical path) |
| NumericalAxioms:23, 32 | numerical bounds |

---

## Agent Prompt Template

```
You are a Lean 4 proof agent for the Riemann Hypothesis formalization.

YOUR TASK: Fix the sorry at [FILE]:[LINE] - [LEMMA_NAME]

## CONSTRAINTS (CRITICAL)
- DO NOT run `lake build` (AI1 handles builds)
- DO NOT spawn sub-agents
- DO NOT modify other files
- Maximum 10 tool calls, then return result
- TIMEOUT: 5 minutes max - return immediately if stuck
- ONE proof attempt only

## WORKFLOW
1. Read [FILE] to see the lemma and context
2. Search for relevant Mathlib lemmas if needed
3. Edit the file with your proof attempt
4. Return result immediately

## RETURN FORMAT
STATUS: [PROVEN | FAILED | NEEDS_WORK]
FILE: [path]
LINE: [number]
TECHNIQUE: [description]
CODE: [proof if PROVEN]
BLOCKER: [issue if FAILED]

## HINTS
[specific hints for this lemma]

## API REFERENCE
- deriv.neg (not deriv_neg)
- nhdsWithin_le_nhds for filter restriction
- Complex.normSq_apply : normSq z = z.re * z.re + z.im * z.im
- Differentiable.comp for composition chains
- Complex.reCLM.differentiable, Complex.imCLM.differentiable

## CRITICAL STRATEGIES

### Rosetta Stone: Use abstract Mathlib lemmas, NOT zeta-specific reasoning
Search for general lemmas like tendsto_inv_nhdsGT_zero, Differentiable.comp, etc.
The abstract lemma is the "translation key" to Lean's math library.

### Helper Lemmas: ALWAYS decompose complex proofs
- Max 3-4 tactics per proof
- If you need `have` inside `have`, extract to separate lemma
- Name helpers: `energy_differentiable`, `gamma_ne_zero_in_strip`
```

---

## Session History

| Session | Sorries Before | Sorries After | Closed |
|---------|----------------|---------------|--------|
| Batch 1-5 | 96 | 52 | 44 |
| Batch 3 | 21 | 17 | 4 |
| Batch C | 17 | 16 | 1 |
| Batch D (current) | 16 | 15 | 1 (energy_deriv_zero_at_half) |

**Latest**: energy_deriv_zero_at_half PROVEN via re²+im² decomposition

---

## How to Launch Agents

```lean
-- Launch with constraints
Task(
  prompt="[Agent prompt with constraints above]",
  subagent_type="general-purpose",
  max_turns=10,
  run_in_background=True
)

-- Check results (non-blocking)
TaskOutput(task_id="xxx", block=False)

-- Kill runaway agents
KillShell(shell_id="xxx")
```

---

## Coordinator Workflow

1. **Launch batch** (4-6 agents on different files)
2. **Monitor every 2-3 min** with `TaskOutput(block=False)`
3. **Collect results** as each agent finishes
4. **Kill stragglers** after 5 minutes (STRICT)
5. **DO NOT run `lake build`** - AI1 handles all builds
6. **Verify with grep** for remaining sorries
7. **Report results** to AI1 for integration

---

## Lessons Learned

### API Issues (Mathlib 4.27)
- `omega` fails on `Int.negSucc` - use explicit contradiction
- `Preorder ℂ` doesn't exist - project to `.re` first
- `deriv.neg` vs `deriv_neg` - different lemmas!
- `zpow_neg` before converting to natural powers
- For `normSq` differentiability: decompose to `re² + im²`

### Agent Failures
- Agents claim SUCCESS but leave sorries - ALWAYS verify with grep
- Agents loop forever - use max_turns=10
- Agents run lake build - causes OOM, forbidden
- Agents spawn sub-agents - causes runaway processes
- Agents edit wrong file lines - verify line numbers

### What Works
- One agent per file
- Explicit constraints in prompt
- 10 tool call limit
- Background execution + periodic check
- Immediate result collection
- Clear hints with search terms

---

## Successful Patterns

```lean
-- Filter nhdsWithin restriction
exact hcont.mono_left nhdsWithin_le_nhds

-- Punctured neighborhood transfer
have hz_ne : Tendsto g (𝓝[>] x) (𝓝[≠] y) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz ?_
filter_upwards [self_mem_nhdsWithin] with σ hσ
...

-- Differentiability of normSq via re²+im² decomposition
have h_eq : (fun x => Complex.normSq (f x)) =
    (fun x => (f x).re^2 + (f x).im^2) := by
  ext x; rw [Complex.normSq_apply]; ring
rw [h_eq]
exact (h_re.pow 2).add (h_im.pow 2)

-- Complex function composition
have h_comp : Differentiable ℝ (g ∘ f) :=
  (g_diff.restrictScalars ℝ).comp f_diff
```

---

*AI1 is coordinator. Agents execute single tasks and return.*
