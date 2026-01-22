# Agent Swarm Dispatch Guide

**Version**: Batch 3
**Coordinator**: AI1
**Build System**: Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
**Current Sorries**: 17

---

## AGENT CONSTRAINTS (MANDATORY - INCLUDE IN EVERY PROMPT)

```
## CONSTRAINTS (CRITICAL - VIOLATION = IMMEDIATE TERMINATION)

1. NEVER run `lake build` - AI1 handles ALL builds
2. NEVER spawn sub-agents or Task calls
3. NEVER modify files outside your ONE assigned target
4. NEVER exceed 10 tool calls - return with status after that
5. ALWAYS return structured result (see format below)
6. ONE proof attempt per agent - do not retry indefinitely

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

## Current Sorries (17 total)

### Priority 1: EnergySymmetry (4 sorries) - HIGH VALUE
| Line | Lemma | Hints |
|------|-------|-------|
| 75 | conjugate_symmetry | Schwarz reflection, Mellin transform workaround |
| 187 | energy_convex_at_half | Second derivative > 0, functional equation |
| 210 | deriv_energy_zero_at_half | Symmetry → zero derivative at center |
| 232 | strict_min_at_half | Convexity + zero deriv → unique min |

### Priority 2: CalculusAxioms (3 sorries)
| Line | Lemma | Hints |
|------|-------|-------|
| 28 | contDiff_two | BLOCKED - hypothesis too weak, may need axiom |
| 63 | taylor_case_2 | MVT, x > x₀ case |
| 125 | taylor_case_3 | MVT, x < x₀ case, reflection |

### Priority 3: TraceAtFirstZero (3 sorries)
| Line | Lemma | Hints |
|------|-------|-------|
| 77 | interval_bound | Interval arithmetic, first zero ≈ 14.134725 |
| 143 | first_zero_trace_pos | Numerical bound |
| 153 | trace_derivative_pos | Positivity argument |

### Priority 4: Other Files (7 sorries)
| File:Line | Lemma |
|-----------|-------|
| AnalyticAxioms:320 | filter extraction |
| AristotleContributions:101 | contributed lemma |
| ClusterBound:83 | cluster bound 1 |
| ClusterBound:102 | cluster bound 2 |
| Convexity:103 | second_deriv_normSq |
| NumericalAxioms:23 | numerical bound 1 |
| NumericalAxioms:32 | numerical bound 2 |

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
- tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
- Complex.normSq_eq_norm_sq : normSq z = ‖z‖²
```

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
4. **Kill stragglers** after 10 minutes
5. **Run single `lake build`** after all agents done
6. **Verify with grep** for remaining sorries
7. **Commit successful proofs**

---

## Lessons Learned

### API Issues (Mathlib 4.27)
- `omega` fails on `Int.negSucc` - use explicit contradiction
- `Preorder ℂ` doesn't exist - project to `.re` first
- `deriv.neg` vs `deriv_neg` - different lemmas!
- `zpow_neg` before converting to natural powers

### Agent Failures
- Agents claim SUCCESS but leave sorries - ALWAYS verify with grep
- Agents loop forever - use max_turns=10
- Agents run lake build - causes OOM, forbidden
- Agents spawn sub-agents - causes runaway processes

### What Works
- One agent per file
- Explicit constraints in prompt
- 10 tool call limit
- Background execution + periodic check
- Immediate result collection

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

-- Int case split (handles both positive and negative)
cases k with
| ofNat n => ...
| negSucc n => exact absurd (Int.natCast_nonneg n) (not_le.mpr hk_neg)

-- FTA for prime powers
NumberTheoryFTA.prime_power_eq_iff hp hq hne n m

-- Divergent + convergent limits
-- f → -∞, g → c ⟹ f + g → -∞
have tendsto_atBot_add_of_tendsto := ...
```

---

## Session History

| Session | Sorries Before | Sorries After | Closed |
|---------|----------------|---------------|--------|
| Batch 1-5 | 96 | 52 | 44 |
| Batch 3 (current) | 21 | 17 | 4 |

**Latest commit**: e2a4d57 - frequency_incommensurability, energy_persistence, log_deriv_neg_divergence, prime_pow_unique

---

*AI1 is coordinator. Agents execute single tasks and return.*
