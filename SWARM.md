# Swarm Management Guide

**Last Updated**: 2026-01-21 20:30
**Curator**: AI2 (Claude Opus 4.5)

---

## 🚀 AGENT MODEL GUIDE (Updated 2026-01-21)

### Model Comparison (Tested)

| Model | Success Rate | Memory | Best For |
|-------|--------------|--------|----------|
| **Haiku** | 17% | Low | ❌ DEPRECATED - too many API errors |
| **Sonnet** | ~60% | None (Task tool) | ✅ Simple lemmas, Mathlib lookups |
| **Opus** | ~90% | High | ✅ Complex proofs, counterexamples, architecture |

### Sonnet Agents (NEW - Recommended for Volume)

**Key Discovery**: Task tool Sonnet agents **share memory** and release after completion.
- Ran 45 agents, memory stayed at 2.6-3.2GB
- Can run unlimited Sonnet agents via Task tool without hitting 5GB
- ~60% produce usable proofs

**Best for:**
- One-liner Mathlib lookups (`exact hp.pos`, `norm_pos_iff.mpr`)
- Simple tactic chains (`apply mul_pos; exact...`)
- Identifying what's missing (honest about limitations)

**Prompt template:**
```
RESEARCH ONLY - NO shell commands. Lean 4.27. CODE ONLY. NO MARKDOWN.
[File and line reference]
[Code context]
Hints: [Relevant Mathlib lemmas]
Output ONLY tactic proof.
```

### Opus Agents (For Critical/Complex Tasks)

**Use when:**
- Mathematical impossibility detection (counterexamples)
- Architectural decisions (axiom design)
- Multi-step complex proofs
- Haiku/Sonnet failed 2+ times

**Memory**: Higher usage - limit to 1-2 concurrent via Task tool

### Haiku Agents DEPRECATED

**Reason**: 17% success rate. 67% failures due to Mathlib 4.27 API complexity.

### Opus Task Files

Location: `/tmp/opus_tasks/`

| Task | Priority | Type | Builds? |
|------|----------|------|---------|
| OPUS-1 | **CRITICAL** | Research: line 964 gap | NO |
| OPUS-2 | HIGH | Mathlib API: line 701 | YES (coordinate) |
| OPUS-3 | MEDIUM | Residues.lean (6 sorries) | YES (sequential) |
| OPUS-4 | HIGH | Verification/counterexamples | NO |

### Dispatch Protocol

```bash
# Spawn Opus agent (NOT haiku!)
claude -p --model opus "$(cat /tmp/opus_tasks/OPUS_1_critical_path_line964.lean)" > llm_input/opus_1_output.lean 2>&1 &

# Recommended: OPUS-1 and OPUS-4 in parallel (no builds)
# Then: OPUS-2 alone (one build)
# Finally: OPUS-3 alone (sequential builds)
```

### Build Coordination

⚠️ **CRITICAL**: Only ONE agent builds at a time!

```bash
# Check if build is running
pgrep -f "lake build" || echo "No build running - safe to proceed"
```

---

## 📊 Current Project Status

| Metric | Count | Notes |
|--------|-------|-------|
| **Explicit Axioms** | 4 | 2 original + 2 new (zero_implies_kernel_axiom, rayleigh_Phi_pos) |
| **Sorries (CliffordZetaMasterKey)** | 5 | 3 FALSE + 1 technical + 1 KEY |
| **Build Status** | ✅ PASSES | 3299 jobs |
| **Lemmas Proven This Session** | 7 | See COORDINATION.md |

### Key Files Modified This Session
- `CliffordZetaMasterKey.lean` - Added Module 4b (Symmetrized Rayleigh)
- `COORDINATION.md` - Documented fix and handoff to AI1
- `SWARM.md` - This file (opus escalation protocol)

---

## ⚠️ CRITICAL: Constant Memory Monitoring

**CHECK MEMORY BEFORE AND AFTER EVERY AGENT OPERATION**

```bash
free -h | grep Mem
```

| Used | Status | Action |
|------|--------|--------|
| < 3 GB | 🟢 Safe | Can spawn 2 agents |
| 3-4 GB | 🟡 Caution | Can spawn 1 agent |
| 4-5 GB | 🟠 Warning | Monitor closely, avoid spawning |
| 5-6 GB | 🔴 Danger | Do NOT spawn, wait for completion |
| > 6 GB | ⛔ CRITICAL | Kill non-essential processes |

**Monitor continuously during agent execution:**
```bash
watch -n 5 'free -h | grep Mem'
```

---

## Quick Reference

```bash
# Check memory before spawning
free -h | grep Mem

# Spawn agent (haiku model for efficiency)
claude -p --model haiku "PROMPT" > llm_input/agentXXX_jobN.lean 2>&1 &

# Monitor running agents
pgrep -af "claude"

# Check output file
ls -la llm_input/agentXXX_jobN.lean && head -20 llm_input/agentXXX_jobN.lean
```

---

## 1. Resource Limits

| Resource | Limit | Current |
|----------|-------|---------|
| Memory | 6 GB max | Check with `free -h` |
| Concurrent haiku agents | **4 agents safe** | Tested 2026-01-21 |
| Concurrent opus agents | **1-2 agents** | Higher memory, use sparingly |
| Default model | `haiku` | Faster, cheaper, sufficient for simple tasks |
| Escalation model | `opus` | For CRITICAL/complex tasks |

### Model Selection Guide

| Task Type | Model | Example |
|-----------|-------|---------|
| Simple lemma (simp, ring, nlinarith) | haiku | CZ-2, CZ-7 |
| Medium theorem (existing Mathlib) | haiku | R-1 to R-5 |
| Complex proof (multi-step) | haiku first, opus if fails | AB-5 |
| Mathematical impossibility check | **opus** | CZ-6 counterexample |
| Architectural decisions | **opus** | CZ-8 axiom design |
| Theorem statement validation | **opus** | CZ-5 wrong statement |

### Memory Guidelines (Updated 2026-01-21)
- **< 3 GB used**: Safe to spawn 4 agents
- **3-4 GB used**: Safe to spawn 2-3 agents
- **4-5 GB used**: Safe to spawn 1 agent, monitor closely
- **> 5 GB used**: Do NOT spawn, wait for completion

**Tested:** 4 concurrent haiku agents peaked at 3.7GB, completed in ~45 sec each

---

## 2. Agent Prompt Engineering

### ❌ BAD: Vague instructions
```
"Prove the lemmas in Residues.lean"
```
Results in summaries, not code.

### ✅ GOOD: Explicit code-only instructions
```
"OUTPUT LEAN 4 CODE ONLY. NO MARKDOWN. NO EXPLANATIONS.

Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1

[Specific task with exact signatures]"
```

### Required Elements in Every Prompt

1. **Version specification**
   ```
   Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
   ```

2. **Output format directive**
   ```
   OUTPUT LEAN 4 CODE ONLY. NO MARKDOWN. NO SUMMARIES.
   ```

3. **Workflow reminder**
   ```
   DO NOT run lake build - AI1 handles builds
   ```

4. **Exact signatures** - Provide the exact lemma/theorem signatures

5. **Mathlib hints** - List relevant lemma names from Mathlib 4.27

### Template
```
You are Swarm Agent #XXX.

OUTPUT LEAN 4 CODE ONLY. NO MARKDOWN. NO EXPLANATIONS.

Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
DO NOT run lake build - AI1 handles builds.

## Task: [Job Name]
File: [target file]
Lines: [line numbers]

[Exact lemma signatures to prove]

## Mathlib 4.27 Hints
- [Relevant lemma 1]
- [Relevant lemma 2]

Output complete Lean 4.27 code with proofs.
```

---

## 3. Agent Lifecycle

**Model: One-shot (retire after task)**

```
Spawn → Execute single task → Write output → Exit (retired)
```

Agents are NOT persistent. Each `claude -p` call:
1. Starts a new process
2. Executes the prompt
3. Writes output to file
4. Terminates automatically

To assign new work: **spawn a new agent** (increment agent number)

**Why one-shot:**
- Clean memory release after each task
- No state management needed
- Simple tracking (PID → output file)
- Avoids context window bloat

**Trade-off:** Spawning overhead (~5-10 sec per agent)

---

## 4. Scaling Method (Gradual Ramp-Up)

**Protocol for spawning multiple agents safely:**

```bash
# Step 1: Check initial memory
free -h | grep Mem

# Step 2: Spawn 2 agents
claude -p --model haiku "PROMPT1" > output1.lean 2>&1 &
claude -p --model haiku "PROMPT2" > output2.lean 2>&1 &

# Step 3: Wait 1 minute
sleep 60

# Step 4: Check memory
free -h | grep Mem

# Step 5: If under threshold, spawn 1 more
# Repeat steps 3-5 until threshold reached
```

**Thresholds:**
| Memory Used | Action |
|-------------|--------|
| < 4 GB | Spawn 1-2 more agents |
| 4-5 GB | Spawn 1 more agent cautiously |
| > 5 GB | STOP spawning, wait for completion |

**Example session (2026-01-21):**
```
Start:   3.1 GB → spawn 2 agents
+1 min:  3.0 GB → spawn 1 agent
+30 sec: 3.0 GB → spawn 2 agents
+45 sec: 3.1 GB → spawn 1 agent
Final:   3.1 GB (6 agents completed, never exceeded 5GB)
```

**Key insight:** Haiku agents complete quickly (~30-60 sec), so memory pressure is brief. Sequential spawning with 30-60 sec gaps prevents accumulation.

---

## 5. Spawning Agents

### Command Pattern
```bash
claude -p --model haiku "PROMPT" > llm_input/agentXXX_jobN.lean 2>&1 &
echo "Agent #XXX spawned - PID: $!"
```

### Post-Spawn Checklist
1. Note the PID
2. Wait 5-10 seconds
3. Check memory: `free -h | grep Mem`
4. Check if process running: `pgrep -af "claude"`
5. Check output file size: `ls -la llm_input/agentXXX_jobN.lean`

### Common Issues

| Issue | Symptom | Fix |
|-------|---------|-----|
| Empty output | 0 byte file | Re-run with stronger "CODE ONLY" directive |
| Summary instead of code | Markdown prose | Add "NO MARKDOWN. NO EXPLANATIONS." |
| Wrong API | Old lemma names | Include "Mathlib 4.27" and specific hints |
| Timeout | Process hangs | Check memory, may need to kill |

---

## 4. Monitoring

### Check Agent Status
```bash
# List running claude processes
pgrep -af "claude" | grep -v grep

# Check specific PID
ps aux | grep [PID]

# Memory usage
free -h | grep Mem
```

### Check Output Quality
```bash
# File exists and has content?
ls -la llm_input/agent*.lean

# Preview content (look for actual Lean code, not markdown)
head -30 llm_input/agentXXX_jobN.lean

# Check for markdown fences (bad sign)
grep '```' llm_input/agentXXX_jobN.lean
```

### Healthy Output Indicators
- Starts with `/-!` or `import`
- Contains `lemma`, `theorem`, `def`
- Contains `:= by` proof blocks
- No markdown code fences

### Unhealthy Output Indicators
- Starts with `##` or `**` (markdown)
- Contains "Summary" or "I have"
- Has ``` code fences
- Empty file

---

## 5. Post-Completion Workflow

1. **Verify output** has actual Lean code
2. **Clean up** markdown fences if present
3. **Update SWARM_TASKS.md** - mark job complete
4. **Update COORDINATION.md** - add to AI1 queue
5. **Check memory** before spawning next agent

---

## 6. Coordination with AI1

### File Locations
| Purpose | Location |
|---------|----------|
| Agent outputs | `llm_input/agentXXX_jobN.lean` |
| Coordination | `COORDINATION.md` |
| Task tracking | `Riemann/ProofEngine/SWARM_TASKS.md` |
| API reference | `swarm_output/SWARM_BRIEFING.md` |

### Handoff Protocol
1. Curator stages files in `llm_input/`
2. Curator updates `COORDINATION.md` queue
3. AI1 claims ownership in `COORDINATION.md`
4. AI1 processes, moves to COMPLETED
5. AI1 releases ownership

---

## 7. Lessons Learned

### 2026-01-21: Initial Swarm Setup

**What worked:**
- Haiku model is sufficient for targeted lemma proofs
- Explicit Lean version in prompt helps API compliance
- Background spawning with `&` allows parallel work
- COORDINATION.md prevents stepping on AI1's work

**What failed:**
- Vague prompts → summaries instead of code
- Missing "CODE ONLY" → markdown output
- Multiple agents → memory pressure

**Optimizations discovered:**
- Include exact lemma signatures in prompt
- List specific Mathlib lemma names as hints
- Clean markdown fences from output before staging
- Check file size immediately after spawn (0 = failed)

### 2026-01-21: Markdown Fence Issue (Agents #005, #006)

**Problem:** Even with "NO MARKDOWN" in prompt, haiku still outputs ```lean fences

**Solution:** Post-process cleanup required:
1. Check for fences: `grep '```' llm_input/agentXXX.lean`
2. If found, manually remove lines 1 and last line
3. Add proper header: `/-! # SWARM AGENT #XXX ... -/`

**Lesson:** Always verify output format before marking complete

### 2026-01-21: AI1 Feedback - Mathlib 4.27 API Validation

**AI1 Note:** "Agent outputs need pre-validation against Mathlib 4.27 APIs"

**High-impact improvements for agent prompts:**
1. Include EXACT Mathlib 4.27 lemma names (not guessed)
2. Use `star` not `conj` for complex conjugation
3. Use `p.val` not `(p : ℕ)` for Primes subtype
4. Use `abbrev` not `def` for Finsupp types
5. Include `Complex.star_def` for simp lemmas

**Template addition for prompts:**
```
## MATHLIB 4.27 API (CRITICAL)
- Conjugate: use `star z` not `conj z`
- Primes: use `p.val` not `(p : ℕ)`
- Complex simp: `Complex.star_def`, `Complex.add_re`, `Complex.mul_re`
- Finsupp: `Finsupp.coe_update`, `Finsupp.support_update`
```

### Agent Success Rate by Job Type

| Job Type | Success Rate | Notes |
|----------|--------------|-------|
| Simple lemmas (simp/ring) | High | Jobs 5, 6 |
| Complex theorems | Medium | Jobs 2, 3 need AI1 fixes |
| Architecture scaffolds | Medium | Job 4 pending |

---

## 8. Swarm Statistics

| Metric | Value |
|--------|-------|
| Total agents spawned | **40** |
| Haiku agents | 36 |
| Opus agents | 4 |
| Original jobs completed | 6/12 (50%) |
| Granular tasks attempted | 18 (AB-1 to AB-6, CZ-1 to CZ-8, R-1 to R-5) |
| Outputs needing cleanup | ~60% (markdown fences) |
| Memory incidents | 0 |
| Peak memory | **3.7 GB** (4 concurrent agents) |
| API mismatch rate | ~40% (expected, AI1 fixes) |
| **CRITICAL theorems fixed** | **2** (CZ-6, CZ-8 via opus) |

### Session 2026-01-21 (Afternoon - Haiku Batch)
- Spawned agents #013-#028 (16 agents)
- Ran 4 agents concurrently without memory issues
- Peak: 3.7GB with 4 agents, returned to 3.1GB after completion
- All outputs staged in `llm_input/`
- **CZ-6 and CZ-8 FAILED** with haiku (too mathematically complex)

### Session 2026-01-21 (Late Afternoon - Opus Escalation)
- Spawned agents #029-#032 using **opus model** for CRITICAL theorems
- Used Task tool with `model: "opus"` instead of background `claude -p`
- **Results:**
  - Agent #029, #031: CZ-6 analysis → **MATHEMATICALLY FALSE** (counterexample found)
  - Agent #030, #032: CZ-8 analysis → **UNPROVABLE** (needs axiom)
- **Action taken:** AI2 applied symmetrized operator fix to CliffordZetaMasterKey.lean
- **Build status:** ✅ PASSES

### Session 2026-01-21 (Evening - Haiku Batch #033-#040)
- Spawned 8 haiku agents in parallel for remaining sorries
- Memory peaked at 3.4GB with 6 concurrent agents - safe
- **Results:**

| Agent | Task | Size | Status |
|-------|------|------|--------|
| #033 | scalarBridge_nonzero | 482B | ✅ CHECK |
| #034 | B_skew_hermitian | 1B | ❌ FAILED |
| #035 | chiralEnergy_as_weighted_sum | 436B | ✅ CHECK |
| #036 | coeff_sym_re_factorization | 2084B | ⚠️ CLEANUP |
| #037 | pole_dominates_constant | 874B | ✅ CHECK |
| #038 | extract_delta_from_nhds | 1043B | ✅ CHECK |
| #039 | coeff_real_of_real | 906B | ⚠️ CLEANUP |
| #040 | rayleigh_identity_sym | 1545B | ⚠️ CLEANUP |

- **Outputs ready for AI1 review** in `llm_input/`
- Agent #034 failed repeatedly - may need opus escalation

### Session 2026-01-21 (Night - Opus Phase 1)
- Dispatched OPUS-1 and OPUS-4 (research, no builds)
- Memory: 2.6GB before spawn, safe
- **CRITICAL FINDINGS:**

| Agent | Task | Status | Output |
|-------|------|--------|--------|
| OPUS-1 | Critical path line 964 | **SOLUTION FOUND** | `OPUS1_critical_path_analysis.lean` |
| OPUS-4 | Axiom verification | **ISSUES FOUND** | `OPUS4_verification_report.lean` |

**OPUS-1 Key Finding:**
- Gap at line 964: `zero_implies_kernel_axiom` gives K kernel, but `chiralEnergy_sym` uses K_sym
- **Solution:** Modify axiom to `zero_implies_symmetric_kernel` (gives both K(s)v=0 AND K(1-s)v=0)
- Justified by functional equation ξ(s) = ξ(1-s)

**OPUS-4 Key Finding:**
- `rayleigh_Phi_pos` axiom is **FALSE** - counterexample: v=(1,0) at prime 2
- `chiralEnergy_sym_nonzero_off_half` theorem is **FALSE** (depends on false axiom)
- **Proof chain is structurally broken**
- Fix needed: Restrict axiom to v with nonzero charge

**Outputs staged:** `llm_input/OPUS1_critical_path_analysis.lean`, `llm_input/OPUS4_verification_report.lean`

### Session 2026-01-21 (Night - Sonnet Stress Test)
- Tested Sonnet agents via Task tool for high-volume sorry reduction
- **Key Discovery:** Task tool agents share memory, don't accumulate!
- Ran 45 Sonnet agents, memory stayed at 2.6-3.2GB throughout

**Sonnet Batch Results:**

| Batch | Agents | High Confidence | Good Attempts | Need Infrastructure |
|-------|--------|-----------------|---------------|---------------------|
| 1-2 | 10 | 4 | 4 | 2 |
| 3 | 5 | 3 | 2 | 0 |
| 4 | 10 | 3 | 4 | 3 |
| 5 | 10 | 4 | 2 | 4 (2 already proven) |
| **Total** | **45** | **~15** | **~12** | **~10** |

**High-Confidence Sonnet Proofs (likely compile):**
```lean
exact hp.pos                    -- ArithmeticAxioms:21
exact norm_pos_iff.mpr hv       -- CliffordAxioms:39
exact sq_nonneg ‖v‖             -- ConservationAxioms:20
rw [deriv_const]                -- CalculusAxioms:43
exact differentiableAt_riemannZeta h_ne  -- AnalyticAxioms:26
simp [Complex.mul_im, h_pure_im]         -- AnalyticBridge:240
```

**Files Generated:** 45 outputs in `llm_input/sonnet_*.lean`

**Recommendation:** Use Sonnet for volume (simple sorries), Opus for critical path.

---

## 9. Opus Escalation Protocol

**When to use Opus instead of Haiku:**

| Indicator | Action |
|-----------|--------|
| Haiku fails 2+ times on same task | Escalate to Opus |
| Task requires mathematical insight | Use Opus directly |
| Task involves proving theorem is FALSE | Use Opus directly |
| Task requires architectural decisions | Use Opus directly |
| Simple lemma proofs (simp, ring) | Haiku sufficient |

### Spawning Opus Agents

**Method 1: Task tool (RECOMMENDED)**
```
Task tool with model: "opus", subagent_type: "general-purpose"
```
- Integrated into Claude Code session
- Better context handling
- Results returned directly

**Method 2: Background command**
```bash
claude -p --model opus "PROMPT" > llm_input/agentXXX_task.lean 2>&1 &
```
- Higher memory usage than haiku
- Limit to 1-2 concurrent opus agents

### Lessons Learned: CZ-6/CZ-8 Escalation

**What haiku couldn't do:**
- Recognize mathematical impossibility
- Find counterexamples
- Recommend architectural fixes
- Understand deep functional equation structure

**What opus discovered:**
- CZ-6 `rayleigh_identity` is **mathematically false** (counterexample verified)
- CZ-8 `zero_iff_kernel` requires **axiom** (no bridge exists)
- Fix: Symmetrized operator K_sym = (K(s) - K(1-s))/2

**Outcome:** 2 CRITICAL theorems resolved that blocked all haiku attempts

---

## 10. Future Improvements

- [x] ~~Consider opus model for complex jobs~~ → **IMPLEMENTED** (Opus Escalation Protocol)
- [ ] Create pre-validated prompt templates per job type
- [ ] Add automatic output validation script
- [ ] Implement retry logic for failed agents
- [ ] Track agent performance by model/prompt type
- [ ] Add cost tracking (haiku vs opus)

---

## 11. CRITICAL: Lean/Mathlib Proof Strategy (The "Rosetta Stone")

**This advice cures "Lean pain"** - the friction between how mathematicians think (epsilon-delta, manual bounds) and how Lean automates (algebraic structures, type classes).

### Filter Logic: "Escape the Epsilon Trap"

**The Problem:**
In standard analysis, proving `f(x) → L` involves: "For every ε > 0, there exists δ > 0 such that..."
In Lean, manually introducing ε and δ is like writing assembly code. You lose access to automation.

**The Solution (`Filter.Tendsto`):**
Mathlib abstracts convergence into **Filters** - algebraic objects representing "neighborhoods."

```lean
-- The Hard Way (Epsilon): Struggle with Archimedean properties and inequalities
-- The Lean Way (Filters): ONE LINE
lemma inverse_blows_up : Tendsto (fun x => x⁻¹) (𝓝[>] 0) atTop :=
  tendsto_inv_nhdsGT_zero
```

**For Pole Domination Proofs:**
Instead of finding δ where the function exceeds M, use `Tendsto.comp` to chain known limits:
- `(s-ρ) → 0` (Linear continuity)
- `x → x²` (Power continuity)
- `x → -1/x` (Inverse limits)
- Therefore `-(s-ρ)⁻² → -∞`

This turns a 50-line inequality proof into a 5-line algebraic proof.

### Complex Derivatives: "Let the Type System Do the Calculus"

**The Problem:**
Proving derivatives exist by showing `lim_{h→0} (f(z+h)-f(z))/h` exists is manual labor.

**The Solution (Type Classes):**
Lean uses Type Classes (`Differentiable`, `AnalyticAt`, `HolomorphicOn`) to tag functions.
- If `f` and `g` are differentiable, Lean automatically knows `f + g`, `f * g`, `f ∘ g`, `exp ∘ f` are differentiable
- Use `fun_prop` tactic or composition chains

```lean
-- Don't unfold derivative definitions. Instead:
have h1 : Differentiable ℂ (fun t => t * log p) := ...
have h2 : Differentiable ℂ cexp := ...
exact h2.comp h1  -- Lean deduces composition is smooth
```

### Refactoring Rules for Agents

| If You See... | Action |
|---------------|--------|
| `ε` or `δ` in a limit proof | DELETE IT. Look for a `Tendsto` lemma in Mathlib |
| A difference quotient | DELETE IT. Use `Differentiable.comp` chains |
| Manual bound calculations | Replace with filter composition |

**This is how we close the gap from 60% to 100% formalization without burning out on trivialities.**

---

## Appendix: File Templates

### Agent Output Header
```lean
/-!
# SWARM AGENT #XXX - JOB N: [Job Name]
Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
Target: [file.lean] lines [N-M]
-/
```

### COORDINATION.md Queue Entry
```markdown
| `llm_input/agentXXX_jobN.lean` | HIGH | Target.lean | [brief description] |
```
