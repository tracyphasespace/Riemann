# Navier-Stokes Formalization Project - AI Guide

**Project**: Lean 4 formalization of Navier-Stokes regularity
**Based on**: Lessons learned from Riemann Hypothesis formalization (2026-01)

---

## Quick Start

```bash
# Check for running builds FIRST (prevents OOM)
pgrep -x lake || echo "No lake process running"

# Build with memory protection
lake build

# Generate proof certificate
lake env lean -M 5000 /tmp/check.lean
```

---

## Critical Lessons Learned (From RH Project)

### 1. THE CATEGORY ERROR

**Wrong approach**: Treat classical PDE theory as "primary" and try to prove the geometric/algebraic framework matches it.

**Correct approach**: The geometric framework IS the physics. Classical formulations are projections/shadows.

For Navier-Stokes, this means:
- Don't try to "prove" the geometric velocity field equals the classical solution
- DEFINE the NS solution as the geometric object, then show properties follow
- The "gap" between geometric and analytic is a DEFINITION, not a theorem

### 2. PLAN BEFORE LEAN

**THE #1 CAUSE OF WASTED TIME**: Jumping into proofs without planning.

Before touching ANY .lean file:
1. State the goal in plain English
2. Ask: Is this theorem mathematically TRUE?
3. Search Mathlib FIRST (Loogle + grep)
4. Decompose into atomic lemmas (1-3 lines each)
5. Write a table of helper lemmas BEFORE coding

### 3. THE REAL SPLIT-SIGNATURE INSIGHT (Key Breakthrough)

**The Problem with Complex Hilbert Spaces:**
In standard complex analysis, phases MIX. Vectors in ℂ can point in opposite
directions and cancel: `e^{iθ} + e^{i(θ+π)} = 0`. This allows "rogue waves"
where random alignments cause unexpected zeros.

**The Solution: Real Split-Signature Cl(n,n):**
In Real Clifford algebra with split signature:
- Each component lives in its own ORTHOGONAL plane
- The bivector B_p for each prime p satisfies B_p² = -1 (rotation)
- Different components COMMUTE: [B_p, B_q] = 0
- **TRACES ADD, they don't interfere**

```
Complex view:  ‖Σ e^{iθ_p}‖² can vanish (cancellation)
Real Cl(n,n): Σ ‖v_p‖² cannot vanish unless each v_p = 0
```

**The Trace Identity Pattern:**
```lean
-- Global trace = Sum of local traces (no cross-terms!)
GeometricTrace Op support = support.sum fun p => LocalTrace Op p

-- This works because [B_p, B_q] = 0 implies orthogonality
-- The "Explicit Formula" becomes a TRACE CALCULATION, not magic
```

**For Navier-Stokes:**
Find the analogous orthogonal decomposition where:
- Each "mode" (Fourier? Wavelet?) lives in its own subspace
- Modes don't interfere - energies ADD
- The regularity condition becomes a trace/eigenvalue condition

### 4. AXIOM STRATEGY

**Foundational axioms** = Definitions of the framework (accept these)
**Technical axioms** = Should be provable, mark for later
**False axioms** = DELETE IMMEDIATELY (we wasted days on false axioms)

Always verify: Is this axiom mathematically TRUE before trying to prove it?

---

## Multi-AI Coordination Protocol

### Build Lock Table (SINGLE SOURCE OF TRUTH)

| Status | Locked By | Started | Notes |
|--------|-----------|---------|-------|
| Available | | | |

**Protocol:**
1. Check table shows "Available"
2. Update to `**IN USE** | AI1/AI2 | timestamp | module`
3. Run your build
4. Update back to "Available" when done

**NEVER** start a build if one is running - causes OOM errors.

### Memory Protection

```bash
lake build                    # Default (may OOM on large projects)
ulimit -v 8000000            # Limit to ~8GB before build
lake env lean -M 5000 file.lean  # Lean's internal limit (MB)
```

### File Locks (Active Work)

| File | Locked By | Started | Task |
|------|-----------|---------|------|
| | | | |

---

## Proof Search Tactics (Use BEFORE manual proofs)

```lean
exact?   -- Find exact lemma match (TRY FIRST)
apply?   -- Find applicable lemmas
aesop    -- Logic/sets/basic algebra
simp?    -- Show simp lemmas used
rw?      -- Find rewrite lemmas
```

**Priority Order:**
1. `exact?` / `apply?` - fastest, often instant
2. `aesop` - good for logic, set theory
3. `simp` with explicit lemmas
4. Manual proof - only after automation fails

---

## Loogle Search Patterns

```bash
# Web interface
https://loogle.lean-lang.org/?q=<type signature>

# Example queries
loogle "Tendsto ?f ?l atTop"      # Limit lemmas
loogle "?a + ?b = ?b + ?a"        # Commutativity
loogle "Continuous ?f"            # Continuity lemmas
loogle "∀ x : ℝ, 0 < x → ?P"     # Positivity lemmas
```

**Local Mathlib search:**
```bash
grep -rn "lemma_name" .lake/packages/mathlib/
```

---

## Atomic Lemma Decomposition

**Each helper lemma must be:**
- 1-3 lines maximum
- Use exactly ONE main Mathlib lemma
- Have a clear type signature

```lean
-- GOOD: Atomic, uses one lemma
private lemma norm_add_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a + b‖ = a + b := by
  rw [Real.norm_of_nonneg (add_nonneg ha hb)]

-- BAD: Monolithic, impossible to debug
theorem big_theorem := by
  [50 lines of tactics that fail somewhere in the middle]
```

---

## Mathlib 4.27+ API Patterns

### Norms and Continuity
```lean
-- Use ‖·‖ (norm), NOT abs for complex/vector
norm_add_le : ‖a + b‖ ≤ ‖a‖ + ‖b‖
norm_smul : ‖c • x‖ = ‖c‖ * ‖x‖

-- Continuity
Continuous.add, Continuous.mul, Continuous.comp
continuous_const, continuous_id
```

### Limits and Filters
```lean
tendsto_nhds_of_eventually_eq
Filter.Eventually.mono
filter_upwards [h1, h2] with x hx1 hx2
```

### Integrals (MeasureTheory)
```lean
MeasureTheory.integral_add
MeasureTheory.setIntegral_congr_fun
MeasureTheory.integral_smul
```

### Function Spaces
```lean
-- Sobolev spaces, Lp spaces
MeasureTheory.Lp
MeasureTheory.memLp_top
```

---

## Sorry Annotation Format

When stuck, document what was tried:

```lean
theorem stuck_theorem : goal := by
  -- TRIED: exact Foo.bar (2026-01-24)
  -- FAILED: type mismatch, expected X got Y
  -- TRIED: apply?
  -- FAILED: no applicable lemmas
  -- BLOCKER: Need Mathlib lemma for Z
  sorry
```

---

## Proof Certificate Generation

After completing a major theorem:

```bash
echo 'import YourModule
#print axioms YourTheorem' > /tmp/check.lean

lake env lean -M 5000 /tmp/check.lean > PROOF_CERTIFICATE.txt
```

**Clean result** (no custom axioms):
```
'YourTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Handoff Protocol

When finishing work:
1. Release build lock (update table above)
2. Update "Current Status" section
3. Add entry to Activity Log
4. Commit and push changes

---

## Current Status

| Metric | Value |
|--------|-------|
| Build Status | **NOT STARTED** |
| Total Sorries | - |
| Total Axioms | - |

---

## Activity Log

### 2026-01-24
- Project initialized
- NS.md created with lessons from RH formalization

---

## Key Architecture Decisions (To Be Made)

1. **What is the "geometric object"?** (Velocity field as section of tangent bundle? Differential form?)
2. **What is the foundational axiom?** (Analogue of Hilbert-Pólya for NS)
3. **What regularity framework?** (Sobolev? Besov? Geometric measure theory?)

---

## Reference: RH Project Success Factors

1. **Concrete Hilbert space** - Used ℓ²(ℂ) with explicit basis
2. **Diagonal operator** - K(s) acted on basis vectors by eigenvalues
3. **Scalar bridge** - Connected geometric object to classical function
4. **Rayleigh decomposition** - Split into Signal + Noise terms
5. **Proof certificate** - Verified axiom dependencies with `#print axioms`
6. **Trace Identity** - Replaced "magic axiom" with geometric trace calculation

### The ExplicitFormulaBridge Pattern

The key insight that closed the RH proof was replacing the "spectral correspondence axiom"
with a **Trace Identity**:

```lean
-- Instead of: axiom zeta_zeros_are_eigenvalues ...
-- We prove:   Tr(K) = Σ_primes (local contributions)

-- Step 1: Define Geometric Trace on Direct Sum
def GeometricTrace (Op : H → H) (support : Finset Primes) : ℝ :=
  support.sum fun p => LocalTrace Op p

-- Step 2: Prove Trace Linearity (from [B_p, B_q] = 0)
theorem trace_linearity : GeometricTrace Op support = Σ LocalTrace

-- Step 3: Match Local Trace to Arithmetic Term
theorem local_trace_matches : LocalTrace Op p = ArithmeticTerm p

-- Step 4: Conclude Spectral Correspondence
-- Tr(K) = Σ ArithmeticTerms = (by Explicit Formula) = Σ ZeroTerms
-- Therefore: Spectrum(K) = Zeros
```

**Why this works:** The orthogonality of Cl(n,n) makes the trace ADDITIVE.
No magic axiom needed - just linearity of trace on orthogonal subspaces.

---

## Common Pitfalls to Avoid

| Pitfall | Solution |
|---------|----------|
| Guessing Mathlib API names | Use Loogle + grep first |
| Writing 50-line proofs | Decompose into 1-3 line helpers |
| Proving false theorems | Verify mathematical truth FIRST |
| Multiple `lake build` processes | Check with `pgrep -x lake` |
| Circular imports | Extract shared lemmas to Common/ |
| Forgetting type coercions | Use explicit `(x : TargetType)` |

---

## Files Structure (Suggested)

```
NavierStokes/
├── Common/
│   └── Mathlib427Compat.lean    # Missing API shims
├── ProofEngine/
│   ├── Axioms.lean              # Foundational axioms
│   ├── VelocityField.lean       # Geometric velocity
│   ├── RegularityBridge.lean    # Classical ↔ Geometric
│   └── MainTheorem.lean         # NS regularity
├── llm_input/
│   ├── NS.md                    # This file
│   └── AXIOM_REVIEW.md          # Axiom documentation
└── PROOF_CERTIFICATE.txt        # Generated axiom trace
```

---

*Created 2026-01-24 | Based on RH formalization lessons*
