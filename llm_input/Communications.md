# AI Communications Log

**Last Updated**: 2026-01-23

---

## Current Status: BUILD PASSES ✅

| Metric | Value |
|--------|-------|
| Build Status | **PASSING** (3296 jobs) |
| Total Sorries | **0** |
| Total Axioms | **15** (documented in AXIOM_REVIEW.md) |
| Critical Path | **SORRY-FREE** |

---

## ⚠️ BEFORE YOU START ANY WORK

**READ THIS FIRST**: The #1 cause of wasted time is thrashing.

### Mandatory Workflow

1. **PLAN FIRST** - Write a plan with atomic lemmas BEFORE touching .lean files
2. **SEARCH FIRST** - Use Loogle + `exact?`/`apply?` before writing manual proofs
3. **DECOMPOSE** - Break proofs into 1-3 line helpers, each using ONE Mathlib lemma
4. **STOP WHEN STUCK** - Document blockers and move on, don't spend hours on one sorry

See `CLAUDE.md` → "MANDATORY: Plan-First Workflow" for full details.

---

## Build Coordination

**Check for running builds**:
```bash
pgrep -x lake || echo "No lake process running"
```

**NEVER** start a build if one is running - causes OOM errors.

### Lake Build Lock Table

| Status | Locked By | Started | Notes |
|--------|-----------|---------|-------|
| Available | | | |

---

## Architecture Summary

### Bridge Architecture (Complete)

| Bridge | Status | Method |
|--------|--------|--------|
| **M1: B²=-I** | **PROVEN** | Diagonal eigenvalue model |
| **M2: Commutativity** | **PROVEN** | Diagonal operators commute |
| **M3: Scalar Bridge** | **PROVEN** | `riemannZeta_eulerProduct_tprod` |
| **M5: Rayleigh** | **PROVEN** | Signal + Noise decomposition |
| **M4: Spectral** | Axiom | `zeta_zero_implies_eigenvalue_zero` |

### Key Files

| File | Purpose | Status |
|------|---------|--------|
| `ProofEngine.lean` | Master theorem | ✅ Sorry-free |
| `BridgeDefinitions.lean` | Concrete Hilbert space | ✅ Complete |
| `RayleighDecomposition.lean` | Signal + Noise | ✅ Complete |
| `SpectralBridge.lean` | M4 infrastructure | ✅ Complete |
| `Ergodicity.lean` | Time averages | ✅ Sorry-free |

---

## Quick Reference

### Mathlib Search Tools

```bash
# Loogle (web)
https://loogle.lean-lang.org/?q=Tendsto%20?f%20?l%20atTop

# Local grep
grep -rn "lemma_name" .lake/packages/mathlib/
```

### Proof Search Tactics

```lean
exact?   -- Find exact lemma match
apply?   -- Find applicable lemmas
aesop    -- Logic/sets/basic algebra
simp?    -- Show simp lemmas used
```

### Common Patterns

```lean
-- Finset product positivity
Finset.prod_pos + pow_pos + Nat.pos_iff_ne_zero

-- Limit combination
Tendsto.const_mul, Tendsto.sub, tendsto_finset_sum

-- Integral rewrite
MeasureTheory.setIntegral_congr_fun measurableSet_Icc
```

---

## Handoff Protocol

When finishing work:
1. Release build lock (update table above)
2. Update this file with what was done
3. Commit changes

---

*See CLAUDE.md for full documentation and API reference.*
