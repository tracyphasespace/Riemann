# Swarm Agent Task Distribution
**Generated:** 2026-01-21

Each task below is a self-contained unit of work. Agents should claim ONE task and complete it fully before taking another.

---

## HIGH PRIORITY: Core Bridge Obligations

### Job 2: Rayleigh Identity (AnalyticBridge.lean:235)
**File:** `AnalyticBridge.lean`
**Lines:** 219-235
**Status:** ✅ COMPLETE - Agent #003 (output in llm_input/agent003_job2.lean)
```lean
theorem rayleigh_identity (s : ℂ) (v : GlobalHilbertSpace) :
    ∃ (chiralEnergy : ℝ), (innerProd v (K_op s v)).im = chiralEnergy := by
  exact ⟨(innerProd v (K_op s v)).im, rfl⟩

theorem rayleigh_decomposition (s : ℂ) (v : GlobalHilbertSpace) :
    (innerProd v (K_op s v)).im =
    v.support.sum fun p => (coeff s p).re * Q_local (v p) / 2 := by
  sorry  -- NEEDS PROOF
```
**Goal:** Prove chiral energy decomposes as weighted sum of local charges.
**Hint:** Expand innerProd, use localBivector_skew_hermitian, then localInner_bivector_eq_charge.

---

### Job 3: Zero-Kernel Bridge (CliffordZetaMasterKey.lean:182-211)
**File:** `CliffordZetaMasterKey.lean`
**Lines:** 182-211
**Status:** ✅ COMPLETE - Agent #004 (output in llm_input/agent004_job3.lean)
```lean
axiom zero_iff_kernel (s : ℂ) (hs : InCriticalStrip s) :
    riemannZeta s = 0 ↔ ∃ v : GlobalHilbertSpace, v ≠ 0 ∧ K_op s v = 0
```
**Goal:** Replace axiom with theorem using determinant ↔ kernel equivalence.
**Hint:** Define finite truncation K_N(s), prove det(K_N) = F_N(s), use Matrix.exists_mulVec_eq_zero_iff.

---

### Job 4: Chirality Final Assembly (ChiralPath.lean:376)
**File:** `ChiralPath.lean`
**Lines:** 368-376
**Status:** ✅ COMPLETE - Agent #006 (output in llm_input/agent006_job4.lean)
```lean
theorem is_chiral_proven (σ : ℝ) (hσ : σ = 1/2) : IsChiral σ := by
  sorry  -- NEEDS: Infinite sum limit + trajectory_avoids_zero
```
**Goal:** Prove IsChiral at σ = 1/2 using infinite sum convergence.
**Hint:** Use trajectory_avoids_zero for finite bounds, then dominated convergence.

---

## MEDIUM PRIORITY: Analysis Infrastructure

### Job 5: Bivector Lemmas (AnalyticBridge.lean:133,166,201,207)
**File:** `AnalyticBridge.lean`
**Status:** ✅ COMPLETE - Agent #005 (output in llm_input/agent005_job5.lean)
```lean
lemma coeff_real_of_real (σ : ℝ) (p : Primes) : (coeff σ p).im = 0 := by sorry
lemma innerProd_conj_symm (u v : GlobalHilbertSpace) : innerProd u v = conj (innerProd v u) := by sorry
lemma localInner_bivector_imaginary (v : LocalSpace) : (localInner v (localBivector v)).re = 0 := by sorry
lemma localInner_bivector_eq_charge (v : LocalSpace) : (localInner v (localBivector v)).im = Q_local v / 2 := by sorry
```
**Goal:** Prove 4 technical lemmas about bivector inner products.

---

### Job 6: Residues Pole Domination (Residues.lean:160,163,196,247)
**File:** `Residues.lean`
**Status:** ✅ COMPLETE - Agent #002 (output in llm_input/agent002_job6.lean)
```lean
-- Line 160: Continuity of derivative of holomorphic function
-- Line 163: Derivative of pole + holomorphic
-- Line 196: Pole domination arithmetic
-- Line 247: Filter intersection and δ extraction
```
**Goal:** Complete 4 technical limit/filter proofs.
**Hint:** Use tendsto_inv_nhdsGT_zero, Filter.Eventually, metric ball extraction.

---

### Job 7: Convexity (Convexity.lean:111)
**File:** `Convexity.lean`
**Status:** OPEN
```lean
theorem energy_convex_at_half (t : ℝ) (ht : 1 ≤ |t|) :
    ∃ c > 0, ∀ σ near 1/2, second_deriv (energy σ t) ≥ c := by
  sorry
```
**Goal:** Prove energy convexity via functional equation.
**Hint:** Use completedRiemannZeta₀ symmetry + second derivative analysis.

---

## LOW PRIORITY: Technical Axioms

### Job 8: Arithmetic Axioms (ArithmeticAxioms.lean)
**File:** `ArithmeticAxioms.lean`
**Lines:** 21, 30, 39
**Status:** OPEN
- Basic arithmetic lemmas for prime computations

### Job 9: Calculus Axioms (CalculusAxioms.lean)
**File:** `CalculusAxioms.lean`
**Lines:** 19, 43
**Status:** OPEN
- Derivative and continuity lemmas

### Job 10: Trace Bounds (TraceAtFirstZero.lean)
**File:** `TraceAtFirstZero.lean`
**Lines:** 87, 89, 147, 160
**Status:** OPEN
- Interval arithmetic bounds for first zero

### Job 11: Clifford Axioms (CliffordAxioms.lean)
**File:** `CliffordAxioms.lean`
**Lines:** 39, 45
**Status:** OPEN
- Clifford algebra structure lemmas

### Job 12: Clustering (ClusteringDomination.lean:96)
**File:** `ClusteringDomination.lean`
**Status:** OPEN
- Connect pole domination to phase clustering

---

## COMPLETED JOBS

| Job | Agent | File | Status |
|-----|-------|------|--------|
| Job 1: FTA Linear Independence | Swarm #001 | DiophantineGeometry.lean | ✅ DONE |
| Job 2: Rayleigh Identity | Swarm #003 | llm_input/agent003_job2.lean | ✅ DONE |
| Job 3: Zero-Kernel Bridge | Swarm #004 | llm_input/agent004_job3.lean | ✅ DONE |
| Job 4: Chirality Assembly | Swarm #006 | llm_input/agent006_job4.lean | ✅ DONE |
| Job 5: Bivector Lemmas | Swarm #005 | llm_input/agent005_job5.lean | ✅ DONE |
| Job 6: Residues Pole Domination | Swarm #002 | llm_input/agent002_job6.lean | ✅ DONE |

---

## CLAIMING A JOB

When you start a job, update this file:
```
### Job N: [Name]
**Status:** IN PROGRESS - Agent #XXX
```

When complete:
```
### Job N: [Name]
**Status:** ✅ COMPLETE - Agent #XXX
```

---

## OUTPUT FORMAT

For each job, provide:
1. The complete Lean proof (no sorry)
2. Any helper lemmas needed
3. Import statements if new ones required
4. Brief explanation of proof strategy

---

## 🔑 CRITICAL: Lean/Mathlib Proof Strategy (The "Rosetta Stone")

**This advice cures "Lean pain"** - the friction between how mathematicians think (epsilon-delta) and how Lean automates (filters, type classes).

### Filter Logic: "Escape the Epsilon Trap"

**Problem:** Manual ε-δ proofs are "assembly code" - Lean can't automate them.

**Solution:** Use `Filter.Tendsto` - filters are algebraic objects for "neighborhoods."

```lean
-- ONE LINE instead of 50 lines of epsilon-delta:
lemma inverse_blows_up : Tendsto (fun x => x⁻¹) (𝓝[>] 0) atTop :=
  tendsto_inv_nhdsGT_zero
```

**For Pole Domination (Residues.lean, Job 6):**
Chain known limits with `Tendsto.comp`:
- `(s-ρ) → 0` (Linear continuity)
- `x → x²` (Power continuity)
- `x → -1/x` (Inverse limits)
- Therefore `-(s-ρ)⁻² → -∞` in 5 lines, not 50.

### Complex Derivatives: "Let Type Classes Do the Calculus"

**Problem:** Proving `lim_{h→0} (f(z+h)-f(z))/h` manually is painful.

**Solution:** Use Type Classes (`Differentiable`, `AnalyticAt`, `HolomorphicOn`).

```lean
-- Lean auto-deduces composition is smooth:
have h1 : Differentiable ℂ (fun t => t * log p) := ...
have h2 : Differentiable ℂ cexp := ...
exact h2.comp h1
```

Use `fun_prop` tactic or `Differentiable.add`, `Differentiable.mul`, `Differentiable.comp`.

### Refactoring Rules for Agents

| If You See... | Action |
|---------------|--------|
| `∀ ε > 0, ∃ δ > 0` | DELETE. Use `Tendsto` lemma |
| Difference quotient | DELETE. Use `Differentiable.comp` |
| Manual HolomorphicOn proof | Use type class inference |

**This is how we close the remaining sorries efficiently - algebraic reasoning, not epsilon-delta grinding.**
