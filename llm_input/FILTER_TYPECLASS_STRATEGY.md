# Filter & Type Class Strategy for Closing Sorries

**Created**: 2026-01-21
**Goal**: Close the 38 critical sorries using Mathlib's automation

---

## WORKFLOW RULE: Snippet Files

**DO NOT MODIFY SOURCE FILES DIRECTLY.**

For each file you want to change, create a snippet file:

```
Location: /home/tracy/development/Riemann/Lean/llm_input/snippets/
Naming: SNIPPET_<FileName>_<line>.lean

Example:
  Target: Riemann/ProofEngine/EnergySymmetry.lean line 163
  Create: llm_input/snippets/SNIPPET_EnergySymmetry_163.lean
```

Snippet file format:
```lean
/-!
# SNIPPET: EnergySymmetry.lean line 163
# Target: energy_deriv_zero_at_half
# Status: PROPOSED
-/

-- Paste the full theorem with your proposed proof:
theorem energy_deriv_zero_at_half (t : ℝ) :
    deriv (fun σ => ZetaEnergy t σ) (1/2) = 0 := by
  -- YOUR PROOF HERE
```

The integrator will review and apply approved snippets.

---

## Core Principle

**Stop fighting Lean. Use its automation.**

| Manual Approach (BAD) | Automated Approach (GOOD) |
|----------------------|---------------------------|
| `∀ ε > 0, ∃ δ > 0, ...` | `Tendsto f filter1 filter2` |
| Difference quotient limits | `Differentiable _ f` + type class |
| Inequality chains | `Tendsto.comp`, `Filter.Eventually` |
| Explicit derivatives | `fun_prop`, `Differentiable.comp` |

---

## 1. Filter Logic Patterns

### The Key Insight
Filters are algebraic objects representing "neighborhoods." Instead of epsilon-delta, compose filters.

### Essential Tendsto Lemmas

```lean
-- Inverse blows up at zero
tendsto_inv_nhdsGT_zero : Tendsto (·⁻¹) (𝓝[>] 0) atTop

-- Negative of atTop is atBot
tendsto_neg_atTop_atBot : Tendsto (-·) atTop atBot

-- Composition
Tendsto.comp : Tendsto g l₂ l₃ → Tendsto f l₁ l₂ → Tendsto (g ∘ f) l₁ l₃

-- Translation
tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
```

### Pattern: Pole Divergence

**Goal**: Prove `(σ - ρ)⁻¹ → +∞` as `σ → ρ⁺`

```lean
theorem pole_diverges (ρ : ℝ) :
    Tendsto (fun σ => (σ - ρ)⁻¹) (𝓝[>] ρ) atTop := by
  -- Step 1: (σ - ρ) → 0⁺ as σ → ρ⁺
  have h_sub : Tendsto (fun σ => σ - ρ) (𝓝[>] ρ) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (continuous_sub_right ρ).tendsto ρ |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_pos.mpr hσ
  -- Step 2: x⁻¹ → +∞ as x → 0⁺ (known lemma)
  -- Step 3: Compose
  exact tendsto_inv_nhdsGT_zero.comp h_sub
```

### Pattern: Squared Pole (for stiffness)

**Goal**: Prove `-(σ - ρ)⁻² → -∞` as `σ → ρ⁺`

```lean
theorem neg_inv_sq_diverges (ρ : ℝ) :
    Tendsto (fun σ => -((σ - ρ)⁻¹) ^ 2) (𝓝[>] ρ) atBot := by
  have h_inv : Tendsto (fun σ => (σ - ρ)⁻¹) (𝓝[>] ρ) atTop := pole_diverges ρ
  have h_sq : Tendsto (fun x => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have h_inv_sq : Tendsto (fun σ => ((σ - ρ)⁻¹) ^ 2) (𝓝[>] ρ) atTop := h_sq.comp h_inv
  exact tendsto_neg_atTop_atBot.comp h_inv_sq
```

### Pattern: Extract δ from Filter

When you DO need a concrete bound:

```lean
-- From Tendsto to ∀ M, ∃ δ
theorem extract_delta {f : ℝ → ℝ} {a : ℝ} (h : Tendsto f (𝓝[>] a) atTop) :
    ∀ M, ∃ δ > 0, ∀ x, a < x → x < a + δ → f x > M := by
  intro M
  rw [Metric.tendsto_nhdsWithin_nhds] at h  -- or use tendsto_atTop
  -- Extract from filter
  have := h.eventually (eventually_gt_atTop M)
  rw [Filter.eventually_nhdsWithin_iff] at this
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp this
  exact ⟨ε, hε, fun x hlo hhi => hball (by simp [Real.dist_eq]; linarith) hlo⟩
```

---

## 2. Type Class Patterns for Derivatives

### The Key Insight
Don't compute derivatives. Prove functions are differentiable, then use algebraic rules.

### Essential Type Classes

```lean
Differentiable ℝ f      -- f is differentiable everywhere
DifferentiableAt ℝ f x  -- f is differentiable at x
Continuous f            -- f is continuous
AnalyticAt ℂ f z        -- f is analytic at z (complex)
```

### The Magic Tactic: `fun_prop`

```lean
-- Automatically proves function properties by chaining instances
example : Differentiable ℝ (fun x => x^2 + Real.sin x) := by fun_prop
example : Continuous (fun x => Real.exp (x^2)) := by fun_prop
```

### Pattern: Composition Chain

```lean
theorem energy_differentiable (t : ℝ) :
    Differentiable ℝ (fun σ => ZetaEnergy t σ) := by
  unfold ZetaEnergy
  -- ZetaEnergy t σ = normSq (riemannXi (σ + t*I))
  -- Chain: normSq ∘ riemannXi ∘ (σ ↦ σ + t*I)
  apply Differentiable.comp
  · exact differentiable_normSq  -- ‖·‖² is smooth
  apply Differentiable.comp
  · sorry -- riemannXi is analytic hence differentiable
  · fun_prop  -- affine map is differentiable
```

### Pattern: Symmetric Function Has Zero Derivative at Center

```lean
theorem deriv_zero_of_symmetric {f : ℝ → ℝ}
    (h_diff : Differentiable ℝ f)
    (h_symm : ∀ x, f x = f (1 - x)) :
    deriv f (1/2) = 0 := by
  -- f(x) = f(1-x) implies f'(x) = -f'(1-x) by chain rule
  have h_deriv_symm : ∀ x, deriv f x = -deriv f (1 - x) := by
    intro x
    have := h_symm  -- differentiate both sides
    -- Use deriv_comp and chain rule
    sorry
  -- At x = 1/2: f'(1/2) = -f'(1/2), so f'(1/2) = 0
  specialize h_deriv_symm (1/2)
  simp at h_deriv_symm
  linarith
```

---

## 3. Target Sorries for Filter Approach

### HIGH VALUE (Filter logic)

| File | Line | Sorry | Approach |
|------|------|-------|----------|
| EnergySymmetry.lean | 163 | `energy_deriv_zero_at_half` | Differentiable + symmetric |
| EnergySymmetry.lean | 192 | `symmetry_and_convexity_imply_local_min` | Second derivative test |
| AnalyticAxioms.lean | 174 | `analytic_stiffness_pos_proven` | Tendsto composition |
| Ergodicity.lean | 147 | `time_average_orthogonality` | Weyl + filter |
| ClusterBound.lean | 90 | `norm_strict_min_at_half_proven` | Approximation transfer |

### MEDIUM VALUE (Type class)

| File | Line | Sorry | Approach |
|------|------|-------|----------|
| PrimeRotor.lean | 251 | `complex_sieve_symmetry` | Schwarz reflection |
| PrimeRotor.lean | 260 | `complex_sieve_deriv_at_half` | Type unification |
| CalculusAxioms.lean | 121 | `effective_convex_implies_min_proven` | MVT + type class |

---

## 4. Common Mistakes to Avoid

### DON'T: Manually unfold limits
```lean
-- BAD
intro ε hε
use δ  -- where does δ come from?
intro x hx
-- 20 lines of inequalities...
```

### DO: Use filter composition
```lean
-- GOOD
exact tendsto_inv_nhdsGT_zero.comp h_sub
```

### DON'T: Compute derivatives by definition
```lean
-- BAD
rw [deriv]
simp only [...]  -- expand difference quotient
-- painful limit calculation
```

### DO: Use type class inference
```lean
-- GOOD
have h_diff : Differentiable ℝ f := by fun_prop
exact deriv_add h_diff.differentiableAt ...
```

---

## 5. Useful Mathlib Imports

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Basic
```

---

## 6. Testing Strategy

Before attempting a sorry:

1. **Identify the mathematical statement** - What are we really proving?
2. **Find the Mathlib equivalent** - Search for existing lemmas
3. **Check type classes** - Does Lean know the functions are differentiable/continuous?
4. **Try `fun_prop` first** - Often solves derivative goals automatically
5. **Use `exact?` or `apply?`** - Let Lean search for lemmas

```lean
-- Diagnostic tactics
#check @tendsto_inv_nhdsGT_zero  -- see type signature
example : Tendsto ... := by exact?  -- search for proof
example : Differentiable ℝ f := by fun_prop  -- try automation
```

---

## Summary

The 38 critical sorries fall into patterns:

| Pattern | Count | Solution |
|---------|-------|----------|
| Limit at pole | ~8 | `Tendsto.comp` with `tendsto_inv_nhdsGT_zero` |
| Derivative exists | ~6 | `fun_prop` or `Differentiable.comp` |
| Symmetry → zero deriv | ~4 | Chain rule + `linarith` |
| Extract δ from limit | ~5 | `Metric.eventually_nhds_iff` |
| Convexity/MVT | ~6 | `StrictConvexOn`, `exists_deriv_eq_slope` |
| Other | ~9 | Case by case |

**Goal**: Close as many as possible using these patterns before resorting to `sorry`.
