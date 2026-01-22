# Swarm Agent Briefing

**READ THIS FIRST BEFORE ANY TASK**

---

## Environment

| Component | Version |
|-----------|---------|
| **Lean** | 4.27.0-rc1 |
| **Mathlib** | v4.27.0-rc1 |
| **Build Command** | `lake build` (AI1 runs this, NOT you) |

---

## Critical API Rules (Lean 4.27 / Mathlib 4.27)

### Complex Numbers
```lean
-- USE: ‖·‖ (norm), NOT Complex.abs
Complex.norm_cpow_eq_rpow_re_of_pos  -- ‖p^(-s)‖ = p^(-s.re)

-- Complex field access
s.re  -- real part
s.im  -- imaginary part
```

### Filters & Limits
```lean
-- Deleted neighborhood (punctured)
𝓝[≠] ρ           -- nhdsWithin at ρ, excluding ρ

-- Right neighborhood
𝓝[>] x           -- nhdsWithin (Ioi x)

-- Key limit lemmas
tendsto_inv_nhdsGT_zero      -- 1/x → +∞ as x → 0⁺
tendsto_neg_atTop_atBot      -- -y → -∞ as y → +∞
Metric.eventually_nhdsWithin_iff  -- extract δ from filter

-- Filter pattern
filter_upwards [self_mem_nhdsWithin] with σ hσ
```

### Derivatives
```lean
DifferentiableOn.deriv       -- derivative of differentiable function
deriv_add                    -- d/dx(f + g) = f' + g'
deriv_inv_sub_const          -- d/dx(x - c)⁻¹ = -(x-c)⁻²
```

### Summability
```lean
Real.summable_nat_rpow       -- Σ n^(-x) converges iff x > 1
Summable.of_norm_bounded_eventually
```

### Matrices
```lean
Matrix.det_eq_zero_iff_exists_mulVec_eq_zero
Matrix.det_blockDiagonal
```

### Finsets & Sums
```lean
Finset.sum_congr             -- rewrite sums
Finset.prod_congr            -- rewrite products
Complex.im_sum               -- Im(Σ) = Σ Im
```

---

## Workflow Rules

1. **DO NOT run `lake build`** - AI1 handles builds
2. **Break sorries into helper lemmas** - smaller proofs are easier to fix
3. **Search Mathlib first** - use existing lemmas, don't reinvent
4. **Output pure Lean 4 code** - minimize prose, maximize code
5. **Use exact API names** - no guessing at lemma names

---

## Output Format

```lean
/-!
# SWARM AGENT #XXX - JOB N: [Job Name]
Lean 4.27.0-rc1 / Mathlib v4.27.0-rc1
-/

import Mathlib.[relevant imports]

-- Helper lemmas first
lemma helper1 ... := by
  [proof]

lemma helper2 ... := by
  [proof]

-- Main theorem
theorem main_result ... := by
  [proof using helpers]
```

---

## Common Mistakes to Avoid

| Wrong (old API) | Right (4.27) |
|-----------------|--------------|
| `Complex.abs z` | `‖z‖` or `Complex.abs z` (both work) |
| `nat.prime` | `Nat.Prime` |
| `finset.sum` | `Finset.sum` |
| `has_deriv_at` | `HasDerivAt` |
| `tendsto_nhds_within` | `Tendsto ... (𝓝[s] x)` |

---

## File Delivery

Output goes to: `llm_input/agentXXX_jobN.lean`

AI1 will:
1. Review your output
2. Run `lake build`
3. Fix any API mismatches
4. Integrate into target file

---

## 🔑 CRITICAL: Lean/Mathlib Proof Strategy (The "Rosetta Stone")

**This advice cures "Lean pain"** - the friction between how mathematicians think (epsilon-delta) and how Lean automates (filters, type classes).

### Filter Logic: "Escape the Epsilon Trap"

**Problem:** Manual ε-δ proofs are "assembly code" - Lean can't automate them.

**Solution:** Use `Filter.Tendsto` - filters are algebraic objects for "neighborhoods."

```lean
-- The Hard Way (Epsilon): Struggle with Archimedean properties
-- The Lean Way (Filters): ONE LINE
lemma inverse_blows_up : Tendsto (fun x => x⁻¹) (𝓝[>] 0) atTop :=
  tendsto_inv_nhdsGT_zero
```

**For Pole Domination Proofs:**
DON'T find δ where function exceeds M. DO chain limits with `Tendsto.comp`:
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

Key tactics: `fun_prop`, `Differentiable.add`, `Differentiable.mul`, `Differentiable.comp`

### Refactoring Rules

| If You See... | Action |
|---------------|--------|
| `∀ ε > 0, ∃ δ > 0` | DELETE. Use `Tendsto` lemma |
| Difference quotient | DELETE. Use `Differentiable.comp` |
| Manual HolomorphicOn | Use type class inference |

**This is how we close sorries efficiently - algebraic reasoning over epsilon-delta grinding.**
