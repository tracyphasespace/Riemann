# Mathlib 4.27 API Guide for Opus Agents

## CRITICAL: Common API Issues

When proofs fail with type class synthesis errors or unknown identifiers, check this guide.

### 1. Tendsto.atTop_mul_atTop - DOES NOT WORK

**Error:** `failed to synthesize instance of type class IsOrderedMonoid ℝ`

**Wrong:**
```lean
exact Tendsto.atTop_mul_atTop h_inv_tendsto h_inv_tendsto
```

**Correct alternatives:**
```lean
-- Option A: Use mul_atTop (different API)
exact h_inv_tendsto.atTop_mul h_inv_tendsto

-- Option B: Show convergence directly using Filter patterns
have : Tendsto (fun x => x^2) atTop atTop := tendsto_pow_atTop (by norm_num : 1 ≤ 2)
exact this.comp h_inv_tendsto
```

### 2. Filter.Tendsto.eventually_lt_atBot - DOES NOT EXIST

**Error:** Unknown method

**Wrong:**
```lean
have h := h_lim.eventually_lt_atBot (-E - 1)
```

**Correct:**
```lean
-- Use Filter.Tendsto.eventually with Filter.eventually_lt_atBot_iff
have h := h_lim.eventually (Filter.eventually_lt_atBot (-E - 1))
-- OR: Manually construct the eventually
have h : ∀ᶠ σ in 𝓝[>] ρ.re, f σ < -E - 1 := by
  rw [Filter.Eventually]
  exact h_lim.preimage_mem_nhds (Iio_mem_atBot _)
```

### 3. Metric.nhdsWithin_le_nhds - DOES NOT EXIST

**Error:** Unknown identifier

**Wrong:**
```lean
filter_upwards [Metric.nhdsWithin_le_nhds (Metric.ball_mem_nhds ρ.re hδ_pos)]
```

**Correct:**
```lean
-- Use nhdsWithin_le_nhds directly (no Metric prefix)
filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds ρ.re hδ_pos)]
```

### 4. Preorder ℂ - DOES NOT EXIST

**Error:** `failed to synthesize instance of type class Preorder ℂ`

Complex numbers are NOT ordered. When working with inequalities:

**Wrong:**
```lean
-- Trying to use < on ℂ directly
have : s < ρ := ...
```

**Correct:**
```lean
-- Work with the .re projection on ℝ
have : s.re < ρ.re := ...

-- For eventually statements, ensure the filter is on ℝ
have h : ∀ᶠ σ in 𝓝[>] ρ.re, (f ((σ : ℂ) + ρ.im * I)).re < M := ...
```

### 5. zpow Rewrites

**Error:** Rewrite patterns don't match

**Wrong:**
```lean
rw [zpow_neg, zpow_natCast]  -- Pattern mismatch
```

**Correct:**
```lean
-- Be explicit about types and use simp with lemmas
simp only [zpow_neg, zpow_natCast, ofReal_pow]
-- OR use norm_cast
norm_cast
-- OR do explicit conversions
have h : (↑x : ℂ) ^ (-2 : ℤ) = ((x^2)⁻¹ : ℂ) := by
  rw [zpow_neg, zpow_natCast, inv_eq_one_div]
```

### 6. Filter.Eventually.and Type Inference

**Error:** `σ has type ℂ but expected ℝ`

When combining eventually statements, ensure both are on the same filter:

**Wrong:**
```lean
have h_both := h1.and h2  -- May infer wrong type for σ
```

**Correct:**
```lean
-- Be explicit about the filter variable type
have h_both : ∀ᶠ (σ : ℝ) in 𝓝[>] ρ.re, P σ ∧ Q σ := h1.and h2
```

### 7. HasDerivAt with ℝ → ℂ Functions

**Error:** Type mismatch in HasDerivAt

When differentiating functions ℝ → ℂ:

**Correct pattern:**
```lean
-- Use ofRealCLM for the coercion derivative
have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt

-- For constants
have h2 : HasDerivAt (fun _ : ℝ => c) 0 σ := hasDerivAt_const σ c

-- Combine with add
have h3 := h1.add h2
```

### 8. Set.mem_Ioi Conversion

**Error:** Type mismatch with `sub_pos.mpr`

When working with nhdsWithin Ioi:

**Wrong:**
```lean
filter_upwards [self_mem_nhdsWithin] with σ hσ
exact sub_pos.mpr hσ  -- hσ : σ ∈ Ioi ρ.re, not σ > ρ.re
```

**Correct:**
```lean
filter_upwards [self_mem_nhdsWithin] with σ hσ
simp only [Set.mem_Ioi] at hσ  -- Now hσ : ρ.re < σ
exact sub_pos.mpr hσ
```

### 9. abs_re_le_abs for Complex

**Error:** Application type mismatch

```lean
-- Wrong: abs_re_le_abs takes one argument
linarith [abs_re_le_abs (h' z - h' ρ)]

-- Correct: Use Complex.abs_re_le_abs
linarith [Complex.abs_re_le_abs (h' z - h' ρ)]
```

### 10. List.foldl_cons Simplification

**Error:** `simp made no progress`

```lean
-- Wrong
simp only [List.foldl]

-- Correct
simp only [List.foldl_cons]
-- OR
simp_all only [List.foldl_cons]
```

## Testing Pattern

When writing proofs for Mathlib 4.27, follow this pattern:

1. **Write small, testable helper lemmas** - Don't write 50-line proofs
2. **Use `sorry` strategically** - Mark API-blocked steps with `-- TIER6_RESUBMIT: reason`
3. **Document the strategy** - Even if the proof fails, the approach should be clear
4. **Check type classes** - Use `#check` and `#print` to verify lemma signatures

## Example: Correct Tendsto Pattern

```lean
theorem stiffness_tendsto (ρ : ℂ) (h : some_hypothesis) :
    Tendsto (fun σ : ℝ => f σ) (𝓝[>] ρ.re) atBot := by
  -- Step 1: Get component lemmas
  have h_sub : Tendsto (fun σ => σ - ρ.re) (𝓝[>] ρ.re) (𝓝[>] 0) := by
    have h1 : Tendsto (fun σ => σ - ρ.re) (𝓝 ρ.re) (𝓝 0) := by
      have := continuous_sub_right ρ.re |>.tendsto ρ.re
      simp only [sub_self] at this
      exact this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h1.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_Ioi] at hσ
    exact sub_pos.mpr hσ

  -- Step 2: Compose with inverse
  have h_inv : Tendsto (fun σ => (σ - ρ.re)⁻¹) (𝓝[>] ρ.re) atTop :=
    tendsto_inv_nhdsGT_zero.comp h_sub

  -- Step 3: Square (avoiding atTop_mul_atTop)
  have h_sq : Tendsto (fun σ => (σ - ρ.re)⁻¹ ^ 2) (𝓝[>] ρ.re) atTop := by
    -- Use pow composition instead of mul
    have h_pow := tendsto_pow_atTop (by norm_num : 1 ≤ 2)
    exact h_pow.comp h_inv

  -- Step 4: Negate
  exact tendsto_neg_atTop_atBot.comp h_sq
```

---

*Generated 2026-01-21 for AI2 / Opus Agents - Mathlib 4.27.0-rc1*
