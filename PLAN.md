# Plan: Prove `complex_sieve_symmetry`

**RESTART CHECKPOINT**: If stuck for >3 attempts on any step, STOP and re-read this plan.

---

## Problem Statement

```lean
lemma complex_sieve_symmetry (σ t : ℝ) :
    ‖ComplexSieveCurve σ t‖ = ‖ComplexSieveCurve (1 - σ) t‖
```

Where:
```lean
def ComplexSieveCurve (σ : ℝ) (t : ℝ) : ℂ :=
  riemannXi (σ + t * I)
```

## Root Cause Analysis

After `simp only [ComplexSieveCurve]`, the goal becomes:
```
‖riemannXi (↑σ + ↑t * I)‖ = ‖riemannXi (↑(1 - σ) + ↑t * I)‖
```

**KEY INSIGHT**: The RHS has `↑(1 - σ)` (coercion of subtraction) which is **syntactically different** from `(1 : ℂ) - ↑σ` even though they're propositionally equal via `Complex.ofReal_sub`.

---

## Strategy: Work Backwards from Goal Form

Instead of fighting the coercion, **express the calc chain in the SAME form as the goal**.

The goal RHS is: `riemannXi (↑(1 - σ) + ↑t * I)`

So our atomic lemma should be:
```lean
(1 : ℂ) - (↑σ + ↑t * I) = starRingEnd ℂ (↑(1 - σ) + ↑t * I)
```

NOT:
```lean
(1 : ℂ) - (↑σ + ↑t * I) = starRingEnd ℂ ((1 - σ : ℂ) + ↑t * I)  -- WRONG: becomes 1 - ↑σ
```

---

## Atomic Lemmas (in order)

### Step 1: Verify Cast Shim Exists
```lean
#check Complex.ofReal_sub  -- ↑(r - s) = ↑r - ↑s
```
**Action**: Verify API exists ✓ (already done)

### Step 2: Atomic Lemma - Conjugate with Explicit Cast
```lean
private lemma conj_explicit (σ t : ℝ) :
    (1 : ℂ) - (↑σ + ↑t * I) = starRingEnd ℂ (↑(1 - σ) + ↑t * I) := by
  -- Use Complex.ofReal_sub to unify casts, then Complex.ext
  rw [Complex.ofReal_sub, Complex.ofReal_one]  -- now both sides have 1 - ↑σ
  rw [starRingEnd_apply]
  apply Complex.ext <;> simp [...]
```

**Test with aesop first**, then manual if needed.

### Step 3: Main Lemma Using Explicit Form
```lean
lemma complex_sieve_symmetry (σ t : ℝ) :
    ‖ComplexSieveCurve σ t‖ = ‖ComplexSieveCurve (1 - σ) t‖ := by
  simp only [ComplexSieveCurve]
  -- Goal: ‖riemannXi (↑σ + ↑t * I)‖ = ‖riemannXi (↑(1 - σ) + ↑t * I)‖
  calc ‖riemannXi (↑σ + ↑t * I)‖
      = ‖riemannXi (1 - (↑σ + ↑t * I))‖ := by rw [riemannXi_symmetric]
    _ = ‖riemannXi (starRingEnd ℂ (↑(1 - σ) + ↑t * I))‖ := by rw [conj_explicit]
    _ = ‖starRingEnd ℂ (riemannXi (↑(1 - σ) + ↑t * I))‖ := by rw [riemannXi_conj]
    _ = ‖riemannXi (↑(1 - σ) + ↑t * I)‖ := norm_conj _
```

---

## Checkpoint Protocol

After EACH step:
1. ✅ Run `lake env lean --stdin` test
2. ✅ If fails, check error message
3. ✅ If >3 attempts fail, STOP and re-read this plan
4. ✅ Update status below

---

## Status Tracker

| Step | Status | Attempts | Notes |
|------|--------|----------|-------|
| 1. API verify | ✅ DONE | 1 | ofReal_sub, norm_conj exist |
| 2. Atomic lemma | ✅ DONE | 2 | Cast shim + Complex.ext worked |
| 3. Main lemma | ✅ DONE | 2 | Full calc chain verified |
| 4. Apply to file | ✅ DONE | 1 | PrimeRotor.lean compiles |

## SUCCESS! `complex_sieve_symmetry` PROVEN

**Key insight**: Use `↑(1 - σ)` form (not `((1-σ) : ℂ)`) to match goal form after unfold.
**Cast shim**: `Complex.ofReal_sub` + `Complex.ofReal_one` aligns syntactic forms.
**Rosetta Stone**: `Complex.ext` with explicit simp lemmas for real/imag parts.

---

## Tools to Use (in order)

1. **Loogle/grep**: Find exact API signatures
2. **aesop**: Try automated proof first
3. **Complex.ext**: Rosetta Stone for ℂ arithmetic
4. **simp with explicit lemmas**: Avoid bare `simp`
5. **Cast shim**: `ofReal_sub.symm` to align forms

---

## Next Action

**EXECUTE STEP 2**: Test atomic lemma with explicit `↑(1 - σ)` form.
