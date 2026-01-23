# Plan: Prove `snr_diverges_to_infinity` in InteractionTerm.lean

**RESTART CHECKPOINT**: If stuck for >3 attempts on any step, STOP and re-read this plan.

---

## Problem Statement

```lean
theorem snr_diverges_to_infinity (primes : List ℕ)
    (h_corr : PairCorrelationBound primes)
    (_h_signal_grows : Tendsto (fun t => IdealEnergy primes.toFinset t) atTop atTop) :
    Tendsto (fun t => IdealEnergy primes.toFinset t / |InteractionEnergy primes.toFinset t|)
            atTop atTop
```

Where:
```lean
structure PairCorrelationBound (primes : List ℕ) : Prop where
  α : ℝ
  hα_lt : α < 1
  h_bound : ∀ t, |InteractionEnergy primes.toFinset t| ≤ (IdealEnergy primes.toFinset t) ^ α
```

## Mathematical Content

Given:
- Signal S(t) = IdealEnergy → ∞ as t → ∞
- Noise N(t) = |InteractionEnergy| ≤ S(t)^α where α < 1

Prove: S(t)/N(t) → ∞

**Key insight**: S/N ≥ S/S^α = S^(1-α) → ∞ since 1-α > 0 and S → ∞

---

## Step 1: Find Mathlib API

Need to find:
- [ ] `Tendsto.div_atTop` or similar for f/g → ∞
- [ ] `Tendsto.rpow` for S^(1-α) → ∞ when S → ∞ and 1-α > 0
- [ ] Comparison lemma: if g ≤ f and f → ∞, then f/g ≥ f/f^α

**Search patterns**:
```
Tendsto.*atTop.*atTop
rpow.*tendsto
div.*tendsto.*atTop
```

---

## Step 2: Atomic Lemmas

### Lemma A: Power with positive exponent diverges
```lean
lemma tendsto_rpow_atTop_of_pos (h : 0 < β) :
    Tendsto (fun x => x ^ β) atTop atTop
```

### Lemma B: Division lower bound
```lean
lemma div_ge_of_le_rpow (hS : 0 < S) (hN : N ≤ S ^ α) (hα : α < 1) :
    S / N ≥ S ^ (1 - α)
```

### Lemma C: Composition gives divergence
```lean
-- If S → ∞ and S^(1-α) → ∞, and S/N ≥ S^(1-α), then S/N → ∞
```

---

## Step 3: Proof Strategy

1. Extract α, hα_lt, h_bound from h_corr
2. Show 1 - α > 0 from hα_lt
3. Show S^(1-α) → ∞ using _h_signal_grows and rpow tendsto
4. Show S/N ≥ S^(1-α) using h_bound
5. Conclude S/N → ∞ by comparison

---

## Step 4: Implementation

```lean
theorem snr_diverges_to_infinity ... := by
  obtain ⟨α, hα_lt, h_bound⟩ := h_corr
  have h_exp_pos : 0 < 1 - α := by linarith
  -- S^(1-α) → ∞
  have h_power_diverges : Tendsto (fun t => (IdealEnergy primes.toFinset t) ^ (1 - α)) atTop atTop := by
    exact Tendsto.rpow_const _h_signal_grows (Or.inl h_exp_pos) -- or similar
  -- S/N ≥ S^(1-α) eventually
  have h_lower : ∀ᶠ t in atTop, IdealEnergy ... / |InteractionEnergy ...| ≥ ... ^ (1 - α) := by
    filter_upwards with t
    have hN := h_bound t
    -- division manipulation
  -- Conclude
  exact Tendsto.atTop_of_eventually_ge h_power_diverges h_lower -- or similar
```

---

## Status Tracker

| Step | Status | Attempts | Notes |
|------|--------|----------|-------|
| 1. API search | 🔄 TODO | 0 | Find Mathlib tendsto/rpow lemmas |
| 2. Atomic lemmas | 🔄 TODO | 0 | Test with aesop |
| 3. Main proof | 🔄 TODO | 0 | Combine atomics |

---

## Next Action

**EXECUTE STEP 1**: Search for Mathlib API for tendsto + rpow + division.
