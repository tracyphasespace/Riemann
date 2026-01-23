# Plan: Prove `snr_diverges_to_infinity` in InteractionTerm.lean

**STATUS: ✅ COMPLETE - 0 sorries**

---

## Summary

The theorem `snr_diverges_to_infinity` is fully proven. Added explicit hypothesis for noise being eventually nonzero.

---

## Final Theorem Signature

```lean
theorem snr_diverges_to_infinity (primes : List ℕ)
    (h_corr : PairCorrelationBound primes)
    (h_signal_grows : Tendsto (fun t => IdealEnergy primes.toFinset t) atTop atTop)
    (h_noise_nonzero : ∀ᶠ t in atTop, InteractionEnergy primes.toFinset t ≠ 0) :
    Tendsto (fun t => IdealEnergy primes.toFinset t / |InteractionEnergy primes.toFinset t|)
            atTop atTop
```

---

## Proof Structure

1. Extract α, bounds from `PairCorrelationBound`
2. Get positive constant C from `IsBigO.exists_pos`
3. Show `S^(1-α) → ∞` via `tendsto_rpow_atTop`
4. Show `(1/C) * S^(1-α) → ∞` via `Tendsto.const_mul_atTop`
5. Show `S/N ≥ (1/C) * S^(1-α)` eventually via division bounds
6. Conclude via `tendsto_atTop_mono'`

---

## Key Mathlib Lemmas Used

- `tendsto_rpow_atTop` : Power with positive exponent diverges
- `tendsto_atTop_mono'` : Eventually comparison for limits
- `IsBigO.exists_pos` : Extract positive constant from Big-O
- `IsBigOWith.bound` : Get eventual bound from IsBigOWith
- `Real.rpow_sub` : `x^(a-b) = x^a / x^b`
- `div_le_div_of_nonneg_left` : Division comparison
- `abs_pos.mpr` : `x ≠ 0 → 0 < |x|`

---

## Next Steps

- [ ] Build full project to verify no regressions
- [ ] Commit changes
- [ ] Update CLAUDE.md sorry count
