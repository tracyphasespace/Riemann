# Build Errors Log

**Purpose**: Track build errors and their resolution status for AI coordination.

**Updated**: 2026-01-22

---

## Active Errors

| File:Line | Error | Tried | Status |
|-----------|-------|-------|--------|
| CalculusAxioms.lean:341 | Type mismatch HasDerivAt const_mul | const_mul swap | AI2 partial fix |
| CalculusAxioms.lean:422 | Unknown `intervalIntegrable_const.mul` | const_mul ordering | AI2 partial fix |
| CalculusAxioms.lean:426 | integral_nonpos_of_forall doesn't exist | negate & use integral_nonneg | RESOLVED (AI2) |

**Resolved (2026-01-22)**: Used negation approach - `0 ≤ ∫ (-f)` via `intervalIntegral.integral_nonneg`, then `simp [integral_neg]` + linarith

**TraceAtFirstZero.lean (2026-01-22 AI2)**:
- `product_in_corners` - PROOF RE-APPLIED (case split on signs, mul_le_mul lemmas)
- `trace_negative_at_first_zero` - CANNOT PROVE (needs native_decide)
- `trace_monotone_from_large_set` - CANNOT PROVE (needs tsum + native arithmetic)

**LinearIndependenceSolved.lean (2026-01-22 AI2)**:
- `clear_denominators` - PROOF WRITTEN (D = ∏ dens, Finset.prod_pos, Rat.num_div_den)
- `log_primes_linear_independent` - depends on FTA from DiophantineGeometry (sorry)
- `phase_space_is_torus` - depends on log_primes_linear_independent (sorry)

**ClusteringDomination.lean (2026-01-22 AI2)**:
- `weightedCosSum_replicate` - PROOF WRITTEN via `foldl_add_replicate` helper
- File is now **SORRY-FREE**

**SieveAxioms.lean (2026-01-22 AI2)**:
- `cos_sum_bounded` - PROOF WRITTEN via `foldl_abs_le_foldl` helper + `abs_cos_le_one`
- File is now **SORRY-FREE**

---

## Error Resolution History

### Template for logging errors:

```markdown
| File:Line | Error | Tried | Status |
|-----------|-------|-------|--------|
| Foo.lean:42 | unknown identifier 'bar' | exact bar | AI2 investigating |
| Foo.lean:42 | unknown identifier 'bar' | rw [baz] | RESOLVED |
```

### Status values:
- `AI1 investigating` - Builder is analyzing
- `AI2 investigating` - Scanner is researching
- `Blocked: [reason]` - Cannot proceed without external input
- `RESOLVED` - Fixed, can be archived

---

## Common Error Patterns

### 1. Unknown identifier
```
error: unknown identifier 'lemma_name'
```
**Resolution**: Use Loogle to find correct lemma name in Mathlib 4.27

### 2. Type mismatch
```
error: type mismatch
  expected: Type₁
  got: Type₂
```
**Resolution**: Check coercions, may need explicit cast or different lemma

### 3. Failed to synthesize instance
```
error: failed to synthesize instance
  SomeTypeClass SomeType
```
**Resolution**: Add instance manually or use different approach

---

## Archived (Resolved)

| Date | File:Line | Error | Resolution |
|------|-----------|-------|------------|
| (archive resolved errors here) | | | |
