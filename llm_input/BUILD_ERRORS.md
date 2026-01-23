# Build Errors Log

**Purpose**: Track build errors and their resolution status for AI coordination.

**Updated**: 2026-01-22

---

## Active Errors

| File:Line | Error | Tried | Status |
|-----------|-------|-------|--------|
| (none currently) | | | |

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
