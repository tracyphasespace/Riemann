# Plan to Eliminate Sorries in Riemann Hypothesis Formalization

This plan outlines the specific steps to resolve the remaining `sorry`, `True`, and `axiom` placeholders in the codebase.

## 1. Foundation: Translation Operators (`Translations.lean`)

**Status:** Critical Blocker. Definition of `L2Translate` is missing.
**Current State:** Defined with `sorry` to unblock compilation.

**Action Plan:**
1.  **Locate Constructor:** Find the Mathlib 4 equivalent of `MeasureTheory.Lp.linearIsometryOfMeasurePreserving`.
    *   *Search Term:* `LinearIsometry.mk` on `Lp` types.
    *   *Alternative:* Construct `LinearMap` first using `Lp.map` and then upgrade to isometry.
2.  **Implement Definition:** Replace the `sorry` in `def L2Translate`.
3.  **Unlock Proofs:** Once defined, the proofs for `L2Translate_add`, `L2Translate_zero`, etc., should be straightforward algebraic manipulations or follow from `MeasurePreserving` properties.
4.  **Unlock Adjoint:** Use the `L2Translate_adjoint` logic from `solutions.md` (which relies on `L2Translate_add` and unitarity).

## 2. Operator Algebra (`PrimeShifts`, `TransferOperator`, `CompletionKernel`)

**Status:** Blocked by `Translations.lean`.
**Current State:** Logic is mostly correct but relies on `L2Translate`.

**Action Plan:**
1.  **Verify PrimeShifts:** Once `L2Translate` works, `PrimeShifts.lean` should be trivial (just definitions).
2.  **TransferOperator Weights:**
    *   Prove `α_modulus_critical`: Simple complex analysis ($|p^{-1/2-it}| = p^{-1/2}$).
    *   Use `Complex.abs_exp` and `Complex.log` properties.
3.  **CompletionKernel Adjoint:**
    *   This is the algebraic heart of the project.
    *   Use `L2Translate_adjoint` (from step 1).
    *   Prove `β_eq` (algebraic manipulation of weights).
    *   Combine to show `K(s)† = K(1 - conj s)`.

## 3. Measure Completion (`CompletionMeasure.lean`)

**Status:** High Risk. Relies on axioms for unitary translation.
**Current State:** 9 `sorry`s, 4 `axiom`s.

**Action Plan:**
1.  **Evaluate Necessity:** If `CompletionKernel` works, do we *need* `CompletionMeasure`? The kernel approach is simpler.
2.  **If needed:** Define the weighted measure $\mu_w$ explicitly.
3.  **Radon-Nikodym:** Prove `RN_deriv_explicit`. This requires measure theory calculus.
4.  **Unitary Correction:** Define `UTranslate` using the RN derivative square root.

## 4. Ricker Wavelets (`CompressionRicker.lean`)

**Status:** Partially Solved.
**Current State:** `rickerReal_bounded` is proven (in `solutions.md`).

**Action Plan:**
1.  **Integrate:** Copy `rickerReal_bounded` proof from `solutions.md` into `CompressionRicker.lean`.
2.  **L2 Membership:** Prove `rickerReal_memLp2`.
    *   Use Gaussian decay bounds.
    *   Show $\int (1-x^2)^2 e^{-x^2} dx < \infty$.

## 5. Trivial Cleanup (`Cl33`, `SpectralReal`)

**Status:** Low Hanging Fruit.

**Action Plan:**
1.  **Cl33 Isomorphism:** Define the map $1 \mapsto 1, i \mapsto B$ and show it preserves operations.
2.  **SpectralReal:** Use the spectral theorem for self-adjoint operators (once `CompletionKernelModel` is verified).

## Execution Order

1.  **Fix `Translations.lean`** (The Keystone).
2.  **Propagate to `PrimeShifts` & `TransferOperator`**.
3.  **Prove `CompletionKernel` Adjoint**.
4.  **Integrate Ricker proofs**.
5.  **Cleanup trivial placeholders**.
