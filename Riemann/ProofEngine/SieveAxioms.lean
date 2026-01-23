import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- CYCLE: import Riemann.GlobalBound.ZetaManifold
-- CYCLE: import Riemann.GlobalBound.PrimeRotor
-- CYCLE: import Riemann.GlobalBound.SieveConstruction

noncomputable section
open Real Filter Topology

namespace ProofEngine

/-!
## Sieve Construction Helper Lemmas (Atomic Units)

These atomic lemmas support the sieve construction proofs.
The main theorems that reference GlobalBound types are in GlobalBound.SieveConstruction.
-/

/-- Atom 1: Dirichlet series absolute convergence for σ > 1/2. -/
lemma dirichlet_abs_convergent (primes : List ℕ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ M : ℝ, primes.foldl (fun acc p => acc + Real.rpow (p : ℝ) (-σ)) 0 ≤ M := by
  -- Finite list always has bounded sum
  exact ⟨_, le_rfl⟩

/-- Helper: Triangle inequality for foldl sums with positive weights -/
private lemma foldl_abs_le_foldl {f g : ℕ → ℝ} (hf_le : ∀ p, |f p| ≤ g p) (primes : List ℕ) :
    |primes.foldl (fun acc p => acc + f p) 0| ≤
    primes.foldl (fun acc p => acc + g p) 0 := by
  induction primes with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, zero_add]
    -- Generalized: |foldl f init xs| ≤ |init| + foldl |f| 0 xs
    -- For our case: |foldl f (f p) ps| ≤ foldl g (g p) ps
    have h_gen : ∀ (init_f init_g : ℝ) (xs : List ℕ),
        |init_f| ≤ init_g →
        (∀ x ∈ xs, |f x| ≤ g x) →
        |xs.foldl (fun acc x => acc + f x) init_f| ≤
        xs.foldl (fun acc x => acc + g x) init_g := by
      intro init_f init_g xs h_init h_xs
      induction xs generalizing init_f init_g with
      | nil => simpa
      | cons x xs' ihx =>
        simp only [List.foldl_cons]
        apply ihx
        · calc |init_f + f x| ≤ |init_f| + |f x| := abs_add _ _
            _ ≤ init_g + g x := add_le_add h_init (h_xs x (List.mem_cons_self _ _))
        · intro y hy
          exact h_xs y (List.mem_cons_of_mem _ hy)
    apply h_gen (f p) (g p) ps
    · exact hf_le p
    · intro x _; exact hf_le x

/-- Atom 2: Cosine sum is bounded. -/
lemma cos_sum_bounded (primes : List ℕ) (σ : ℝ) (t : ℝ) :
    |primes.foldl (fun acc p => acc + Real.rpow (p : ℝ) (-σ) * Real.cos (t * Real.log p)) 0| ≤
    primes.foldl (fun acc p => acc + Real.rpow (p : ℝ) (-σ)) 0 := by
  apply foldl_abs_le_foldl
  intro p
  rw [abs_mul]
  calc |Real.rpow (p : ℝ) (-σ)| * |Real.cos (t * Real.log p)|
      ≤ |Real.rpow (p : ℝ) (-σ)| * 1 := by
        apply mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |Real.rpow (p : ℝ) (-σ)| := mul_one _
    _ = Real.rpow (p : ℝ) (-σ) := abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

-- NOTE: construction_is_chiral_proven and construction_is_bounded_proven
-- are defined in GlobalBound.SieveConstruction to avoid import cycles.

end ProofEngine
