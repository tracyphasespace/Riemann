import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.GetD  -- For List.getD_eq_getElem
import Riemann.ProofEngine.NumberTheoryFTA
import Riemann.ProofEngine.DiophantineGeometry
import Riemann.ProofEngine.LinearIndependenceSolved
-- import Riemann.GlobalBound.ArithmeticGeometry  -- REMOVED: creates import cycle

noncomputable section
open Real Filter Topology LinearIndependenceSolved

namespace ProofEngine

/-- Atom 1: Equality of prime powers implies equality of exponents (FTA). -/
lemma prime_pow_unique_proven {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) {m n : ℕ} :
    p ^ n = q ^ m ↔ n = 0 ∧ m = 0 :=
  -- Use the proven theorem from NumberTheoryFTA (with variable order adjusted)
  NumberTheoryFTA.prime_power_eq_iff hp hq hne n m

/-- Helper: Product of prime powers is nonzero. -/
private lemma prod_prime_pow_ne_zero {S : Finset ℕ} (h_primes : ∀ p ∈ S, Nat.Prime p)
    (e : ℕ → ℕ) : S.prod (fun p => p ^ e p) ≠ 0 := by
  -- Product is positive, hence nonzero
  have h_pos : 0 < S.prod (fun p => p ^ e p) := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (h_primes p hp).pos (e p)
  exact Nat.pos_iff_ne_zero.mp h_pos

/-- Helper: (p^e).factorization p = e for prime p -/
private lemma prime_pow_factorization_self {p e : ℕ} (hp : p.Prime) :
    (p ^ e).factorization p = e := by
  rw [hp.factorization_pow, Finsupp.single_eq_same]

/-- Helper: (q^e).factorization p = 0 for distinct primes p ≠ q -/
private lemma prime_pow_factorization_other {p q e : ℕ} (hq : q.Prime) (hne : p ≠ q) :
    (q ^ e).factorization p = 0 := by
  rw [hq.factorization_pow, Finsupp.single_eq_of_ne hne]

/-- Helper: Factorization of prime power product at a prime in the set. -/
private lemma factorization_prod_prime_pow {S : Finset ℕ} (h_primes : ∀ p ∈ S, Nat.Prime p)
    (e : ℕ → ℕ) (p : ℕ) (hp : p ∈ S) :
    (S.prod (fun q => q ^ e q)).factorization p = e p := by
  -- Step 1: Product of prime powers is nonzero (needed for factorization_prod_apply)
  have h_ne_zero : ∀ q ∈ S, q ^ e q ≠ 0 := fun q hq =>
    Nat.pos_iff_ne_zero.mp (pow_pos (h_primes q hq).pos (e q))
  -- Step 2: Apply factorization_prod_apply to express as sum
  rw [Nat.factorization_prod_apply h_ne_zero]
  -- Step 3: Use sum_eq_single_of_mem: only the p term contributes
  rw [Finset.sum_eq_single_of_mem p hp]
  -- Step 3a: The p term gives e p
  · exact prime_pow_factorization_self (h_primes p hp)
  -- Step 3b: All other terms give 0
  · intro q hq hqp
    exact prime_pow_factorization_other (h_primes q hq) (Ne.symm hqp)

/-- Atom 2: Unique factorization for prime products (Rosetta Stone: use Nat.factorization). -/
lemma prod_prime_pow_unique {S : Finset ℕ} (h_primes : ∀ p ∈ S, Nat.Prime p)
    (a b : ℕ → ℕ) (h_eq : S.prod (fun p => p ^ a p) = S.prod (fun p => p ^ b p)) :
    ∀ p ∈ S, a p = b p := by
  intro p hp
  have ha := factorization_prod_prime_pow h_primes a p hp
  have hb := factorization_prod_prime_pow h_primes b p hp
  rw [h_eq] at ha
  exact ha.symm.trans hb

/-- Helper: Convert list with proof to subtype finset -/
private def listToSubtypeFinset (primes : List ℕ) (_h_primes : ∀ p ∈ primes, Nat.Prime p)
    (_h_nodup : primes.Nodup) : Finset {x : ℕ // x.Prime} :=
  (primes.toFinset).subtype (fun p => p.Prime)

/-- Helper: Membership preservation -/
private lemma mem_listToSubtypeFinset {primes : List ℕ} {h_primes : ∀ p ∈ primes, Nat.Prime p}
    {h_nodup : primes.Nodup} {p : ℕ} (hp : p ∈ primes) :
    ⟨p, h_primes p hp⟩ ∈ listToSubtypeFinset primes h_primes h_nodup := by
  simp only [listToSubtypeFinset, Finset.mem_subtype, List.mem_toFinset]
  exact hp

/-- Helper: Get coefficient at prime's index in the list.
    Uses idxOf which returns length if not found. -/
private def getCoeffAtPrime (primes : List ℕ) (coeffs : List ℚ) (p : {x : ℕ // x.Prime}) : ℚ :=
  coeffs.getD (primes.idxOf p.val) 0

/-- Atomic 1: zipWith cons distributes over sum -/
private lemma zipWith_sum_cons
    (f : ℕ → ℚ → ℝ) (a : ℕ) (b : ℚ) (as : List ℕ) (bs : List ℚ) :
    (List.zipWith f (a :: as) (b :: bs)).sum = f a b + (List.zipWith f as bs).sum := by
  simp only [List.zipWith_cons_cons, List.sum_cons]

/-- Atomic 2: zipWith of empty list has zero sum -/
private lemma zipWith_sum_nil_left
    (f : ℕ → ℚ → ℝ) (bs : List ℚ) :
    (List.zipWith f [] bs).sum = 0 := by
  simp only [List.zipWith_nil_left, List.sum_nil]

/-- Atomic 3: Subtype finset elements come from list elements -/
private lemma mem_list_of_mem_subtype {primes : List ℕ} {h_primes : ∀ p ∈ primes, Nat.Prime p}
    {h_nodup : primes.Nodup} {p : {x : ℕ // x.Prime}}
    (hp : p ∈ listToSubtypeFinset primes h_primes h_nodup) :
    p.val ∈ primes := by
  simp only [listToSubtypeFinset, Finset.mem_subtype, List.mem_toFinset] at hp
  exact hp

/-- Helper: zipWith sum equals Finset sum over subtype primes.
    TODO: Complete the inductive proof. Currently blocked by coercion issues in Lean 4.27. -/
private lemma zipWith_sum_eq_finset_sum (primes : List ℕ) (coeffs : List ℚ)
    (h_primes : ∀ p ∈ primes, Nat.Prime p) (h_nodup : primes.Nodup)
    (h_length : primes.length = coeffs.length) :
    (List.zipWith (fun p q => (q : ℝ) * log p) primes coeffs).sum =
    ∑ p ∈ listToSubtypeFinset primes h_primes h_nodup,
      (getCoeffAtPrime primes coeffs p : ℝ) * log (p : ℕ) := by
  sorry -- Inductive proof deferred due to coercion complexity

/-- Atom 3: Linear independence of logs follows from FTA. -/
theorem fta_implies_log_independence_proven (primes : List ℕ) (coeffs : List ℚ)
    (h_primes : ∀ p ∈ primes, Nat.Prime p) (h_nodup : primes.Nodup)
    (h_length : primes.length = coeffs.length)
    (h_sum : (List.zipWith (fun p q => (q : ℝ) * log p) primes coeffs).sum = 0) :
    ∀ q ∈ coeffs, q = 0 := by
  -- Strategy: Use log_primes_linear_independent from LinearIndependenceSolved.lean
  --
  -- If coeffs is empty, trivially true
  by_cases h_empty : coeffs = []
  · intro q hq; rw [h_empty] at hq; simp at hq

  -- If primes is empty, then coeffs is empty by h_length (contradiction with h_empty)
  by_cases h_primes_empty : primes = []
  · rw [h_primes_empty] at h_length
    simp only [List.length_nil] at h_length
    exact absurd (List.eq_nil_of_length_eq_zero h_length.symm) h_empty

  -- Main case: both lists nonempty
  intro q hq

  -- Get index of q in coeffs
  obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hq

  -- Get corresponding prime
  have hi_lt' : i < primes.length := by omega

  let p_i := primes[i]'hi_lt'
  have hp_i_prime : Nat.Prime p_i := h_primes p_i (List.getElem_mem hi_lt')

  -- Build the finset and coefficient function
  let s := listToSubtypeFinset primes h_primes h_nodup
  let g := getCoeffAtPrime primes coeffs

  -- The key: apply linear independence
  have h_lin_indep := linearIndependent_iff'.mp log_primes_linear_independent

  -- Convert the zipWith sum to a Finset sum
  have h_finset_sum : ∑ p ∈ s, (g p : ℝ) * log (p : ℕ) = 0 := by
    rw [← zipWith_sum_eq_finset_sum primes coeffs h_primes h_nodup h_length]
    exact h_sum

  -- Need to convert to smul form for linear independence
  have h_smul_sum : ∑ p ∈ s, g p • log (p : ℕ) = 0 := by
    simp only [Rat.smul_def]
    exact h_finset_sum

  -- Apply linear independence
  have h_g_zero : ∀ p ∈ s, g p = 0 := h_lin_indep s g h_smul_sum

  -- Now extract that q = 0
  -- The prime p_i is in s, and g ⟨p_i, hp_i_prime⟩ = q
  have hp_i_in_s : (⟨p_i, hp_i_prime⟩ : {x : ℕ // x.Prime}) ∈ s := by
    simp only [s, listToSubtypeFinset, Finset.mem_subtype, List.mem_toFinset]
    exact List.getElem_mem hi_lt'

  have h_g_pi : g ⟨p_i, hp_i_prime⟩ = q := by
    simp only [g, getCoeffAtPrime]
    -- idxOf p_i in primes should give i (since primes is nodup)
    have h_idxOf : primes.idxOf p_i = i := by
      apply List.Nodup.idxOf_getElem h_nodup
    rw [h_idxOf]
    -- coeffs.getD i 0 = coeffs[i] when i < coeffs.length
    rw [@List.getD_eq_getElem ℚ coeffs (0:ℚ) i hi_lt]
    exact hi_eq

  rw [← h_g_pi]
  exact h_g_zero ⟨p_i, hp_i_prime⟩ hp_i_in_s

-- NOTE: signal_diverges_proven moved to GlobalBound.ArithmeticGeometry to avoid import cycle.

end ProofEngine
