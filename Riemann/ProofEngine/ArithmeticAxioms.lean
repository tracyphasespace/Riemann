import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
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
private def listToSubtypeFinset (primes : List ℕ) (h_primes : ∀ p ∈ primes, Nat.Prime p)
    (h_nodup : primes.Nodup) : Finset {x : ℕ // x.Prime} :=
  (primes.toFinset).subtype (fun p => p.Prime)

/-- Helper: Membership preservation -/
private lemma mem_listToSubtypeFinset {primes : List ℕ} {h_primes : ∀ p ∈ primes, Nat.Prime p}
    {h_nodup : primes.Nodup} {p : ℕ} (hp : p ∈ primes) :
    ⟨p, h_primes p hp⟩ ∈ listToSubtypeFinset primes h_primes h_nodup := by
  simp only [listToSubtypeFinset, Finset.mem_subtype, List.mem_toFinset]
  exact hp

/-- Helper: Get coefficient at prime's index in the list -/
private def getCoeffAtPrime (primes : List ℕ) (coeffs : List ℚ) (p : {x : ℕ // x.Prime}) : ℚ :=
  match primes.indexOf? p.val with
  | some i => coeffs.getD i 0
  | none => 0

/-- Helper: zipWith sum equals Finset sum over subtype primes -/
private lemma zipWith_sum_eq_finset_sum (primes : List ℕ) (coeffs : List ℚ)
    (h_primes : ∀ p ∈ primes, Nat.Prime p) (h_nodup : primes.Nodup)
    (h_length : primes.length = coeffs.length) :
    (List.zipWith (fun p q => (q : ℝ) * log p) primes coeffs).sum =
    ∑ p ∈ listToSubtypeFinset primes h_primes h_nodup,
      (getCoeffAtPrime primes coeffs p : ℝ) * log (p : ℕ) := by
  -- This is a technical lemma about converting between list and finset sums
  -- The key insight: both sums range over the same primes with same coefficients
  induction primes generalizing coeffs with
  | nil =>
    simp only [List.zipWith_nil_left, List.sum_nil, listToSubtypeFinset, List.toFinset_nil,
               Finset.subtype_empty, Finset.sum_empty]
  | cons p ps ih =>
    cases coeffs with
    | nil => simp at h_length
    | cons c cs =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      -- For the tail, apply IH
      have h_primes' : ∀ q ∈ ps, Nat.Prime q := fun q hq => h_primes q (List.mem_cons_of_mem p hq)
      have h_nodup' : ps.Nodup := List.Nodup.of_cons h_nodup
      have h_length' : ps.length = cs.length := by simp only [List.length_cons] at h_length; omega
      -- TRIED: induction with Finset.sum_insert (2026-01-23)
      -- BLOCKED: listToSubtypeFinset cons expansion is complex
      --   Need: (p :: ps).toFinset.subtype = insert ⟨p, _⟩ (ps.toFinset.subtype)
      --   Then: Finset.sum_insert + show p ∉ ps.toFinset (from h_nodup)
      --   Then: getCoeffAtPrime returns c for head, apply IH for tail
      -- NEXT: Try List.sum_map_eq_finset_sum or direct equality proof
      sorry

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
    exact absurd (List.length_eq_zero.mp h_length.symm) h_empty

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
    convert h_sum using 2 with p c
    ring

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
    -- indexOf? p_i in primes should give i (since primes is nodup)
    have h_indexOf : primes.indexOf? p_i = some i := by
      rw [List.indexOf?_eq_some_iff]
      constructor
      · exact hi_lt'
      constructor
      · rfl
      · intro j hj hj_lt
        -- If primes[j] = p_i and j < i, contradiction with nodup
        have hj_eq : primes[j] = p_i := hj
        have hi_eq' : primes[i] = p_i := rfl
        -- By nodup, indices with same value must be equal
        have := List.Nodup.getElem_inj_iff h_nodup |>.mp (hj_eq.trans hi_eq'.symm)
        omega
    rw [h_indexOf]
    simp only [List.getD, hi_lt, hi_eq]
    split
    · rfl
    · omega

  rw [← h_g_pi]
  exact h_g_zero ⟨p_i, hp_i_prime⟩ hp_i_in_s

-- NOTE: signal_diverges_proven moved to GlobalBound.ArithmeticGeometry to avoid import cycle.

end ProofEngine
