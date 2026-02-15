import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational
import Riemann.ProofEngine.ArithmeticAxioms
import Riemann.ProofEngine.NumberTheoryFTA

noncomputable section
open Real Filter Topology

namespace ProofEngine

/-!
## Geometric Helper Lemmas (Atomic Units)
-/

/-- Atom 1: Two frequencies k*log(p) and j*log(q) are distinct for distinct primes. -/
lemma frequency_incommensurability {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    {k j : ℤ} (hk : k ≠ 0) (hj : j ≠ 0) :
    (k : ℝ) * log p ≠ (j : ℝ) * log q := by
  -- B3-3: Uses FTA (prime_power_eq_iff) from NumberTheoryFTA
  -- Proof strategy: k*log(p) = j*log(q) implies p^k = q^j (by log injectivity)
  -- FTA then gives contradiction since distinct primes can't have equal powers
  intro h_eq
  have h_log_p_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have h_log_q_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  rw [← Real.log_zpow, ← Real.log_zpow] at h_eq
  have hpk_pos : (0 : ℝ) < (p : ℝ) ^ (k : ℤ) := zpow_pos hp_pos k
  have hqj_pos : (0 : ℝ) < (q : ℝ) ^ (j : ℤ) := zpow_pos hq_pos j
  have h_pow_eq : (p : ℝ) ^ (k : ℤ) = (q : ℝ) ^ (j : ℤ) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hpk_pos) (Set.mem_Ioi.mpr hqj_pos) h_eq
  have h_same_sign : (0 < k ∧ 0 < j) ∨ (k < 0 ∧ j < 0) := by
    rcases lt_trichotomy k 0 with hk_neg | hk_zero | hk_pos
    · right
      constructor
      · exact hk_neg
      · have : (k : ℝ) * log p < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hk_neg) h_log_p_pos
        rw [Real.log_zpow, Real.log_zpow] at h_eq
        rw [h_eq] at this
        have : (j : ℝ) < 0 := by
          by_contra hj_nonneg
          push_neg at hj_nonneg
          have : 0 ≤ (j : ℝ) * log q :=
            mul_nonneg (by exact_mod_cast hj_nonneg) (le_of_lt h_log_q_pos)
          linarith
        exact_mod_cast this
    · exact absurd hk_zero hk
    · left
      constructor
      · exact hk_pos
      · have : (k : ℝ) * log p > 0 := mul_pos (by exact_mod_cast hk_pos) h_log_p_pos
        rw [Real.log_zpow, Real.log_zpow] at h_eq
        rw [h_eq] at this
        have : (j : ℝ) > 0 := by
          by_contra hj_nonpos
          push_neg at hj_nonpos
          have : (j : ℝ) * log q ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hj_nonpos) (le_of_lt h_log_q_pos)
          linarith
        exact_mod_cast this
  rcases h_same_sign with ⟨hk_pos, hj_pos⟩ | ⟨hk_neg, hj_neg⟩
  · -- Positive case: k > 0 and j > 0
    cases k with
    | ofNat n =>
        cases j with
        | ofNat m =>
            -- Extract Nat positivity from Int positivity using omega after simp
            have hn_pos : 0 < n := by simp only [Int.ofNat_eq_natCast] at hk_pos; omega
            have hm_pos : 0 < m := by simp only [Int.ofNat_eq_natCast] at hj_pos; omega
            have h_nat_eq : p ^ n = q ^ m := by
              have h : ((p : ℕ) : ℝ) ^ n = ((q : ℕ) : ℝ) ^ m := h_pow_eq
              exact_mod_cast h
            have h_fta := (NumberTheoryFTA.prime_power_eq_iff hp hq hne n m).mp h_nat_eq
            -- FTA gives n = 0 ∧ m = 0, contradicting hn_pos and hm_pos
            exact absurd h_fta.1 (Nat.ne_of_gt hn_pos)
        | negSucc m =>
            -- j = Int.negSucc m < 0, contradicts hj_pos : 0 < j
            exact (not_lt_of_gt hj_pos) (by simp)
    | negSucc n =>
        -- k = Int.negSucc n < 0, contradicts hk_pos : 0 < k
        exact (not_lt_of_gt hk_pos) (by simp)
  · -- Negative case: k < 0 and j < 0
    cases k with
    | ofNat n =>
        -- k = Int.ofNat n >= 0, contradicts hk_neg : k < 0
        simp only [Int.ofNat_eq_natCast] at hk_neg
        exact absurd (Int.natCast_nonneg n) (not_le.mpr hk_neg)
    | negSucc n =>
        cases j with
        | ofNat m =>
            -- j = Int.ofNat m >= 0, contradicts hj_neg : j < 0
            simp only [Int.ofNat_eq_natCast] at hj_neg
            exact absurd (Int.natCast_nonneg m) (not_le.mpr hj_neg)
        | negSucc m =>
            -- k = Int.negSucc n = -(n+1), j = Int.negSucc m = -(m+1)
            -- Both are negative integers
            let n' := n + 1
            let m' := m + 1
            have hn' : -(Int.negSucc n : ℤ) = (n' : ℤ) := by simp [Int.negSucc_eq, n']
            have hm' : -(Int.negSucc m : ℤ) = (m' : ℤ) := by simp [Int.negSucc_eq, m']
            have hn'_pos : 0 < n' := Nat.succ_pos n
            -- Invert the equation: p^(-(negSucc n)) = q^(-(negSucc m))
            have h_pow_eq' :
                (p : ℝ) ^ (-(Int.negSucc n) : ℤ) = (q : ℝ) ^ (-(Int.negSucc m) : ℤ) := by
              rw [zpow_neg, zpow_neg, h_pow_eq]
            rw [hn', hm'] at h_pow_eq'
            simp only [zpow_natCast] at h_pow_eq'
            have h_nat_eq : p ^ n' = q ^ m' := by
              have h : ((p : ℕ) : ℝ) ^ n' = ((q : ℕ) : ℝ) ^ m' := h_pow_eq'
              exact_mod_cast h
            have h_fta := (NumberTheoryFTA.prime_power_eq_iff hp hq hne n' m').mp h_nat_eq
            -- FTA gives n' = 0 ∧ m' = 0, but n' = n+1 > 0, contradiction
            exact absurd h_fta.1 (Nat.ne_of_gt hn'_pos)

/-- Atom 2: If sin(t log p) = 0 and sin(t log q) = 0, then t must be zero (or rational logs). -/
theorem energy_persistence_proven {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (t : ℝ) (ht : t ≠ 0) :
    sin (t * log p) ≠ 0 ∨ sin (t * log q) ≠ 0 := by
  -- B3-4: Uses frequency_incommensurability (B3-3)
  -- If both sin=0, then t log p = k π and t log q = j π.
  -- This implies k*log(q) = j*log(p), contradicting B3-3.
  by_contra h_both_zero
  push_neg at h_both_zero
  obtain ⟨h_sin_p, h_sin_q⟩ := h_both_zero
  -- Extract integer multiples: sin(x) = 0 ↔ ∃ k : ℤ, k * π = x
  rw [sin_eq_zero_iff] at h_sin_p h_sin_q
  obtain ⟨k, hk⟩ := h_sin_p  -- k * π = t * log p
  obtain ⟨j, hj⟩ := h_sin_q  -- j * π = t * log q
  have h_log_p_pos : 0 < log p := log_pos (by exact_mod_cast hp.one_lt)
  have h_log_q_pos : 0 < log q := log_pos (by exact_mod_cast hq.one_lt)
  -- k must be nonzero (else t * log p = 0 with t ≠ 0 and log p > 0)
  have hk_ne : k ≠ 0 := by
    intro hk_zero
    simp only [hk_zero, Int.cast_zero, zero_mul] at hk
    exact mul_ne_zero ht (ne_of_gt h_log_p_pos) hk.symm
  -- j must be nonzero (similarly)
  have hj_ne : j ≠ 0 := by
    intro hj_zero
    simp only [hj_zero, Int.cast_zero, zero_mul] at hj
    exact mul_ne_zero ht (ne_of_gt h_log_q_pos) hj.symm
  -- From k * π = t * log p and j * π = t * log q,
  -- derive k * log q = j * log p (to apply frequency_incommensurability)
  have h_eq : (k : ℝ) * log q = (j : ℝ) * log p := by
    have hpi_ne : π ≠ 0 := ne_of_gt pi_pos
    have hlogp_ne : log p ≠ 0 := ne_of_gt h_log_p_pos
    have hlogq_ne : log q ≠ 0 := ne_of_gt h_log_q_pos
    have hk_eq : t = (k : ℝ) * π / log p := by field_simp at hk ⊢; linarith
    have hj_eq : t = (j : ℝ) * π / log q := by field_simp at hj ⊢; linarith
    have heq : (k : ℝ) * π / log p = (j : ℝ) * π / log q := by rw [← hk_eq, ← hj_eq]
    field_simp [hlogp_ne, hlogq_ne, hpi_ne] at heq
    linarith
  -- This contradicts frequency_incommensurability (applied to q, p with k, j swapped)
  exact frequency_incommensurability hq hp (Ne.symm hne) hk_ne hj_ne h_eq

end ProofEngine
