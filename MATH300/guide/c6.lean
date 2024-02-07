import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

-- Notice that in Lean ℕ starts at 0
-- While in textbook ℕ starts at 1
-- We therefore need to include an additional hypothesis
-- to indicate the starting point of our ℕ

-- 6.2.01 (Theorem 6.2) For every n ∈ ℕ, 3 | (7ⁿ − 1).
example : ∀ (n : ℕ) (hn : 1 ≤ n), 3 ∣ (7 ^ n - 1) := by
  apply Nat.le_induction
  · use 2
    norm_num
  · intro k hn h1
    rcases h1 with ⟨m, h1⟩
    use 7 * m + 2
    have h2 : 3 * (7 * m + 2) = 3 * m * 7 + 6 := by
      ring
    rw [h2, ←h1]
    have h3 : 7 ^ (k + 1) = 7 * 7 ^ k := by
      exact pow_succ 7 k
    rw[h3]
    rw [Nat.mul_sub_right_distrib, Nat.sub_eq_of_eq_add]
    rw [Nat.add_assoc]
    norm_num
    rw [Nat.sub_add_cancel]
    rw [Nat.mul_comm 7 (7 ^ k)]
    norm_num
    have h: 1 = 7^0 := by norm_num
    rw [h]
    apply Nat.pow_le_pow_of_le_right
    linarith
    linarith

-- 6.2.02 Theorem 6.3
example : ∀ (n : ℕ) (hn : 1 ≤ n), 5 ∣ (8 ^ n - 3 ^ n) := by
  apply Nat.le_induction
  · use 1
    norm_num
  · intro k hn h1
    rcases h1 with ⟨m, h1⟩
    use 8 ^ k + 3 * m
    rw[mul_add, ← mul_assoc, mul_comm 5 3]
    rw[mul_assoc, ← h1]
    have h2 : 5 * 8 ^ k + 3 * (8 ^ k - 3 ^ k) = 8 * 8 ^ k + 3 * 8 ^ k - 3 * 8 ^k -3 * 3 ^ k := by
      ring_nf
    rw[h2]
    have h3 : 8 ^ (k + 1) = 8 * 8 ^ k := by
      exact pow_succ 8 k
    rw[h3]
    have h4 : 3 ^ (k + 1) = 3 * 3 ^ k := by
      exact pow_succ 3 k
    rw[h4]
    have h5 : 3 * 8 ^ k - 3 * 8 ^k = 0 := by
    --  ring_nf
    -- rw[← sub_mul 8^k 3] -- error ??
    -- rw only works for equivalence, not implication
      norm_num



-- 6.2.03 (Theorem 6.4)
example : ∀ (n : ℕ) (hn : 1 ≤ n), 2 ^ n >= 2 * n := by
    apply Nat.le_induction
    · linarith
    · intro k hn h1
      rw[pow_succ]
      have h2 : 2 <= 2 := by
        linarith
      have h3 : 2 * 2 ^ k >= 2 * (2 * k) := by
        -- Nat.mul_le_mul h1 h2 -- why unknown tactic? i got it from moogle
        -- need a tactic to use the theorem
        exact Nat.mul_le_mul h2 h1
      have htemp : 2 * (2 * k) = 2 * k + 2 * k := by
        ring
      rw [htemp] at h3
      have h4 : 2 * k + 2 * k >= 2 * (k + 1) := by
        linarith
      exact le_trans h4 h3







-- Theorem 6.5
