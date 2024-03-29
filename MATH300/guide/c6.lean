import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.Basic

open BigOperators

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
    rw [Nat.add_sub_self_right]


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

-- 6.2.04 (Theorem 6.5)
 example : ∀ (n : ℕ) (hn : 1 ≤ n), Nat.factorial n <= n ^ n := by
     apply Nat.le_induction
     · norm_num
     · intro k hn h1
       rw[Nat.factorial_succ]
       have h2 : (k + 1) * Nat.factorial k <= (k + 1) * k ^ k := by
         rw[mul_le_mul_left]
         exact h1
       have h3 : (k + 1) * k ^ k < (k + 1) * (k + 1) ^ k := by
         rw[mul_le_mul_left (k+1)]
         -- exercise 6.2
       have h4 : (k + 1) * (k + 1) ^ k = (k + 1) ^ (k + 1) := by
       sorry
      sorry


-- 6.2.05 (Theorem 6.6)

--example : ∀ (n : ℕ) (hn : 1 ≤ n), (Finset.sum (Finset.range n) fun i => i) = n * (n - 1) / 2 := by
--  apply Finset.sum_range_induction

exampl (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih, Nat.succ_eq_add_one]
  ring

-- This was in the text book (Section 5.2), I think it is the same problem as therorem 6.6 from the Math 300 textbook, right?
--theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by


-- 6.2.06 (Theorem 6.7)

example (n : ℕ) : ∏ i in range n, (4 * i - 2) = (2 * n)! / n! := by
  sorry
  --induction' n with n ih

-- 6.2.07 (Theorem 6.8)
example : ∀ (n : ℕ) (hn : 1 ≤ n), n^2 - n >= 0 := by
  intro n
  rw[pow_two n]
  intro h
  linarith
