import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

-- 6.1 Prove: If a is a non-negative integer,
--            then aⁿ ≥ 0 for all n ∈ N.
example {a : ℕ} : ∀ n : ℕ, a^n ≥ 0 := by
  sorry

-- 6.2 Prove: If a and b are non-negative integers
--     such that a < b, then aⁿ < bⁿ for all n ∈ ℕ.
example {a b n : ℕ} (hn : 1 ≤ n) :
        ∀ n : ℕ, n > 0 → a < b → a^n < b^n := by
  apply Nat.le_induction


-- 6.3 Let n be a positive integer.
--     Use induction to prove that 9 | 10ⁿ −1.
example {n : ℕ} (hn : n > 0) : 9 ∣ 10^n - 1 := by
  sorry

example : ∀ (n : ℕ) (hn : 1 ≤ n), 9 ∣ 10^n - 1 := by
  apply Nat.le_induction
  · norm_num
  · intro k hn h1
    rcases h1 with ⟨m, h1⟩
    use 10 * m + 1
    have h2 : 9 * (10 * m + 1) = 9 * m * 10 + 9 := by
      ring
    rw [h2, ← h1]
    have h3 : 10 ^ (k + 1) = 10 * 10 ^ k := by
      exact pow_succ 10 k
    rw[h3]
    rw [Nat.mul_sub_right_distrib, Nat.sub_eq_of_eq_add]
    rw [Nat.add_assoc]
    norm_num
    rw [Nat.sub_add_cancel]
    rw [Nat.mul_comm 10 (10 ^ k)]
    norm_num
    have h: 1 = 10^0 := by norm_num
    rw [h]
    apply Nat.pow_le_pow_of_le_right
    linarith
    linarith






-- 6.4 Let n be a positive integer.
--     Use induction to prove that 8 |3²ⁿ −1.
example {n : ℕ} (hn : n > 0) : 8 ∣ 3^(2 * n) - 1 := by
  sorry

example : ∀ (n : ℕ) (hn : 1 ≤ n), 8 ∣ 3^(2 * n) - 1 := by
  apply Nat.le_induction
  · norm_num
  · intro k hn h1
    rcases h1 with ⟨m, h1⟩
    use 9 * m + 1
    have h2 : 8 * (9 * m + 1) = 8 * m * 9 + 8 := by
      ring
    rw[h2, ← h1]
    have h3 : 3^(2 * (k+1)) = 3 ^ (2 * k) * 3 ^ 2 := by
      rw[mul_add, mul_one]
      rw[← one_add_one_eq_two, add_assoc (1+1)]
      -- 2 * (k + 1) = 2 * k + 2 = ((2 * k) + 1) + 1
      rw[pow_succ, pow_succ]
    rw[h3]
    rw [Nat.mul_sub_right_distrib, Nat.sub_eq_of_eq_add]
    rw [Nat.add_assoc]
    norm_num
    rw [Nat.sub_add_cancel]
    rw [Nat.mul_comm]
    norm_num
    have h : 1 = 3 ^ 0 := by norm_num
    rw[h]
    apply Nat.pow_le_pow_of_le_right
    linarith
    linarith





-- 6.5 Let n be a positive integer.
--     Use induction to prove that 6 |n³ −n.
example {n : ℕ} (hn : n > 0) : 6 ∣ n^3 - n := by
  sorry

example : ∀ (n : ℕ) (hn : 1 ≤ n), 6 ∣ n^3 - n := by
  apply Nat.le_induction
  · norm_num
  · intro k hn h1
    rcases h1 with ⟨m, h1⟩
    have h2 : (k+1)^3 - (k+1) = k^3 + 3 * k^2 + 3 * k -k := by
      --apply?
      norm_num -- why isnt this working??
      --rfl
    rw[h2]
    have h3 : 3 * k^2 + 3 * k = 3 * k * (k+1) := by
      norm_num
    rw[add_assoc, h3]
    -- rw[add_assoc, h1]
    have h4 : k^3 + 3 * k * (k+1) -k = k^3 -k + 3 * k * (k+1) := by
      rw[add_assoc]
    rw[h4, h1]
    have h5 : 2 | k^3 -k + 3 * k * (k+1) := by
      apply Nat.even_add_one -- Even (n + 1) ↔ ¬Even n
      apply Nat.even_mul     -- Even (m * n) ↔ Even m ∨ Even n
    












example : ∀ (n : ℕ) (hn : 1 ≤ n) , ∃ m , n * (n+1) = 2 * m := by
  intro n hn
  --apply?
  refine ex_of_PSigma
  sorry


-- 6.6 Let n be a positive integer.
--     Use induction to prove that
