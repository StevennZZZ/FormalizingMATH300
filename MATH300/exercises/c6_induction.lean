import Mathlib.Data.Int.Basic

-- 6.1 Prove: If a is a non-negative integer,
--            then aⁿ ≥ 0 for all n ∈ N.
example {a : ℕ} : ∀ n : ℕ, a^n ≥ 0 := by
  sorry

-- 6.2 Prove: If a and b are non-negative integers
--     such that a < b, then aⁿ < bⁿ for all n ∈ ℕ.
example {a b : ℕ} :
        ∀ n : ℕ, a < b → a^n < b^n := by
  sorry

-- 6.3 Let n be a positive integer.
--     Use induction to prove that 9 | 10ⁿ −1.
example {n : ℕ} (hn : n > 0) : 9 ∣ 10^n - 1 := by
  sorry

-- 6.4 Let n be a positive integer.
--     Use induction to prove that 8 |3²ⁿ −1.
example {n : ℕ} (hn : n > 0) : 8 ∣ 3^(2 * n) - 1 := by
  sorry

-- 6.5 Let n be a positive integer.
--     Use induction to prove that 6 |n³ −n.
example {n : ℕ} (hn : n > 0) : 6 ∣ n^3 - n := by
  sorry

-- 6.6 Let n be a positive integer.
--     Use induction to prove that
