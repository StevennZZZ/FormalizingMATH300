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
    -- rewrite using function sub_mul and use ring
