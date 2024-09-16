import Mathlib.Data.Real.Basic

-- 4.1.01 Let a, b, and c be integers and suppose that c|a and c|b.
--        For all integers n and m, c|(an + bm).
example {a b c : ℤ} (h1 : c ∣ a) (h2 : c ∣ b) : ∀ n m : ℤ, c ∣ (a * n + b * m) := by
  cases' h1 with k1 h1
  cases' h2 with k2 h2
  intro n m
  use k1 * n + k2 * m
  rw [h1]
  rw [h2]
  ring


-- 4.2.01 There exist integers m and n such that 10m + 13n = 3.
example : ∃ m n : ℤ, 10 * m + 13 * n = 3 := by
  use -1, 1
  norm_num


-- 4.2.02 For every integer a, there exists an integer b such that a + b = 1.
theorem c4_eg : ∀ a : ℤ, ∃ b : ℤ, a + b = 1 := by
  intro a
  use 1 - a
  ring


-- 4.3.01 (Theorem 4.2.) For every integer a, there exists a UNIQUE integer b such that a + b = 1.
theorem c4_2 : ∀ a : ℤ, ∃! b : ℤ, a + b = 1 := by
  intro a
  apply exists_unique_of_exists_of_unique
  · exact c4_eg a  -- "use" the theorem (the same as conditional statement)
  · intro b c
    intro h1
    intro h2
    have h3 : b = 1 - a := by
      linarith
    have h4 : c = 1 - a := by
      linarith
    rw [h3, h4]

-- 4.3.02 (Theorem 4.3.) For every integer a, there is a unique integer b such that 10a + 2b = 4.
theorem c4_3 : ∀ a : ℤ, ∃! b : ℤ, 10 * a + 2 * b = 4 := by
  intro a
  apply exists_unique_of_exists_of_unique
  · use 2 - 5 * a
    ring
  · intro b c h1 h2
    have h3 : 10 * a + 2 * b = 10 * a + 2 * c := by
      rw [h1, h2]
    have h4 : 2 * b = 2 * c := by
      linarith
    have h5 : 0 = 2 * (c - b) := by
      linarith
    have h6 : (2 : ℤ)  = 0 ∨ c - b = 0 := by
      exact mul_eq_zero.1 (h5.symm)  -- EPI 15
    cases' h6 with h7 h8
    · norm_num at h7
    · linarith  -- based on h8
