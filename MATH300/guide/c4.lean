import Mathlib.Data.Real.Basic

-- 4.2.01 There exist integers m and n such that 10m + 13n = 3.
example : ∃ m n : ℤ, 10 * m + 13 * n = 3 := by
  use -1, 1
  norm_num


-- 4.2.02 For every integer a, there exists an integer b such that a + b = 1.
example : ∀ a : ℤ, ∃ b : ℤ, a + b = 1 := by
  intro a
  use 1 - a
  ring
