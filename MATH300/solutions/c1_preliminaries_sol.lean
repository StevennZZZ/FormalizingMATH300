import Mathlib.Data.Real.Basic

section -- 1.1
-- 1.1 (a): If a and b are integers and a + b = a,
--          then b = 0
example (a b : ℤ) (h : a + b = a) : b = 0 := by
  rw [← add_right_eq_self]
  exact h

-- 1.1 (b): If a, b, c and d are integers, then
--          (a + b) + (c + d) = (a + c) + (b + d)
example (a b c d : ℤ) : (a + b) + (c + d) =
                        (a + c) + (b + d) := by
  rw [add_assoc, ← add_assoc b, add_comm b c, add_assoc c b, add_assoc a c]

-- 1.1 (c): If a, b, and c are integers such that ac = bc
--          and c ≠ 0, then a = b.
example (a b c : ℤ) (h₁ : a * c = b * c) (h₂ : c ≠ 0) :
                    a = b := by
  sorry

-- 1.1 (d) : Binomial Expansion: If a and b are integers,
--           then (a + b)² = (a² + 2ab) + b²
--                         = a² + (2ab + b²)
--(Note: for any integer x, x² = x ·x and x + x = 2x.)
-- * You only need to prove (a + b)² = (a² + 2ab) + b²
--   in this Lean exercise
example (a b : ℤ) : (a + b)^2 = (a^2 + 2 * a * b) + b^2 := by
  exact add_sq a b

end -- 1.1
