import Mathlib.Data.Real.Basic

-- Before you work on exercises (1):
-- There is a variant of rw tactic: nth_rewrite
-- which works almost the same as rw, except an additional argument: n
-- i.e. (nth_rewrite n [h]), compared to (rw [h])
-- that will only rewrite the nth variable of the expression
-- if you use rw [h], it will try to rewrite all the variables!
example {x y : ℤ} (h1 : x = 1) (h2 : 1 + y = x): x + y = x := by
  nth_rewrite 1 [h1]  -- only changes the first x to 1, another x in the goal remains the same
  exact h2


-- Before you work on exercises (2):
-- In Lean, parentheses are put implicitly to the first two variables
-- e.g. (a + b) + (c + d) and a + b + (c + d) are internally the same


-- Good luck!


section -- 1.1
-- 1.1 (a): If a and b are integers and a + b = a,
--          then b = 0
example (a b : ℤ) (h : a + b = a) : b = 0 := by
  sorry

-- 1.1 (b): If a, b, c and d are integers, then
--          (a + b) + (c + d) = (a + c) + (b + d)
example (a b c d : ℤ) : (a + b) + (c + d) =
                        (a + c) + (b + d) := by
  sorry

-- 1.1 (c): If a, b, and c are integers such that ac = bc
--          and c ≠ 0, then a = b.
-- Warning: The theorem we need for this problem is not in EPI's table!
-- It also requires "prove by cases" and "prove by contradiction" in chapter 3.
-- We will go back to this problem in chapter 3. Feel free for ignore it for now.
example (a b c : ℤ) (h1 : a * c = b * c) (h2 : c ≠ 0) :
                    a = b := by
  sorry


-- 1.1 (d) : Binomial Expansion: If a and b are integers,
--           then (a + b)² = (a² + 2ab) + b²
--                         = a² + (2ab + b²)
--(Note: for any integer x, x² = x ·x and x + x = 2x.)
-- * You only need to prove (a + b)² = (a² + 2ab) + b²
--   in this Lean exercise
example (a b : ℤ) : (a + b)^2 = (a^2 + 2 * a * b) + b^2 := by
  sorry

end -- 1.1
