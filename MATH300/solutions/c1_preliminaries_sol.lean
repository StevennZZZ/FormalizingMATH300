import Mathlib.Data.Real.Basic

section -- 1.1
-- 1.1 (a): If a and b are integers and a + b = a,
--          then b = 0
example (a b : ℤ) (h : a + b = a) : b = 0 := by
  rw [add_comm a b] at h  -- EPI 3
  nth_rewrite 2 [←zero_add a] at h  -- EPI 6
  exact add_right_cancel h  -- EPI 11


-- 1.1 (b): If a, b, c and d are integers, then
--          (a + b) + (c + d) = (a + c) + (b + d)
example (a b c d : ℤ) : (a + b) + (c + d) =
                        (a + c) + (b + d) := by
  rw [add_assoc a c (b + d)]  -- EPI 4
  rw [← add_assoc c b d]  -- EPI 4
  rw [add_comm c b]  -- EPI 3
  rw [add_assoc b c d]  -- EPI 4
  rw [←add_assoc  a b (c + d)]  -- EPI 4


-- 1.1 (c): If a, b, and c are integers such that ac = bc
--          and c ≠ 0, then a = b.
-- Warning: The theorem we need for this problem is not in EPI's table!
-- It also requires "prove by cases" technique in chapter 3.
-- We will go back to this problem in chapter 3. Feel free for ignore it for now.
example (a b c : ℤ) (h1 : a * c = b * c) (h2 : c ≠ 0) :
                    a = b := by
  rw [mul_eq_mul_right_iff] at h1
  cases' h1 with ha hb  -- prove by cases
  · exact ha
  · contradiction  -- trivially true


-- 1.1 (d) : Binomial Expansion: If a and b are integers,
--           then (a + b)² = (a² + 2ab) + b²
--                         = a² + (2ab + b²)
--(Note: for any integer x, x² = x ·x and x + x = 2x.
-- You can find the commands for x^2 = x ·x in EPI 25.
-- The command for 2 * x = x + x is "two_mul x"
-- * For this Lean exercise
--   You only need to prove (a + b)² = a² + (2(ab) + b²)
example (a b : ℤ) : (a + b)^2 = a^2 + (2 * (a * b) + b^2) := by
  rw [sq (a + b)]  -- EPI 25
  rw [mul_add (a + b) a b]  -- EPI 5
  rw [mul_comm (a + b) a, mul_comm (a + b) b]  -- EPI 3
  rw [mul_add a a b, mul_add b a b]  -- EPI 5
  rw [add_assoc (a * a) (a * b) (b * a + b * b)]  -- EPI 4
  rw [← add_assoc (a * b) (b * a) (b * b)]  -- EPI 4
  rw [mul_comm b a]  -- EPI 3
  rw [← two_mul (a * b)]  -- From the comments for this problem
  rw [← sq a, ← sq b]  -- EPI 25

end -- 1.1
