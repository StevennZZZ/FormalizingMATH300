import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Parity

-- 4.1  for all integers m and n,
--      4 |(m² + n²) if and only if m and n are even.
-- You might need this theorem, which is De Morgan's laws in Lean:
-- theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b
-- Some other theorems about parity that we used in chapter 3 can be helpful
-- e.g. Int.odd_iff_not_even, Int.even_or_odd, etc.
example : ∀ m n : ℤ, 4 ∣ (m^2 + n^2) ↔ Even m ∧ Even n := by
  sorry


-- 4.2  for all integers a, b, and c, with c ≠ 0,
--      a | b if and only if ca | cb.
-- You might need this theorem:
-- theorem mul_left_inj'... (hc : c ≠ 0) : a * c = b * c ↔ a = b
example : ∀ a b c : ℤ, (c ≠ 0) → (a ∣ b ↔ c * a ∣ c * b) := by
  sorry


-- 4.3 Prove that there exist integers m and n such that
--     2m + 3n = 12.
--     Are these integers unique? (Justify your answer.)
example : ∃ m n, 2 * m + 3 * n = 12 := by
  sorry
  -- briefly explain why these integers are unique / not unique


-- 4.4 Prove that there is no negative integer n
--     such that n² + n < 0.
--     (HINT: Notice that you are proving the negation of:
--      there exists a negative integer n such that
--      n² + n < 0.)
-- You may need this theorem:
-- theorem mul_nonneg_of_nonpos_of_nonpos ...
--         (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b
example : ¬(∃ n : ℤ, n^2 + n < 0) := by
  sorry


-- 4.5 Prove that, for every integer m, there is a unique
--     integer n such that 5m −n = 8.
-- hint hint: exists_unique_of_exists_of_unique is your friend :)
example : ∀ m : ℤ, ∃! n, 5 * m - n = 8 := by
  sorry
