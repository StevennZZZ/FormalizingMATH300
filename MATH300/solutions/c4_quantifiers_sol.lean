import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Parity

-- 4.1  for all integers m and n,
--      4 |(m² + n²) if and only if m and n are even.
example {m n : ℤ} : ∀ m n : ℤ, 4 ∣ (m^2 + n^2) ↔ Even m ∧ Even n := by
  sorry

-- 4.2  for all integers a, b, and c, with c ≠ 0,
--      a | b if and only if ca | cb.
example {a b c : ℤ} (h : c ≠ 0) :
        ∀ a b c : ℤ, a ∣ b ↔ c * a ∣ c * b := by
  sorry

-- 4.3 Prove that there exist integers m and n such that
--     2m + 3n = 12.
--     Are these integers unique? (Justify your answer.)
example {m n : ℤ} : ∃ m n, 2 * m + 3 * n = 12 := by
  sorry

-- 4.4 Prove that there is no negative integer n
--     such that n² + n < 0.
--     (HINT: Notice that you are proving the negation of:
--      there exists a negative integer n such that
--      n² + n < 0.)
example {n : ℤ} : ¬(∃ n, n^2 + n < 0) := by
  sorry

-- 4.5 Prove that, for every integer m, there is a unique
--     integer n such that 5m −n = 8.
example {m : ℤ} : ∀ m : ℤ, ∃! n, 5 * m - n = 8 := by
  sorry
