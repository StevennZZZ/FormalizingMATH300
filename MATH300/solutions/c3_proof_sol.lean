import Mathlib.Data.Real.Basic

section -- 3.1

-- Suppose a and b are integers, prove each of the following:
variable (a b : ℤ)

-- 3.1 (a) If a and b are both odd, then a + b is even.
example (h : Odd a ∧ Odd b) : Even (a + b) := by
  cases' h with ha hb
  cases' ha with k₁ hc
  cases' hb with k₂ hd
  use k₁ + k₂ + 1
  rw [hc, hd]
  ring

-- 3.1 (b) If a is even and b is odd, then a + b is odd.
example (h : Even a ∧ Odd b) : Odd (a + b) := by
  cases' h with ha hb
  cases' ha with k₁ hc
  cases' hb with k₂ hd
  use k₁ + k₂
  rw [hc, hd]
  ring

-- 3.1 (c) If a + b is odd,
--         then a and b must have opposite parity.
example (h : Odd (a + b)) :
        (Even a ∧ Odd b) ∨ (Odd a ∧ Even b) := by
  sorry

end -- 3.1


section -- 3.2

-- Suppose a and b are integers.
variable (a b : ℤ)

-- 3.2 (c) −|a| ≤ a ≤ |a|
example : -|a| ≤ a ∧ a ≤ |a| := by
  rw [← abs_le]

-- 3.2 (d) |a|² = a²
example : |a|^2 = a^2 := by
  rw [sq_abs]

-- 3.2 (e) |ab|= |a||b|
example : |a * b| = |a| * |b| := by
  rw [abs_mul]

-- 3.2 (f) |a| ≤ |b| if and only if −|b| ≤ a ≤ |b|
example : |a| ≤ |b| ↔ -|b| ≤ a ∧ a ≤ |b| := by
  rw [abs_le]

end -- 3.2

-- 3.3 Let a and b be negative integers.
--     Prove that if a < b then a² > b².
example (a b : ℤ) (ha : a < 0) (hb : b < 0) (h : a < b) :
        a^2 > b^2 := by
  sorry

-- 3.4 Suppose a and b are positive integers.
--     Prove that, if a | b, then a ≤ b.
example (a b : ℤ) (ha : a > 0) (hb : b > 0) (h : a ∣ b) :
        a ≤ b := by
  sorry

-- 3.5 Let a,b and c be positive integers.
--     Prove that if a|b and b|c, then a|c.
example (a b c: ℤ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
        (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  sorry

-- 3.6 Suppose a > 0 and b ≥ 0 are integers such that a|b.
--     Prove that, if b < a, then b = 0.
example (a b : ℤ) (ha : a > 0) (hb : b ≥ 0) (h : a ∣ b) :
        b < a → b = 0 := by
  sorry

-- 3.7 too long, so skip for now

-- 3.8 Let a and b be integers. Prove that
--     a²b + a + b is even
--     if and only if a and b are both even.
example (a b : ℤ) : Even (a^2 * b + a + b)
                    ↔ Even a ∧ Even b := by
  sorry

-- 3.9 Prove that, if n is the product of any four
--     consecutive integers, then n + 1 is the square
--     of an integer
example (a b c d n : ℤ)
        (hb : b = a + 1) (hc : c = a + 2) (hd : d = a + 3)
        (hn : n = a * b * c * d) :
        (n + 1 = a^2) ∨ (n + 1 = b^2) ∨
        (n + 1 = c^2) ∨ (n + 1 = d^2) := by
  sorry
