import Mathlib.Tactic

section -- 8.1

-- 8.1 Let a, b, c, d ∈ ℤ. Let m be a positive integer.
variable {a b c d m : ℤ}
--     Prove that if a ≡ b (mod m) and c ≡ d (mod m), then
variable (h₁ : a ≡ b [ZMOD m]) (h₂ : c ≡ d [ZMOD m])

-- (a + c) ≡ (b + d) (mod m)
example : (a + c) ≡ (b + d) [ZMOD m] := by
  sorry

-- ac ≡ bd (mod m)
example : a * c ≡ b * d [ZMOD m] := by
  sorry

end

-- 8.2 Use induction to prove that,
--     for any non-negative integer n, 10ⁿ ≡ 1 (mod 9)
example : ∀ n : ℕ, 10^n ≡ 1 [ZMOD 9] := by
  sorry

-- 8.3 Prove that 20 ∣ 3⁵⁴²⁷ - 7.
example : 20 ∣ 3^5427 - 7 := by
  sorry

-- 8.4 Prove that 35 ∣ 14⁷⁸⁰⁰ - 21.
example : 35 ∣ 14^7800 - 21 := by
  sorry

-- 8.5 Prove the following theorem: Let n ∈ Z.
--     If 4 | n, then 76n ≡ n (mod 100).
example {n : ℤ} (h : 4 ∣ n) : 76 * n ≡ n [ZMOD 100] := by
  sorry

-- 8.6, 8.7, 8.8 skip
