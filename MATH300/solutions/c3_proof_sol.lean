import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Parity
import MATH300.guide.c3
import Mathlib.Data.Real.Irrational

-- Start from thes exercises we will make use of many theorems proved either in Mathlib
-- or by ourselves earlier.
-- You can see that we import "MATH300.guide.c3", which indicates the path of "c3.lean" file
-- and contains all the theorems we proved in the chapter 3 guide.
-- Feel free to use any of the theorems :)


-- Suppose a and b are integers, prove each of the following:
-- 3.1 (a) If a and b are both odd, then a + b is even.
theorem e3_1_a {a b : ℤ} (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  cases' ha with k1 h1
  cases' hb with k2 h2
  use (k1 + k2 + 1)
  rw [h1, h2]
  ring


-- 3.1 (b) If a is even and b is odd, then a + b is odd. (proved in the guide)


-- 3.1 (c) If a + b is odd,
--         then a and b must have opposite parity.
-- hint: Useful Mathlib theorems: Int.even_or_odd (n : ℤ) : Even n ∨ Odd n
--                                Int.odd_iff_not_even {n : ℤ} : Odd n ↔ ¬Even n
--                                Int.even_iff_not_odd {n : ℤ} : Even n ↔ ¬Odd n
-- Useful theorem from our guide: c3_1 {a b : ℤ} (h1 : Even a) (h2 : Even b) : Even (a + b)
--                                e3_1_b {a b : ℤ} (ha : Even a) (hb : Odd b) : Odd (a + b)
-- And don't forget the theorems you proved in this file!
example {a b : ℤ} (h : Odd (a + b)) : (Even a ∧ Odd b) ∨ (Odd a ∧ Even b) := by
  have ha : Even a ∨ Odd a := by
    exact Int.even_or_odd a
  have hb : Even b ∨ Odd b := by
    exact Int.even_or_odd b
  cases' ha with ha1 ha2
  · cases' hb with hb1 hb2
    · have h_contra : Even (a + b) := by
        exact c3_1 ha1 hb1
      rw [Int.even_iff_not_odd] at h_contra
      contradiction
    · left
      constructor
      · exact ha1
      · exact hb2
  · cases' hb with hb1 hb2
    · right
      constructor
      · exact ha2
      · exact hb1
    have h_contra : Even (a + b) := by
        exact e3_1_a ha2 hb2
    rw [Int.even_iff_not_odd] at h_contra
    contradiction


-- 3.2 proved in the guide

-- 3.3 Let a and b be negative integers.
--     Prove that if a < b then a² > b².
example {a b : ℤ} (ha : a < 0) (hb : b < 0) (h : a < b) : a^2 > b^2 := by
  have h1 : a * a > b * a := by
    exact mul_lt_mul_of_neg_right h ha  -- EPI 20
  have h2 : a * b > b * b := by
    exact mul_lt_mul_of_neg_right h hb  -- EPI 20
  linarith


-- 3.4 Suppose a and b are positive integers.
--     Prove that, if a | b, then a ≤ b.
--     Hint: I declare a and b as natural numbers instead of integers here.
--     It makes no difference in the context but becomes much more easier to deal with in Lean.
--     Depending on how you approach this problem, you might need this theorem:
--     A natural number ≠ 0 if and only if it's ≥ 1. (In Lean natural numbers start from 0).
--     In Lean: Nat.one_le_iff_ne_zero {n : ℕ} : 1 ≤ n ↔ n ≠ 0
theorem e3_4 {a b : ℕ} (h1 : a > 0) (h2 : b > 0) (h : a ∣ b) : a ≤ b := by
  cases' h with k h
  rw [h]
  have h1 : k ≠ 0 := by
    by_contra h2
    have h3 : a * k = 0 := by
      rw [h2]
      ring
    rw [h3] at h
    have h4 : ¬b > 0 := by
      linarith
    contradiction
  have h2 : k ≥ 1 := by
    exact Nat.one_le_iff_ne_zero.2 h1
  have h3 : a ≥ 0 := by
    linarith
  have h4 : 1 * a ≤ k * a := by
    exact mul_le_mul_of_nonneg_right h2 h3
  linarith


-- 3.5 Let a,b and c be positive integers.
--     Prove that if a|b and b|c, then a|c.
example {a b c: ℤ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  cases' h1 with k1 h1
  cases' h2 with k2 h2
  rw [h1] at h2
  use k1 * k2
  rw [h2]
  ring


-- 3.6 Suppose a > 0 and b ≥ 0 are integers such that a|b.
--     Prove that, if b < a, then b = 0.
--     Hint: The theorems we use in exercise 3.4 (or even the theorem e3_4 itself!) might be useful.
example {a b : ℕ} (ha : a > 0) (hb : b ≥ 0) (h : a ∣ b) : b < a → b = 0 := by
  intro h1
  by_contra h2
  have h3 : b ≥ 1 := by
    exact Nat.one_le_iff_ne_zero.2 h2
  have h4 : b > 0 := by
    linarith
  have h5 : b ≥ a := by
    exact e3_4 ha h4 h
  have h6 : ¬b < a := by
    linarith
  contradiction


-- ** The next Lean exercise is optional and unrelated to what we've learned in this chapter's guide.
--    Feel free to skip to 3.8.

-- 3.7 This problem is testing your skill to apply closure of integers and to prove by contracition.
--     Unfortunately, Lean' definitions of the rational number and the quotient of integers
--     are completely different from the textbook's :(
--     We can, of course, define our own rational numbers and division operation here,
--     but we don't have enough programming tools yet.
--     Therefore, I will not ask you to prove these theorems in Lean for now,
--     and I will show you the corresponding theorems in Mathlib.
--     Hopefully we can get back to this problem later once we are more skilled at Lean.
-- p.s. Here we use the command "section ... end" commands to define a space in this file specifically for some variables.
--      Then we use "variable {...} (...)"" command to declare those variables that can be used everywhere in the space.
--      After the "end" command those variables will be gone forever.
--      We will talk more about these commands in chapter 5.

-- Textbook's definition of rational numbers:
-- a number q is rational if it can be written in the form m/n ,
-- where m and n are integers and n ̸= 0. Any real number that is not rational is irrational.

section
-- theorem (a) & fact 1:
-- If q and r are rational, then q + r and qr are rational.
variable {q r : ℚ}
#check q + r
#check q * r
-- Given two rational numbers a/b and c/d , we define their sum and product as follows:
-- a/b + c/d = (a*d + b*c) / (b*d) and (a/b) * (c/d) = (a*c) / (b*d).
-- In Lean, you can use the command "Rat.normalize a b"
-- to make a rational number "a / b" to its normalized form (reduced form).
-- To a rational number q, you can access its numerator by "q.num" and denominator by "q.den".
#check Rat.add_def q r
#check Rat.mul_def q r
#eval (3/2 : ℚ) + (4/3 : ℚ)
#eval (3/2 : ℚ) * (4/3 : ℚ)
end

-- fact 2: For any integer a ≠ 0, a / a = 1.
-- Again, Lean's definition of quotient of integers is different. We will skip this for now.

section
-- fact 3: Every rational number q has a rational additive inverse −q such that q + (−q) = (−q) + q = 0
variable {q : ℚ}
#check Rat.add_comm q (-q)
#check Rat.add_left_neg q
end

section
-- fact 4: Every irrational number r has an irrational additive inverse −r such that r+(−r) = (−r)+r = 0.
-- Mathlib.Data.Real.Irrational package includes theorems  about irrational numbers
variable {r : ℝ} (h : Irrational r)
example : r + (-r) = -r + r := by
  ring
example : r + (-r) = 0 := by
  ring

section
-- theorem (b) If q is rational and r is irrational, then q + r is irrational.
variable {q : ℚ} {r : ℝ} (hr : Irrational r)
#check Irrational.rat_add q hr
end

section
-- theorem (c) If q is rational, q ≠ 0, and r is irrational, then qr is irrational.
variable {q : ℚ} {r : ℝ} (hq : q ≠ 0) (hr : Irrational r)
#check Irrational.mul_rat hr hq
end

-- theorem (d) The sum of two irrational numbers may be a rational number.
--     This can be proved using the fact 4. We only need to show that 0 is a rational number.
#check (0 : ℚ)


-- 3.8 Let a and b be integers. Prove that
--     a²b + a + b is even if and only if a and b are both even.
--     Hint: contrapose! tactic sometimes can be "too aggressive"
--           To use the fact of logic that "P → Q ≡ ¬P ∨ Q", use this Mathlib theorem:
--           not_or_of_imp {a b : Prop} (a✝ : a → b) : ¬a ∨ b
--           Don't forget that you can use the theorems we proved before!
example {a b : ℤ} : Even (a^2 * b + a + b) ↔ Even a ∧ Even b := by
  constructor
  · contrapose!
    intro h1
    rw [← Int.odd_iff_not_even]
    have h2 : Odd a ∨ Odd b := by
      rw[Int.odd_iff_not_even, Int.odd_iff_not_even]
      exact not_or_of_imp h1
    cases' h2 with ha hb
    · cases' ha with k ha
      use 2 * k^2 * b + b + 2 * k * b + k
      rw [ha]
      ring
    · cases' hb with k hb
      rw [hb]
      have h2 : a ^ 2 * (2 * k + 1) + a + (2 * k + 1) = 2 * (k * a^2 + k) + a * (a + 1) + 1 := by
        ring
      rw [h2]
      have h3 : Even (a * (a + 1)) := by
        exact c3_3 a
      cases' h3 with g h3
      rw [h3]
      use k * a^2 + k + g
      ring
  · intro h
    cases' h with ha hb
    have h_prod_even (x y : ℤ) (h_x : Even x) (h_y : Even y) : Even (x * y) := by
      cases' h_x with k1 h_x
      cases' h_y with k2 h_y
      use 2 * k1 * k2
      rw [h_x, h_y]
      ring
    have h1 : Even (a^2) := by
      have htemp : a^2 = a * a := by
        ring
      rw [htemp]
      exact h_prod_even a a ha ha
    have h2 : Even (a^2 * b) := by
      exact h_prod_even (a^2) b h1 hb
    have h3 : Even (a^2 * b + a) := by
      exact c3_1 h2 ha
    have h4 : Even (a^2 * b + a + b) := by
      exact c3_1 h3 hb
    exact h4


-- 3.9 Prove that, if n is the product of any four
--     consecutive integers, then n + 1 is the square
--     of an integer
example (a n : ℤ) (h : n = a * (a + 1) * (a + 2) * (a + 3)) : ∃ b : ℤ, n + 1 = b^2 := by
  use a^2 + 3 * a + 1
  rw [h]
  ring
