import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Parity

-- 3.0.01 (complicated way) Prove that (x + y) * (x + y) = x * x + (x * y + y * x) + y * y
example {x y : ℝ} : (x + y) * (x + y) = x * x + (x * y + y * x) + y * y := by
  calc
    _ = (x + y) * x + (x + y) * y := by exact mul_add (x + y) x y  -- 5. The Distributive Law
    _ = x * (x + y) + y * (x + y):= by rw [mul_comm (x + y) x, mul_comm (x + y) y]  -- 3. Commutativity
    _ = x * x + x * y + (y * x + y * y) := by rw [mul_add x x y, mul_add y x y]  -- 5. The Distributive Law
    _ = x * x + (x * y + (y * x + y * y)) := by rw [add_assoc (x * x) (x * y) (y * x + y * y)]  -- 4. Associativity
    _ = x * x + ((x * y + y * x) + y * y) := by rw [← add_assoc (x * y) (y * x) (y * y)]  -- 4. Associativity
    _ = x * x + (x * y + y * x) + y * y := by rw [← add_assoc (x * x) (x * y + y * x) (y * y)]  -- 4. Associativity


-- 3.0.01 (simple way) Prove that (x + y) * (x + y) = x * x + (x * y + y * x) + y * y
example {x y : ℝ} : (x + y) * (x + y) = x * x + (x * y + y * x) + y * y := by
  ring


-- theorem 3.1. If a and b are even integers, then a + b is even.
theorem c3_1 {a b : ℤ} (h1 : Even a) (h2 : Even b) : Even (a + b) := by
  cases' h1 with k1 h1
  cases' h2 with k2 h2
  use k1 + k2
  rw [h1, h2]
  ring


-- theorem 3.2. Suppose a, b, and c are integers. If a|b and b|c, then a|c.
theorem c3_2 {a b c : ℤ} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  cases' h1 with k h1
  cases' h2 with l h2
  use k * l
  rw [h2, h1]
  ring


-- 3.1.03 If P → R, and R → Q, then P → Q.
example {P Q R : Prop} (h1 : P → R) (h2 : R → Q) : P → Q := by
  intro h
  apply h2
  apply h1
  exact h


-- 3.1.04 If a and b are even integers, then 2 ∣ a + b
example {a b : ℤ} (h1 : Even a) (h2 : Even b) : 2 ∣ a + b := by
  have h3 : Even (a + b) := by
    exact c3_1 h1 h2
  cases' h3 with k h4
  use k
  rw [h4]
  ring


-- 3.2.1 (Theorem 3.3.) The product of two consecutive integers is even.
theorem c3_3 (n : ℤ) : Even (n * (n + 1)) := by
  have h : Even n ∨ Odd n := by
    exact Int.even_or_odd n
  cases' h with heven hodd
  · cases' heven with k heven
    use k * (n + 1)
    rw [heven]
    ring
  · cases' hodd with k hodd
    use n * (k + 1)
    rw [hodd]
    ring


-- (Theorem 3.4.) (Elementary Properties of Absolute Value).
-- Suppose a and b are integers. Then:

-- 3.2.2. |a| ≥ 0.
theorem c3_4_1 {a : ℤ} : |a| ≥ 0 := by
  have h : a < 0 ∨ a = 0 ∨ a > 0 := by
    exact lt_trichotomy a 0
  rcases h with h1 | h2 | h3
  · have h : |a| = -a := by
      exact abs_of_neg h1
    rw [h]
    linarith
  · rw [h2]
    norm_num
  · have h : |a| = a := by
      exact abs_of_pos h3
    rw [h]
    linarith


-- 3.2.3. |-a| = |a|
theorem c3_4_2 {a : ℤ} : |-a| = |a| := by
  have h : a < 0 ∨ a = 0 ∨ a > 0 := by
    exact lt_trichotomy a 0
  rcases h with h1 | h2 | h3
  · have h : -a > 0 := by
      linarith
    rw [abs_of_pos h, abs_of_neg h1]
  · rw [h2]
    norm_num
  · have h : -a < 0 := by
      linarith
    rw [abs_of_neg h, abs_of_pos h3]
    ring



-- 3.4.01 If P is true, then P is true
example {P : Prop} (h : P) : P := by
  by_contra h1
  contradiction
