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


-- 3.2.01 (Theorem 3.3.) The product of two consecutive integers is even.
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

-- 3.2.02. |a| ≥ 0.
theorem c3_4_a {a : ℤ} : |a| ≥ 0 := by
  have h : a < 0 ∨ a ≥ 0 := by
    exact lt_or_le a 0
  cases' h with h1 h2
  · rw [abs_of_neg h1]
    linarith
  · rw [abs_of_nonneg h2]
    exact h2


-- 3.2.03. |-a| = |a|
theorem c3_4_b {a : ℤ} : |-a| = |a| := by
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


-- 3.2.04. -|a| ≤ a ≤ |a|
theorem c3_4_c {a : ℤ} : -|a| ≤ a ∧ a ≤ |a| := by
  have h : a < 0 ∨ a ≥ 0 := by
    exact lt_or_le a 0
  cases' h with h1 h2
  · constructor
    · rw [abs_of_neg h1]
      linarith
    · rw [abs_of_neg h1]
      linarith
  · constructor
    · rw [abs_of_nonneg h2]
      linarith
    · rw [abs_of_nonneg h2]


-- 3.2.05 |a|² = a²
theorem c3_4_d {a : ℤ} : |a|^2 = a^2 := by
  have h : a < 0 ∨ a ≥ 0 := by
    exact lt_or_le a 0
  cases' h with h1 h2
  · rw [abs_of_neg h1]
    ring
  · rw [abs_of_nonneg h2]


-- 3.2.06 |ab| = |a||b|
theorem c3_4_e {a b : ℤ} : |a * b| = |a| * |b| := by
  have ha : a < 0 ∨ a = 0 ∨ a > 0 := by
    exact lt_trichotomy a 0
  rcases ha with ha1 | ha2 | ha3
  · have hb : b < 0 ∨ b = 0 ∨ b > 0 := by
      exact lt_trichotomy b 0
    rcases hb with hb1 | hb2 | hb3
    · have htemp : b * a > 0 * a:= by
        exact mul_lt_mul_of_neg_right hb1 ha1
      have hab : a * b > 0 := by
        linarith
      rw [abs_of_pos hab, abs_of_neg ha1, abs_of_neg hb1]
      ring
    · rw [hb2]
      norm_num
    · have htemp : b * a < 0 * a := by
        exact mul_lt_mul_of_neg_right hb3 ha1
      have hab : a * b < 0 := by
        linarith
      rw [abs_of_neg hab, abs_of_neg ha1, abs_of_pos hb3]
      ring
  · have hb : b < 0 ∨ b ≥ 0 := by
      exact lt_or_le b 0
    cases' hb with hb1 hb2
    · rw [ha2]
      norm_num
    · rw [ha2]
      norm_num
  · have hb : b < 0 ∨ b = 0 ∨ b > 0 := by
      exact lt_trichotomy b 0
    rcases hb with hb1 | hb2 | hb3
    · have htemp : a * b < 0 * b := by
        exact mul_lt_mul_of_neg_right ha3 hb1
      have hab : a * b < 0 := by
        linarith
      rw [abs_of_neg hab, abs_of_pos ha3, abs_of_neg hb1]
      ring
    · rw [hb2]
      norm_num
    · have htemp : 0 * b < a * b := by
        exact mul_lt_mul_of_pos_right ha3 hb3
      have hab : a * b > 0 := by
        linarith
      rw [abs_of_pos hab, abs_of_pos ha3, abs_of_pos hb3]


-- 3.2.07 |a| ≤ |b| iff -|b| ≤ a ≤ |b|
theorem c3_4_f {a b : ℤ} : |a| ≤ |b| ↔ -|b| ≤ a ∧ a ≤ |b| := by
  constructor
  · intro h1
    constructor
    · have ha : a < 0 ∨ a ≥ 0 := by
        exact lt_or_le a 0
      cases' ha with ha1 ha2
      · rw [abs_of_neg ha1] at h1
        linarith
      · rw [abs_of_nonneg ha2] at h1
        linarith
    · have ha : a < 0 ∨ a ≥ 0 := by
        exact lt_or_le a 0
      cases' ha with ha1 ha2
      · have htemp : |b| ≥ 0 := by
          exact c3_4_a
        linarith
      · rw [abs_of_nonneg ha2] at h1
        exact h1
  · intro h2
    cases' h2 with h21 h22
    have ha : a < 0 ∨ a ≥ 0 := by
      exact lt_or_le a 0
    cases' ha with ha1 ha2
    · rw [abs_of_neg ha1]
      linarith
    · rw [abs_of_nonneg ha2]
      linarith


-- 3.2.08 (Theorem 3.5) Triangle Inequality.
--        If a and b are integers, then |a + b| ≤ |a| + |b|
theorem c3_5 {a b : ℤ} : |a + b| ≤ |a| + |b| := by
  have h1a : -|a| ≤ a ∧ a ≤ |a| := by
    exact c3_4_c
  have h1b : -|b| ≤ b ∧ b ≤ |b| := by
    exact c3_4_c
  cases' h1a with h1a_left h1a_right
  cases' h1b with h1b_left h1b_right
  have h2_left : -|a| + (-|b|) ≤ a + b := by
    exact add_le_add h1a_left h1b_left  -- can also use linarith
  have h2_right : a + b ≤ |a| + |b| := by
    exact add_le_add h1a_right h1b_right  -- can also use linarith
  have h3 : -(|a| + |b|) ≤ a + b ∧ a + b ≤ |a| + |b| := by
    constructor
    · rw [neg_eq_neg_one_mul |a|, neg_eq_neg_one_mul |b|] at h2_left
      rw [← mul_add (-1) |a| |b|, ← neg_eq_neg_one_mul (|a| + |b|)] at h2_left
      exact h2_left
    · exact h2_right
  have h4 : |(|a| + |b|)| = |a| + |b| := by
    have h41 : |a| ≥ 0 := by
      exact c3_4_a
    have h42 : |b| ≥ 0 := by
      exact c3_4_a
    have h43 : |a| + |b| ≥ 0 := by
      exact add_le_add h41 h42
    exact abs_of_nonneg h43
  rw [← h4]
  rw [← h4] at h3
  exact (@c3_4_f (a + b) (|a| + |b|)).2 h3


-- 3.3.01 (Theorem 3.6) Suppose n is an integer. If n² is even, then n is even.
theorem c3_6 {n : ℤ} : Even (n^2) → Even n := by
  contrapose!
  intro h
  rw [← Int.odd_iff_not_even]
  rw [← Int.odd_iff_not_even] at h
  cases' h with k h
  use (2*k^2+2*k)
  rw[h]
  ring


-- 3.3.02 (Theorem 3.7) Let n be an integer. If n² + 2n < 0, then n < 0.
theorem c3_7 {n : ℤ} : n^2 + 2 * n < 0 → n < 0 := by
  contrapose!
  intro h1
  have h2 : 0 ≤ n^2 := by
    exact sq_nonneg n
  linarith


-- 3.4.01 If P is true, then P is true
example {P : Prop} (h : P) : P := by
  by_contra h1
  contradiction


-- 3.4.02 (Theorem 3.8.) No integer is both even and odd.
theorem c3_8 {n : ℤ} : ¬(Even n ∧ Odd n) := by
  by_contra h
  cases' h with heven hodd
  cases' heven with k h1
  cases' hodd with l h2
  rw [h1] at h2
  have h3 : 2 * (k - l) = 1 := by
    linarith
  have h4 : (2 : ℤ) ∣ 1 := by
    use (k - l)
    exact h3.symm
  norm_num at h4


-- 3.4.03 (Theorem 3.9.) √2 is irrational.
theorem c3_9 {m n : ℤ} (h1 : n ≠ 0) (h2 : ¬(Even m ∧ Even n)) : 2 * n^2 ≠ m^2 := by
  by_contra h3
  have h4 : Even (m^2) := by
    use n^2
    linarith
  have h5 : Even m := by
    exact c3_6 h4
  have h6 : ∃ k, m = k + k := by
    cases' h5 with k h5
    use k
  cases' h6 with k h6
  have h7 : 2 * n^2 - 4 * k^2 = 0 := by
    rw [h3, h6]
    ring
  have h8 : n^2 = k^2 + k^2 := by
    linarith
  have h9 : Even (n^2) := by
    use k^2
  have h10 : Even n := by
    exact c3_6 h9
  have h11 : Even m ∧ Even n := by
    constructor
    · exact h5
    · exact h10
  contradiction


-- 3.4.04 (Theorem 3.10.) Let a be an integer. If a² is odd, then a is odd.

-- contrapositive

theorem c3_10_a {a : ℤ} : Odd (a^2) → Odd a := by
  contrapose!
  rw [← Int.even_iff_not_odd, ← Int.even_iff_not_odd]
  intro h
  cases' h with k h
  use 2 * k^2
  rw [h]
  ring

-- contradiction

-- Exercise 3.1(b)
theorem e3_1_b {a b : ℤ} (ha : Even a) (hb : Odd b) : Odd (a + b) := by
  cases' ha with k1 h1
  cases' hb with k2 h2
  use (k1 + k2)
  rw [h1, h2]
  ring

-- Then...
theorem c3_10_b {a : ℤ} : Odd (a^2) → Odd a := by
  intro h1
  by_contra h2
  rw [← Int.even_iff_not_odd] at h2
  have h3 : Odd (a + a^2) := by
    exact (e3_1_b h2 h1)
  have h4 : a + a^2= a * (a + 1) := by
    ring
  rw [h4] at h3
  have h5 : Even (a * (a + 1)) := by
    exact c3_3 a
  rw [Int.even_iff_not_odd] at h5
  contradiction


-- 3.5.01 (Theorem 3.11.) Let a be an integer. Then a is odd if and only if a² −1 is even.
theorem c3_11 {a : ℤ} : Odd a ↔ Even (a^2 - 1) := by
  constructor
  · intro h1
    cases' h1 with k h1
    use (2 * k^2 + 2 * k)
    rw [h1]
    ring
  · contrapose!
    rw [← Int.even_iff_not_odd, ← Int.odd_iff_not_even]
    intro h2
    cases' h2 with k h2
    use 2 * k^2 - 1
    rw [h2]
    ring
