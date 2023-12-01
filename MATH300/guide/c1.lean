import Mathlib.Data.Real.Basic

--1.1.01

#eval 1 + 1 = 2
#eval 1 + 1 = 3
#eval 2^10 < 2000
#eval 500 * 20 + 1356^2 - 63794 ≥ 10000


--1.1.02
example {n : ℝ} (h1 : n = 1) : n + 1 = 2 := by
  rw [h1]
  norm_num


--1.1.03
example {a b : ℤ} (h1 : a = 2) (h2 : b = 5) : a + b = 7 := by
  rw [h1, h2]
  norm_num


--1.1.04
example {n : ℝ} (h1 : 1 = n) : n + 1 = 2 := by
  rw [← h1]
  norm_num


--1.2.01
example : |-7| = 7 := by
  norm_num


--1.2.02
example : 3 ∣ 6 := by
  use 2


--1.2.03
example : Even 20 := by
  use 10


--1.3.01
example {a b : ℤ} : a + b = b + a := by
  exact add_comm a b


--1.3.02
example {a b : ℤ} (h : a < b) : a + 5 < b + 5 := by
  exact add_lt_add_right h 5


--1.3.03
example {a : ℤ} (h : a = 1) : a = 1 := by
  exact h


--1.3.04
example {a b : ℤ} (h : a + c = b + 0) : a + c = b := by
  rw [add_zero b] at h
  exact h


--1.3.1.01 (incomplete)
example {a b c : ℤ} (h : c = a + b) : a = c - b := by
  sorry

--1.3.1.01 (complete)
example {a b c : ℤ} (h : c = a + b) : a = c - b := by
  -- Substitution of Equals:
  have h1 : c + (-b) = (a + b) + (-b) := by
    congr
  -- Associativity of Addition
  have h2 : c + (-b) = a + (b + (-b)) := by
    rw [add_assoc a b (-b)] at h1
    exact h1
  -- Additive Inverses
  have h3 : c + (-b) = a + 0 := by
    rw [add_right_neg b] at h2
    exact h2
  -- Additive Identity
  have h4 : c + (-b) = a := by
    rw [add_zero a] at h3
    exact h3
  -- Symmetry of equality
  have h5 : a = c + (-b) := by
    symm at h4
    exact h4
  exact h5
