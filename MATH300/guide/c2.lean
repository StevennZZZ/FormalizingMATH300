import Mathlib.Data.Real.Basic

-- 2.1.01
#eval 10 > 5
#eval ¬(10 > 5)


-- 2.2.01
#eval (1 + 1 = 2) ∧ (2 = 0)
#eval (1 + 1 = 2) ∨ (2 = 0)


-- 2.2.02
example {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq


-- 2.2.03
example {P Q : Prop} (h : P) : P ∨ Q := by
  left
  exact h


-- 2.2.04
example {P Q : Prop} (h : Q) : P ∨ Q := by
  right
  exact h


-- 2.2.05
example {P Q : Prop} (h : P ∧ Q) : P := by
  cases' h with hp hq
  exact hp


-- 2.2.06
example {P Q : Prop} (h : P ∨ Q) : P ∨ Q := by
  cases' h with hp hq
  · left
    exact hp
  · right
    exact hq


-- 2.3.01
#eval 10 < 5 → 3 = 4


-- 2.3.02 (a)
example {x : ℝ} (h : x = 2) : x^2 = 4 := by
  rw [h]
  norm_num


-- 2.3.02 (b)
example {x : ℝ} : x = 2 → x^2 = 4 := by
  intro h
  rw [h]
  norm_num


-- 2.3.03
example {P Q : Prop} (h1 : P) (h2 : P → Q) : Q := by
  apply h2
  exact h1


-- 2.3.1.01
example {P Q : Prop} (h : P → Q) : ¬Q → ¬P := by
  contrapose!
  exact h


-- 2.3.2.01
example {P Q : Prop} (h1 :  P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · exact h1
  · exact h2


-- 2.4.01 (a)
example : ∃ n : ℝ, |n| > 0 := by
  use 1
  norm_num


-- 2.4.01 (b)
example : ∃ n : ℝ, |n| > 0 := by
  use -1
  norm_num


-- 2.4.02
example : ∀ n : ℝ, |n| ≥ 0 := by
  intro n
  norm_num


-- 2.4.03
example {n : ℤ} (h : Even n) : Odd (n + 1) := by
  cases' h with k newh
  use k
  rw [newh]
  ring
