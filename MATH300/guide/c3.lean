import Mathlib.Data.Real.Basic

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


-- temp theorem (delete or modify later)
theorem c3_1 {a b : ℤ} (h1 : Even a) (h2 : Even b) : Even (a + b) := by
  sorry


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


-- 3.4.01 If P is true, then P is true
example {P : Prop} (h : P) : P := by
  by_contra h1
  contradiction
