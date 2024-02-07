import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

section -- 7.1 For any sets A, B, and C:

variable {α : Type*}
variable (A B C : Set α)
variable (a b c : α)

#check a ∈ A
#check A × B

-- 7.0.1 A × B = {(a, b) : a ∈ {1, 2, 3}, b ∈ {4, 5}}
--             = {(1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)}.

--example {A : ℕ} (h1 : A = {1, 2, 3}) (h2 : B = {4, 5}) : [A × B] = {(1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)} := by
-- sorry

-- 7.1.1
#check ℝ × ℝ

-- 7.1.2
#check [ℤ × ℤ] ⊆ [ℝ × ℝ]
