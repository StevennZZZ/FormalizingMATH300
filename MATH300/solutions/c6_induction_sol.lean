import Mathlib.Data.Real.Basic

-- 6.1 Prove: If a is a non-negative integer,
--            then aⁿ ≥ 0 for all n ∈ N.
example {a : ℤ} (h : a ≥ 0) : ∀ n : ℕ, a^n ≥ 0 := by
  sorry
