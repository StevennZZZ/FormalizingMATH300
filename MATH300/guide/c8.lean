import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#print Equivalence

-- 8.0.01 (Theorem 8.1)
-- Congruence modulo m is an equivalence relation.
-- (i.e. (a, b) ∈ R if and only if a ≡ b (mod m).)
-- variable {m : ℤ}
-- def r := fun (a b : ℤ) ↦ a ≡ b [ZMOD m]
-- example : Equivalence r :=
