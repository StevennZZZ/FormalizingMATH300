import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Digits

#print Equivalence

-- 8.0.01 (Theorem 8.1)
-- Congruence modulo m is an equivalence relation.
-- notice: Int.modEq_iff_dvd {n a b : ℤ} : a ≡ b [ZMOD n] ↔ n ∣ b - a
example {n : ℤ} : Equivalence (Int.ModEq n) := by
  -- reflexive
  have refl : ∀ (x : ℤ), (Int.ModEq n) x x := by
    intro a
    rw [Int.modEq_iff_dvd]
    norm_num
  -- symmetric
  have symm : ∀ {x y : ℤ}, (Int.ModEq n) x y → (Int.ModEq n) y x := by
    intro a b h
    rw [Int.modEq_iff_dvd] at h
    rcases h with ⟨k, h⟩
    have h2 : n ∣ a - b := by
      use -k
      linarith
    rw [Int.modEq_iff_dvd]
    exact h2
  -- transitive
  have trans : ∀ {x y z : ℤ}, (Int.ModEq n) x y → (Int.ModEq n) y z → (Int.ModEq n) x z := by
    intro a b c h1 h2
    rw [Int.modEq_iff_dvd] at h1 h2
    rcases h1 with ⟨k1, h1⟩
    rcases h2 with ⟨k2, h2⟩
    rw [Int.modEq_iff_dvd]
    use (k1 + k2)
    linarith
  exact Equivalence.mk refl symm trans


-- 8.0.02 (Theorem 8.2)
-- For any positive integer m, every integer is congruent
-- to exactly one element of the set {0,1,2,...,m − 1}
-- modulo m.
theorem e_t : ∀ m : ℕ, m > 0 → ∃ z ∈ Finset.range m, m ≡ z [ZMOD m] := by
  intros m h
  exists 0
  constructor
  simp
  linarith
  rw [Int.modEq_iff_dvd]
  simp


-- 8.3.01 (Theorem 8.3)
-- Every integer that is the sum of two squares is
-- congruent to 0, 1 or 2 modulo 4.
example (i x y : ℤ) (h : i = x^2 + y^2) : (i ≡ 0 [ZMOD 4]) ∨ (i ≡ 1 [ZMOD 4]) ∨ (i ≡ 2 [ZMOD 4]) := by
  sorry


-- 8.4.01 (Theorem 8.4)
-- Let n be a postive integer and let s be the sum of the
-- digits of n. Then n ≡ s (mod 9).
example (n s : ℕ) (h : s = List.sum (Nat.digits 10 n)) : n ≡ s [ZMOD 9] := by
  sorry
