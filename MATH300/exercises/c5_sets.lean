import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

section -- 5.1 Prove that, for any sets A and B:
variable {α : Type*}
variable (A B : Set α)

-- 5.1 (a) A ∩ B ⊆ A
example : A ∩ B ⊆ A := by
  sorry

-- 5.1 (b) A ⊆ A ∪ B
example : A ⊆ A ∪ B := by
  sorry

end -- 5.1


-- 5.2 Let A = {n ∈ Z : 18 ∣ n}, B = {n ∈ Z : 3 ∣ n},
--     and C = {n ∈ Z : 2 ∣ n}. Prove that A ⊆ B ∩ C.
example (ha : A = {n : ℤ | 18 ∣ n})
        (hb : B = {n : ℤ | 3 ∣ n})
        (hc : C = {n : ℤ | 2 ∣ n}) :
        A ⊆ B ∩ C := by
  sorry

-- 5.3 Let A = {n ∈ Z : n = 4k + 1 for some k ∈ Z}
--     and B = {n ∈ Z : n = 4k − 3 for some k ∈ Z}.
--     Prove that A = B.
example (ha : A = {n : ℤ | 4 ∣ (n - 1)})
        (hb : B = {n : ℤ | 4 ∣ (n + 3)})
        : A = B := by
  sorry

-- 5.4 skip

section -- 5.5 Let A and B be sets.
--         Prove the following facts.
variable {α : Type*}
variable (A B : Set α)

-- 5.5 (a) A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A)
example : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  sorry

-- 5.5 (b) The sets A \ B, A ∩ B and B \ A are pairwise
-- disjoint (i.e., the intersection of any pair of them
-- is empty (so you have three things to prove here)).
example : (A \ B) ∩ (A ∩ B) = ∅ := by
  sorry
example : (A \ B) ∩ (B \ A) = ∅ := by
  sorry
example : (A ∩ B) ∩ (B \ A) = ∅ := by
  sorry

end -- 5.5

-- 5.6 skip

-- 5.7 Prove the following theorem:
--     Let A and B be sets. Then A \ (A ∩ B) = A \ B.
example {α : Type*} (A B : Set α) :
        A \ (A ∩ B) = A \ B := by
  sorry

-- 5.8 Prove the following theorem: Let A, B and C be sets.
--     Then (A \ C) ∩ (B \ C) = (A ∩ B) \ C.
example {α : Type*} (A B C: Set α) :
        (A \ C) ∩ (B \ C) = (A ∩ B) \ C := by
  sorry

-- 5.9 Let A, B, and C be sets.
--     Prove that (A ∪ C) ∩ B ⊆ A ∪ (B ∩ C).
example {α : Type*} (A B C: Set α) :
        (A ∪ C) ∩ B ⊆ A ∪ (B ∩ C) := by
  sorry

-- 5.10 Let A, B, and C be sets. Suppose A ∪ C ⊆ B ∪ C.
--      Prove that A \ C ⊆ B.
example {α : Type*} (A B C: Set α) (h : A ∪ C ⊆ B ∪ C) :
        A \ C ⊆ B := by
  sorry

-- 5.11 skip

section -- 5.12 Let A and B be sets.
--         Prove each of the following.
variable {α : Type*}
variable (A B : Set α)

-- 5.12 (a) A ⊆ B if and only if 𝒫(A) ⊆ 𝒫(B).
example : A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B := by
  sorry

-- 5.12 (b) 𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B)
example : 𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B) := by
  sorry

-- 5.12 (c) 𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B)
example : 𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B) := by
  sorry

-- 5.12 (d) There exist sets A and B such that
--          𝒫(A ∪ B) ⊈ 𝒫(A) ∪ 𝒫(B).
example : ∃ A B : Set α, ¬(𝒫(A ∪ B) ⊆ 𝒫(A) ∪ 𝒫(B)) := by
  sorry

-- 5.12 (e) 𝒫(A) ∪ 𝒫(B) = 𝒫(A ∪ B)
--          if and only if A ⊆ B or B ⊆ A.
example : 𝒫(A) ∪ 𝒫(B) = 𝒫(A ∪ B) ↔ A ⊆ B ∨ B ⊆ A := by
  sorry

-- 5.13 - 5.18 skip (family sets)
variable {α : Type*}
variable (A B : Set α)
variable (F G : Set (Set α))
-- 5.13
example :
   ⋃ (x ∈ F ∪ G), x = (⋃ x ∈ F, x) ∪ (⋃ y ∈ G, y) := by
  sorry
