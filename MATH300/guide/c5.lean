import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice


-- 5.0.01
#check {x : ℤ | x ≥ 5 ∧ x ≤ 103}


-- 5.0.02
#check 1
#check 1.5
#check (1 : ℝ)


-- 5.0.03
variable (a b : ℤ)
variable (P : Prop)


-- 5.0.04
section
variable (a b : ℤ)
variable (P : Prop)
end


-- 5.0.05
#check ℕ
#check ℝ


-- 5.0.06
section
variable (α : Type)
variable (A : Set α)
end


-- Declare variables of sets for all the problems in this chapter
variable {α : Type} {A B C D : Set α}


-- 5.3.01
example : ∅ ⊆ A := by
  intro x
  intro h
  contradiction


-- 5.3.02 (Theorem 5.1.) Let A, B, C and D be sets.
-- Suppose A ⊆ B and C ⊆ D. Then A ∪ C ⊆ B ∪ D.
example (h1 : A ⊆ B) (h2 : C ⊆ D) : A ∪ C ⊆ B ∪ D := by
  intro x
  intro h3
  cases' h3 with h3 h4
  · have h5 : x ∈ B := by
      exact h1 h3
    left
    exact h5
  · have h6 : x ∈ D := by
      exact h2 h4
    right
    exact h6


-- 5.5.01 (Theorem 5.2.) Let A be a set. Then A \ A = ∅.
example : A \ A = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x
  by_contra h
  cases' h with h1 h2
  contradiction


-- Results from De Morgan's Laws of sets
-- x ∉ A ∪ B ↔ x ∉ A ∧ x ∉ B
theorem notin_union_iff_notin_and_notin {x : α} : x ∉ A ∪ B ↔ x ∉ A ∧ x ∉ B := by
  constructor
  · intro h1
    rw [←Set.mem_compl_iff, Set.compl_union] at h1
    cases' h1 with h1 h2
    rw [Set.mem_compl_iff] at h1
    rw [Set.mem_compl_iff] at h2
    constructor
    · exact h1
    · exact h2
  · intro h3
    rw [←Set.mem_compl_iff, ←Set.mem_compl_iff] at h3
    rw [←Set.mem_compl_iff, Set.compl_union, Set.mem_inter_iff]
    exact h3


-- 5.5.02 (Theorem 5.3.) Let A, B, and C be sets. Then A \ (B ∪ C) = (A \ B) ∩ (A \ C).
example : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  rw [Set.Subset.antisymm_iff]
  constructor
  -- ⊢ A \ (B ∪ C) ⊆ A \ B ∩ (A \ C)
  · intro x
    intro h1
    cases' h1 with h1 h2
    rw [notin_union_iff_notin_and_notin] at h2
    cases' h2 with h2 h3
    have h4 : x ∈ A \ B := by
      constructor
      · exact h1
      · exact h2
    have h5 : x ∈ A \ C := by
      constructor
      · exact h1
      · exact h3
    constructor
    · exact h4
    · exact h5
  -- ⊢ A \ B ∩ (A \ C) ⊆ A \ (B ∪ C)
  · intro x
    intro h1
    cases' h1 with h1 h2
    cases' h1 with h11 h12
    cases' h2 with h21 h22
    constructor
    · exact h11
    · have h3 : x ∉ B ∧ x ∉ C := by
        constructor
        · exact h12
        · exact h22
      rw [notin_union_iff_notin_and_notin]
      exact h3


-- 5.6.01 ∀ A, ∅ ∈ 𝒫(A)
theorem empty_in_pow : ∅ ∈ 𝒫 (A) := by
  rw [Set.mem_powerset_iff]
  intro x h
  contradiction


-- 5.6.02 (Theorem 5.4.) Let A and B be sets. Then 𝒫(A) ⊆ 𝒫(A ∪ B)
example : 𝒫(A) ⊆ 𝒫(A ∪ B) := by
  intro S h1
  rw [Set.mem_powerset_iff] at h1
  have h2 (y : α) (h : y ∈ S) : y ∈ A ∪ B := by
    left
    exact h1 h
  have h3 : S ⊆ A ∪ B := by
    exact h2
  exact (Set.mem_powerset_iff S (A ∪ B)).2 h3


-- 𝒫 A ∩ 𝒫 B = ∅ ∨ ∃ S ∈ 𝒫 A ∩ 𝒫 B, S ≠ ∅
theorem pow_inter_neq_pow_empty (h : 𝒫(A) ∩ 𝒫(B) ≠ {∅}) :
         𝒫 A ∩ 𝒫 B = ∅ ∨ ∃ S ∈ 𝒫 A ∩ 𝒫 B, S ≠ ∅ := by
  rw [← Set.powerset_empty, Ne, Set.Subset.antisymm_iff, not_and_or] at h
  cases' h with h1 h2
  · simp at h1
    rcases h1 with ⟨x, hb, ha, hemp⟩
    simp
    right
    use x
  · absurd h2
    simp


-- {x} ∈ S → S ≠ {∅}
theorem set_in_S_neq_set_empty {x : α} {S : Set (Set α)} (h : {x} ∈ S) : S ≠ {∅} := by
  by_contra h1
  rw [h1] at h
  have h2 : {x} = ∅ := by
    exact Set.eq_of_mem_singleton h
  have h3 : {x} ≠ ∅ := by
    exact Set.singleton_ne_empty x
  contradiction


-- 5.6.03 Theorem 5.5. Let A and B be sets. Then A ∩ B = ∅ if and only if 𝒫(A) ∩ 𝒫(B) = {∅}
-- reverse order
example : A ∩ B = ∅ ↔ 𝒫(A) ∩ 𝒫(B) = {∅} := by
  constructor
  · contrapose!
    intro h1
    have h2 : 𝒫 A ∩ 𝒫 B = ∅ ∨ ∃ S ∈ 𝒫 A ∩ 𝒫 B, S ≠ ∅ := by
      exact pow_inter_neq_pow_empty h1
    cases' h2 with h_contra h2
    · have h4 : ∅ ∈ 𝒫 A ∩ 𝒫 B := by
        constructor
        · exact empty_in_pow
        · exact empty_in_pow
      have h5 : Set.Nonempty (𝒫 A ∩ 𝒫 B) := by
        use ∅
      rw [Set.nonempty_iff_ne_empty] at h5  -- mark
      contradiction
    · cases' h2 with S h2
      cases' h2 with h2 h4
      cases' h2 with h2 h3
      rw [← Set.nonempty_iff_ne_empty, Set.Nonempty] at h4
      cases' h4 with x h5
      have h6 : x ∈ A ∩ B := by
        rw [Set.mem_powerset_iff] at h2
        rw [Set.mem_powerset_iff] at h3
        constructor
        · exact h2 h5
        · exact h3 h5
      use x
  · contrapose!
    intro h1
    rw [Set.Nonempty] at h1
    cases' h1 with x h1
    cases' h1 with h1 h2
    have h3 : {x} ⊆ A := by
      exact Set.singleton_subset_iff.2 h1  -- mark
    have h4 : {x} ⊆ B := by
      exact Set.singleton_subset_iff.2 h2
    have h5 : {x} ≠ ∅ := by
      exact Set.singleton_ne_empty x  -- mark
    rw [← Set.mem_powerset_iff] at h3
    rw [← Set.mem_powerset_iff] at h4
    have h6 : {x} ∈ 𝒫 A ∩ 𝒫 B := by
      constructor
      · exact h3
      · exact h4
    exact set_in_S_neq_set_empty h6


-- 5.6.1.01 (Theorem 5.6.) Let A and B be families.
--                         Then ∪ (A ∩ B) ⊆ (∪ A) ∩ (∪ B)
example (A B : Set (Set α)) : ⋃₀ (A ∩ B) ⊆ (⋃₀ A) ∩ (⋃₀ B) := by
  intro x h1
  rw [Set.mem_sUnion] at h1 -- mark
  cases' h1 with S h2
  cases' h2 with h2 h4
  cases' h2 with h2 h3
  have h4 : x ∈ ⋃₀ A := by
    rw [Set.mem_sUnion]
    use S
  have h5 : x ∈ ⋃₀ B := by
    rw [Set.mem_sUnion]
    use S
  constructor
  · exact h4
  · exact h5
