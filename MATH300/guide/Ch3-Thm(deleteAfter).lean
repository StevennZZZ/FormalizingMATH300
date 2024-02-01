import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Parity

/-Theorems 3.1: If a and b are even integers, then a + b is even.-/
/-page 22-/
example (a b : ℤ) : (Even a) ∧ (Even b) →  Even (a + b) := by
  unfold Even
  rintro ⟨h1, h2⟩
  cases' h1 with r1 hr1
  cases' h2 with r2 hr2
  use r1 + r2
  rw [hr1]
  rw [hr2]
  exact add_add_add_comm r1 r1 r2 r2

/-Theorems3.2: Suppose a, b, and c are integers. If a|b and b|c, then a|c.
  page 23-/
example (a b c : ℤ) : (a∣b) ∧ (b∣c) → (a∣c) := by
  rintro⟨h1,h2⟩
  cases' h1 with k₁ h₁
  cases' h2 with k₂ h₂
  use k₁*k₂
  rw [h₂, h₁]
  rw [mul_assoc]

--Theorems 3.3: The product of two consecutive integers is even.-/
--page 23
example (a b : ℤ) : (b = a + 1) → Even (a * b)  := by
  intro h1
  have h2 : Even a ∨ Odd a := by exact Int.even_or_odd a
  cases' h2 with h3 h4
  · rw[h1]
    cases' h3 with k h3
    use (k * (2 * k + 1))
    rw[h3]
    ring




/-
Theorem 3.4 (Elementary Properties of Absolute Value). Suppose a and b are integers. Then:
(a) |a| ≥ 0.
(b) | − a| = |a|.
(c) −|a| ≤ a ≤ |a|.
(d) |a|^2 = a^2.
(e) |ab| = |a||b|.
(f) |a| ≤ |b| if and only if −|b| ≤ a ≤ |b|.
-/
/-page 24-/
  /-(a)-/
  example (a : ℤ ) : |a| ≥ 0 := by


  /-(b)-/
  example (a : ℤ ) : |-a| = |a| := by
    norm_num

  /-(c)-/
  example (a : ℤ ) : -|a| ≤ a ∧ a ≤ |a| := by
    sorry

  /-(d)-/
  example (a : ℤ ) : |a|^2 = a^2 := by
    norm_num

  /-(e)-/
  example (a b : ℤ ) : |a * b| = |a| * |b| := by
    ring_nf

  /-(f)-/
  example (a b : ℤ ) : ((|a| ≤ |b|) → (-|b| ≤ a ≤ |b|)) ∧ ((-|b| ≤ a ≤ |b|) → (|a| ≤ |b|)) := by
    sorry

/-Theorem 3.5 (The Triangle Inequality)-/
example (a b: ℤ ) : |a + b|  ≤ |a|  + |b| := by
  sorry

/-Theorem 3.6: Suppose n is an integer. If n^2 is even, then n is even-/
example (n : ℤ ) : Even (n^2) → Even (n) := by
  contrapose!
  intro h
  rw [← Int.odd_iff_not_even]
  rw [← Int.odd_iff_not_even] at h
  cases' h with k h
  use (2*k^2+2*k)
  rw[h]
  ring




/-Theorem 3.7: Let n be an integer. If n^2 + 2n < 0, then n < 0-/
example (n : ℤ ) : ((n^2 + 2*n) < 0) → n < 0 := by
  contrapose!
  intro h1
  have h2 : 0 ≤ n^2 := by
    exact sq_nonneg n
  have h3 : 0 ≤ n + n := by
    exact add_le_add h1 h1
  have h4 : n + n = 2*n := by
    ring
  rw[h4] at h3
  exact add_le_add h2 h3


/-Theorem 3.8: No integer is both even and odd-/
example (a : ℤ ) : ¬ (Even a ∧ Odd a ) := by
  intro h
  cases' h with h1 h2
  rw[Int.odd_iff_not_even] at h2
  contradiction


/-Theorem 3.9 : √2 is irrational.-/
/-(I am not sure about this.)-/
example (a, b : ℤ ) : ¬(√2 = a/b) :=by
  sorry

/-Theorem 3.10 : Let a be an integer. If a^2 is odd, then a is odd-/
example (a : ℤ ) : Odd (a^2) → Odd (a) := by
  contrapose!
  intro h
  rw [← Int.even_iff_not_odd]
  rw [← Int.even_iff_not_odd] at h
  cases' h with k h
  use (2*k^2)
  rw[h]
  ring

/-Theorem 3.11 : Let a be an integer. Then a is odd if and only if a^2-1 is even-/
example (a : ℤ ) : (Odd a → Even (a^2 - 1)) ∧ (Even (a^2 - 1) → Odd a) := by
  constructor
  · intro h1
    cases' h1 with k h1
    use (2*k^2+2*k)
    rw[h1]
    ring
  · contrapose!
    intro h2
    rw [← Int.even_iff_not_odd] at h2
    rw [← Int.odd_iff_not_even]
    cases' h2 with k h2
    use (2*k^2 - 1)
    rw[h2]
    ring


/-Theorem 4.1 : Let a, b, and c be integers and suppose that c|a and c|b. For all integers n and m, c|(an + bm)-/
example (a b c : ℤ ) :
