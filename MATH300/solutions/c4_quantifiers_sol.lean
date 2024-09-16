import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Parity

-- 4.1  for all integers m and n,
--      4 |(m² + n²) if and only if m and n are even.
-- You might need this theorem, which is De Morgan's laws in Lean:
-- theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b
-- Some other theorems about parity that we used in chapter 3 can be helpful
-- e.g. Int.odd_iff_not_even, Int.even_or_odd, etc.

-- Don't panic if the code looks so long! There's lots of copy and paste work,
-- the underlying logic of proving each subgoal is similar

example : ∀ m n : ℤ, 4 ∣ (m^2 + n^2) ↔ Even m ∧ Even n := by
  intro m n
  constructor
  · intro h1
    by_contra h2
    rw [not_and_or, Int.odd_iff_not_even.symm, Int.odd_iff_not_even.symm] at h2
    cases' h2 with h2 h3
    · have h2_1 :Even n ∨ Odd n:= by
        exact Int.even_or_odd n
      cases' h2_1 with h2_1_1 h2_1_2
      · cases' h2 with a hm
        cases' h2_1_1 with b hn
        rw [hm, hn] at h1
        have hab : (2 * a + 1)^2 + (b + b)^2 = 4 * (a ^2 + a + b^2) + 1 :=by
          ring
        rw [hab] at h1
        cases' h1 with k hk
        have h_temp : 4 * k - 4 * (a ^2 + a + b^2) = 1 := by
          linarith
        have h_temp2 : 4 * (k - (a ^2 + a + b^2)) = 1 := by
          linarith
        have h_divides : (4 : ℤ) ∣ 1 := by
          use k - (a ^2 + a + b^2)
          exact h_temp2.symm
        norm_num at h_divides
      · cases' h2 with a hm
        cases' h2_1_2 with b hn
        rw [hm, hn] at h1
        have hab : (2 * a + 1)^2 + (2 * b + 1)^2 = 4 * (a^2 + a + b^2 + b) + 2 := by
          ring
        rw [hab] at h1
        cases' h1 with k hk
        have h_temp : 4 * k - 4 * (a ^2 + a + b^2 + b) = 2 := by
          linarith
        have h_temp2 : 4 * (k - (a ^2 + a + b^2 + b)) = 2 := by
          linarith
        have h_divides : (4 : ℤ) ∣ 2 := by
          use k - (a ^2 + a + b^2 + b)
          exact h_temp2.symm
        norm_num at h_divides
    · have h3_1 :Even m ∨ Odd m:= by
        exact Int.even_or_odd m
      cases' h3_1 with h3_1_1 h3_1_2
      · cases' h3 with a hn
        cases' h3_1_1 with b hm
        rw [hm, hn] at h1
        have hab : (b + b)^2 + (2 * a + 1)^2 = 4 * (a ^2 + a + b^2) + 1 :=by
          ring
        rw [hab] at h1
        cases' h1 with k hk
        have h_temp : 4 * k - 4 * (a ^2 + a + b^2) = 1 := by
          linarith
        have h_temp2 : 4 * (k - (a ^2 + a + b^2)) = 1 := by
          linarith
        have h_divides : (4 : ℤ) ∣ 1 := by
          use k - (a ^2 + a + b^2)
          exact h_temp2.symm
        norm_num at h_divides
      · cases' h3 with a hn
        cases' h3_1_2 with b hm
        rw [hm, hn] at h1
        have hab : (2 * b + 1)^2 + (2 * a + 1)^2 = 4 * (a^2 + a + b^2 + b) + 2 := by
          ring
        rw [hab] at h1
        cases' h1 with k hk
        have h_temp : 4 * k - 4 * (a ^2 + a + b^2 + b) = 2 := by
          linarith
        have h_temp2 : 4 * (k - (a ^2 + a + b^2 + b)) = 2 := by
          linarith
        have h_divides : (4 : ℤ) ∣ 2 := by
          use k - (a ^2 + a + b^2 + b)
          exact h_temp2.symm
        norm_num at h_divides
  · intro h
    cases' h with hm hn
    cases' hm with k hm
    cases' hn with g hn
    have htemp : m^2 + n^2 = 4 * (k^2 + g^2) := by
      rw [hm, hn]
      ring
    use (k^2 + g^2)


-- 4.2  for all integers a, b, and c, with c ≠ 0,
--      a | b if and only if ca | cb.
-- You might need this theorem:
-- theorem mul_left_inj'... (hc : c ≠ 0) : a * c = b * c ↔ a = b
example : ∀ a b c : ℤ, (c ≠ 0) → (a ∣ b ↔ c * a ∣ c * b) := by
  intro a b c h
  constructor
  · intro hab
    cases' hab with k hab
    rw [hab]
    use k
    ring
  · intro hc
    cases' hc with k hc
    use k
    apply (mul_left_inj' h).1
    linarith


-- 4.3 Prove that there exist integers m and n such that
--     2m + 3n = 12.
--     Are these integers unique? (Justify your answer.)
example : ∃ m n, 2 * m + 3 * n = 12 := by
  use 3, 2
  -- These integers aren't unique.
  -- e.g. m = 0, n = 4; m = 3, n = 2.


-- 4.4 Prove that there is no negative integer n
--     such that n² + n < 0.
--     (HINT: Notice that you are proving the negation of:
--      there exists a negative integer n such that
--      n² + n < 0.)
-- You may need this theorem:
-- theorem mul_nonneg_of_nonpos_of_nonpos ...
--         (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b
example : ¬(∃ n : ℤ, n^2 + n < 0) := by
  by_contra h
  cases' h with n h
  have hn : n < 0 ∨ n = 0 ∨ n > 0:= by
    exact lt_trichotomy n 0  -- EPI 8
  rcases hn with h1 | h2 | h3
  · have h1_new : n ≤ 0 := by
      linarith
    have h_n_plus_1 : n + 1 ≤ 0 := by
      linarith
    have h_contra : n * (n + 1) ≥ 0 := by
      exact mul_nonneg_of_nonpos_of_nonpos h1_new h_n_plus_1
    have htemp : n * (n + 1) = n^2 + n := by
      ring
    rw [htemp] at h_contra
    linarith
  · rw [h2] at h
    norm_num at h
  · have h_n_sq : n^2 > 0 := by
      rw [pow_two n]  -- EPI 25
      have htemp : 0 = 0 * n := by
        ring
      rw [htemp]
      exact mul_lt_mul_of_pos_right h3 h3  -- EPI 19
    have h_contra : n^2 + n > 0 := by
      have htemp : (0 : ℤ)  = 0 + 0 := by
        norm_num
      rw [htemp]
      exact add_lt_add h_n_sq h3  -- EPI 21
    linarith


-- 4.5 Prove that, for every integer m, there is a unique
--     integer n such that 5m −n = 8.
-- hint hint: exists_unique_of_exists_of_unique is your friend :)
example : ∀ m : ℤ, ∃! n, 5 * m - n = 8 := by
  intro m
  apply exists_unique_of_exists_of_unique
  · use 5 * m - 8
    ring
  · intro a b ha hb
    have h1 : a = 5 * m - 8 := by
      linarith
    have h2 : b = 5 * m - 8 := by
      linarith
    rw [h1, h2]
