import Mathlib.Data.Set.Basic

def injective (f : A → B) : Prop :=
∀ (x₁ x₂ : A), f x₁ = f x₂ → x₁ = x₂

def surjective (f : A → B) : Prop :=
∀ (y : B), ∃ (x : A), f x = y
-- 9.8  if A ∩ B = ∅, then f and g are injective if and only if f and g are injective
-- Assume A and B are sets, and f and g are functions from A and B to some set C.
variables {A B C : Type} {f : A → C} {g : B → C}
variable {h : A ∩ B = ∅}

example (h₁ : injective f) (h₂ : injective g) : injective (λ x => if h x then f x else g x) :=
begin
  intros x₁ x₂ h₃,
  cases h x₁;
  cases h x₂;
  simp * at *; cc,
end

example (h₃ : injective (λ x => if h x then f x else g x)) : injective f ∧ injective g :=
begin
  split,
  { intros x₁ x₂ h₄,
    have h₅ := h₃ x₁ x₂,
    cases h x₁;
    cases h x₂;
    simp * at *; cc },
  { intros x₁ x₂ h₄,
    have h₅ := h₃ x₁ x₂,
    cases h x₁;
    cases h x₂;
    simp * at *; cc }
end

example : (injective f) ∧ (injective g) ↔ injective (λ x => if h x then f x else g x) :=
begin
  apply iff.intro,
  { exact λ ⟨hf, hg⟩, by apply_instance },
  { exact λ hf, ⟨by apply_instance, by apply_instance⟩ }
end
