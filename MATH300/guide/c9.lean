import Mathlib.Data.Set.Function

-- Declare variables of sets for all the problems in this chapter
variable {α : Type} {A B C D : Set α}

section -- 9.1.01 (Theorem 9.1.)
--  Let A, B and C be sets, f : A → B and g : B → C.
--  Then g ◦ f is a function from A to C.
variable (f : A → B) (g : B → C)
#check g ∘ f
