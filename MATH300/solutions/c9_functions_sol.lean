import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic


--9.2. Suppose f : A → C andg : B →C. Prove that if A∩B = ∅,then f ∪ g : (A∪B) → C.

example: (f : A → C) (g : B → C) (h : A ∩ B = ∅) :
  f ∪ g : (A ∪ B) → C :=
begin
  intros x,
  cases x with a b,
  { exact f a },
  { exact g b }
end

--9.4 Let S and T be sets and f : S → T. Definearelation R on S by
 --(a, b) ∈ R ⇔ f(a) = f(b).
 --Prove that R is an equivalence relation
example: (S T : Type) (f : S → T) :
  is_equivalence_relation (λ a b, f a = f b) :=
begin
  intros a b c,
  { reflexivity },
  { symmetry },
  { transitivity }
end

 --9.5. Prove that the identity function is a bijection. That is, let A be a set and define f : A → A by
 --f(x) = x. Prove that f is a bijection.
  example: (A : Type) : bijective (λ x : A, x) :=
  begin
    -- Prove it's injective
    intros x y hxy,
    apply hxy,
    -- Prove it's surjective
    intros y,
    exact y,
  end

--9.6. Let Qpos = {q ∈ Q : q > 0} and Qneg = {q ∈ Q : q < 0}. Prove that the function h : Qpos → Qneg
--defined by h(x) = −xis abijection.
variables {Q : Type} {Qpos Qneg : set Q} (h : Qpos → Qneg) (x : Qpos)

example: (hx : h x = -x) : function.injective h ∧ function.surjective h :=by
  sorry


variables {A B : Type} (f : A → B)


--9.7. Let A and B be sets, and suppose f : A → B is a bijection. Prove that f−1 is a bijection from B to A.
example : function.bijective (function.inv_fun f) := by
  sorry
