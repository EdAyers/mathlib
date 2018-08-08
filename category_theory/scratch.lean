
import .category
import .functor
universes u1 u2 v1 v2

namespace category_theory
    section 
        variables 
            {C : Type u1} [𝒞 : category.{u1 v1} C] 
            {D : Type u2} [𝒟 : category.{u2 v2} D]
        include 𝒟 𝒞
        def functor_extensionality 
            (F G : C ↝ D) 
            (ob_eq : ∀ (X : C), F X = G X) 
            (map_eq : ∀ {X Y : C} (f : X ⟶ Y), (eq.rec_on (ob_eq Y) (eq.rec_on (ob_eq X) (F.map f)) : G X ⟶ G Y) = (G.map f)) 
            : F = G :=
            begin
                cases F,
                cases G,
                sorry
            end
    end
end category_theory


lemma my_ext (α :Type)
  (P Q : α -> Type)
  (f : Π (a : α), P a )
  (g : Π (a : α), Q a)
  (p : ∀ (a : α), P a = Q a) :
    (∀ (a : α), (eq.rec_on (p a) (f a) : Q a) = g a)
    -> (eq.rec_on (funext p : P = Q) f : Π (a : α), Q a) = g :=
begin
  cases (funext p : P = Q), 
  exact funext
end

#check heq

structure mystr :=
    (A : ℕ)
    (B : bool)
    (p : A > 10)

theorem mystr_eq : ∀ (x y : mystr) (A_eq : x.A = y.A) (B_eq : x.B = y.B), x = y
| ⟨xA, xB, xp⟩ ⟨_, _, _⟩ rfl rfl := by sorry


