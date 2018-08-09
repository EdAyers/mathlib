
import .category
import .functor
universes u1 u2 v1 v2

namespace category_theory
    section 
        variables 
            {C : Type u1} [𝒞 : category.{u1 v1} C] 
            {D : Type u2} [𝒟 : category.{u2 v2} D]
        include 𝒟 𝒞

        section
        lemma functor_eq : ∀ (F G : C ↝ D) (obj_eq : F.obj = G.obj) (map_eq : (eq.rec_on obj_eq F.map : (Π {X Y : C}, (X ⟶ Y) -> (G.obj X ⟶ G.obj Y))) = G.map), F = G
        | ⟨F_obj, F_map, _, _ ⟩ ⟨ _, _ , _ , _ ⟩ rfl rfl := rfl        
        lemma functor_extensionality : 
            ∀   (F G : C ↝ D) 
                (ob_eq : ∀ (X : C), F.obj X = G.obj X) 
                (map_eq : ∀ (X Y : C) (f : X ⟶ Y), ((eq.rec_on (funext ob_eq : F.obj = G.obj) (F.map)): (Π {X Y}, (X ⟶ Y) -> (G.obj X ⟶ G.obj Y))) f = (G.map f)), F = G
            | F G ob_eq map_eq := functor_eq F G (funext ob_eq) (funext (λ X, funext (λ Y, funext (λ f, map_eq X Y f))))
        end
    end
end category_theory


section
structure str2 :=
    (A : ℕ -> Type)
    (B : Π {a : ℕ} , A a)
lemma str2_ext : ∀ (x y : str2) (A_eq : x.A = y.A) (B_eq : (eq.rec_on A_eq x.B : (Π a : ℕ , y.A a) ) = y.B), x = y
| ⟨xA, xB⟩ ⟨_, _⟩ rfl rfl := rfl
end


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
| ⟨xA, xB, xp⟩ ⟨_, _, _⟩ rfl rfl := rfl

