/- I am forcing myself to write out the category theory code again so that I can understand it line-by-line -/
import tactic.restate_axiom
import tactic.interactive
namespace shadow_cats
universes u v
meta def obviously := `[skip]
class category (Ob : Type u) : Type (max u (v+1)) :=
    (Hom : Ob -> Ob -> Type v)
    (id : Π X : Ob, Hom X X)
    (comp : Π {X Y Z : Ob}, Hom X Y -> Hom Y Z -> Hom X Z)
    (id_comp : ∀ {X Y : Ob} (f : Hom X Y), comp (id X) f = f)
    (comp_id : ∀ {X Y : Ob} (f : Hom X Y), comp f (id Y) = f)
    (assoc : ∀ {W X Y Z} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), comp (comp f g) h = comp f (comp g h))
infixr ` >> `:80 := category.comp
infixr ` ⟶ `:10 := category.Hom
notation `𝟙` := category.id
restate_axiom category.id_comp
restate_axiom category.comp_id
restate_axiom category.assoc
attribute [simp, ematch] category.id_comp_lemma category.comp_id_lemma category.assoc_lemma
abbreviation large_category (C : Type (u+1)) : Type (u+1) := category.{u+1 u} C
abbreviation small_category (C : Type u)     : Type (u+1) := category.{u u} C
universes u1 v1 u2 v2 u3 v3 u4 v4
structure functor (C : Type u1) [category.{u1 v1} C] (D : Type u2) [category.{u2 v2} D] : Type (max u1 u2 v1 v2) :=
    (obj : C -> D)
    (map : Π {X Y : C}, (X ⟶ Y) -> ((obj X) ⟶ (obj Y)))
    (map_id : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X))
    (map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map(f >> g) = map(f) >> map(g))
restate_axiom functor.map_id
restate_axiom functor.map_comp
attribute [simp,ematch] functor.map_id_lemma functor.map_comp_lemma
infixr ` &> `:70 := functor.map
infixr ` ~> `:70 := functor
namespace functor
    section --coe stuff, extensionality
        variables 
            {C : Type u1} [𝒞 : category.{u1 v1} C] 
            {D : Type u2} [𝒟 : category.{u2 v2} D]
        include 𝒞 𝒟
        instance : has_coe_to_fun (C ~> D) := {F := λ F, C -> D, coe := λ F, F.obj}
        @[simp] lemma coe_def (F : C ~> D) (X : C) : F X = F.obj X := rfl -- automatically simplify this
    end
    section 
        variables 
            {C : Type u1} [𝒞 : category.{u1 v1} C] 
            {D : Type u2} [𝒟 : category.{u2 v2} D]
        include 𝒟
        include 𝒞
        lemma functor_eq : ∀ (F G : C ~> D) (obj_eq : F.obj = G.obj) (map_eq : (eq.rec_on obj_eq F.map : (Π {X Y : C}, (X ⟶ Y) -> (G.obj X ⟶ G.obj Y))) = G.map), F = G
        | ⟨F_obj, F_map, _, _ ⟩ ⟨ _, _ , _ , _ ⟩ rfl rfl := rfl        
        lemma functor_extensionality : 
            ∀   (F G : C ~> D) 
                (ob_eq : ∀ (X : C), F.obj X = G.obj X) 
                (map_eq : ∀ (X Y : C) (f : X ⟶ Y), ((eq.rec_on (funext ob_eq : F.obj = G.obj) (F.map)): (Π {X Y}, (X ⟶ Y) -> (G.obj X ⟶ G.obj Y))) f = (G.map f)), F = G
            | F G ob_eq map_eq := functor_eq F G (funext ob_eq) (funext (λ X, funext (λ Y, funext (λ f, map_eq X Y f))))
    end
    section -- functor id
        variables (C : Type u1) [𝒞 : category.{u1 v1} C]
        include 𝒞
        protected definition id : C ~> C := { obj := λ X, X,map := λ _ _ f, f, map_id := by simp_intros, map_comp := by simp_intros }
        variable {C}
        @[simp] lemma id_obj (X : C) : (functor.id C) X = X := rfl
        @[simp] lemma id_map {X Y : C} (f : X ⟶ Y) : (functor.id C).map f = f := rfl
    end
    section -- composition
        variables
            {C1 : Type u1} [𝒞1 : category.{u1 v1} C1]
            {C2 : Type u2} [𝒞2 : category.{u2 v2} C2] 
            {C3 : Type u3} [𝒞3 : category.{u3 v3} C3] 
        include 𝒞1 𝒞2 𝒞3
        /--`F >>> G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).-/
        definition comp (F : C1 ~> C2) (G : C2 ~> C3) : C1 ~> C3 := 
        { obj       := λ X, G.obj (F.obj X), 
        map       := λ _ _ f, G.map (F.map f), 
        map_id    := by simp_intros, 
        map_comp  := by simp_intros }
        infixr ` >>> `:80 := comp
        @[simp] lemma comp_obj (F : C1 ~> C2 ) (G : C2  ~> C3) (X : C1) : (F >>> G).obj X = G.obj (F.obj X) := rfl
        @[simp] lemma comp_map (F : C1 ~> C2 ) (G : C2  ~> C3) (X Y : C1) (f : X ⟶ Y) : (F >>> G).map f = G.map (F.map f) := rfl
        section -- comp assoc lemma
            variables {C4 : Type u4} [𝒞4 : category.{u4 v4} C4] 
            include 𝒞4
            lemma comp_assoc (F : C1 ~> C2 ) (G : C2  ~> C3) (H : C3 ~> C4) : (F >>> G) >>> H = F >>> (G >>> H) 
                := by simp [comp]
        end
    end
    section --comp_id and id_comp
        variables 
            {C : Type u1} [𝒞 : category.{u1 v1} C] 
            {D : Type u2} [𝒟 : category.{u2 v2} D]
        include 𝒞 𝒟
        lemma comp_id (F : C ~> D) : F >>> (functor.id D) = F 
        := by cases F;dsimp [comp, functor.id];congr
        lemma id_comp (F : C ~> D) : (functor.id C) >>> F = F 
        := by cases F; dsimp [comp, functor.id]; congr
    end


end functor
end shadow_cats