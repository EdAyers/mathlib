import category_theory.functor

universes u v

namespace category_theory

def Category : Type (max (u+1) (v+1)) := Σ C : Type u, category.{u v} C
instance (𝒞 : Category) : category (𝒞.1) := 𝒞.2

instance CAT : category.{(max (u+1) (v+1)) (max u v)} Category :=
{ Hom     := λ 𝒞 𝒟, 𝒞.1 ↝ 𝒟.1,
  id      := λ 𝒞, (functor.id 𝒞.1),
  comp    := λ _ _ _ F G, F ⋙ G,
  id_comp := λ 𝒞 𝒟, functor.id_comp,
  comp_id := λ 𝒞 𝒟, functor.comp_id,
  assoc   := λ 𝒞1 𝒞2 𝒞3 𝒞4, functor.comp_assoc }

end category_theory