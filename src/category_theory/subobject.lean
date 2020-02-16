import .category order ..order.galois_connection ..order.complete_lattice ..data.set
import category_theory.whiskering
import category_theory.opposites
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.pullbacks
import category_theory.epi_mono
import category_theory.category.Cat
import category_theory.yoneda
universes u v w

namespace category_theory

/-- The subobject category -/
structure sub (C : Type u) [𝒞 : category.{v} C] (X : C) :=
(A : C)
(f : A ⟶ X)
(hf : @mono C 𝒞 _ _ f)

/-- sub is a cateogry. -/
instance sub.is_cat {C : Type u} [𝒞 : category.{v} C] {X : C} : category (@sub C 𝒞 X) :=
{  hom := λ A B, {h : A.A ⟶ B.A // h ≫ B.f = A.f}
,  id  := λ A, ⟨𝟙 A.A, by simp⟩
, comp :=
  λ A B C a b, subtype.mk ((subtype.val a) ≫ b.val) (begin
    cases b, cases a, dsimp at *, simp [b_property, a_property] at *,
  end)
, assoc' := begin rintros ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩, simp  end
, id_comp' := begin rintros ⟨A,a,_⟩ ⟨B,b,_⟩ ⟨f,_⟩, apply subtype.ext.2, dsimp,  simp end
, comp_id' := begin rintros ⟨A,a,_⟩ ⟨B,b,_⟩ ⟨f,_⟩, apply subtype.ext.2, dsimp, simp end
}

@[simp] lemma sub_id {C : Type u} [𝒞 : category.{v} C] {X : C} {A : sub C X}: subtype.val (𝟙 A) = 𝟙 A.A := by refl
@[simp] lemma sub_id2 {C : Type u} [𝒞 : category.{v} C] {X : C} {A : sub C X}: ↑(𝟙 A) = 𝟙 A.A := by refl
@[simp] lemma sub_comp {C : Type u} [𝒞 : category.{v} C] {X : C} {A B D : sub C X} {f : A ⟶ B} {g : B ⟶ D}: subtype.val (f ≫ g) = f.val ≫ g.val := by refl

open category_theory.limits
open opposite

/-- Pullback of a monic is monic. -/
lemma pullback_mono {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞]
  {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (hm : @mono _ 𝒞 _ _ f) : @mono C 𝒞 (pullback f g) _ (pullback.snd) :=
begin
  split, intros A a b e,
  have c : pullback.fst ≫ f = pullback.snd ≫ g, apply pullback.condition,
  apply pullback_hom_ext,
    show a ≫ pullback.fst = b ≫ pullback.fst,
    apply hm.1, simp,
    rw c, rw ← category.assoc,  rw e, simp,
  show a ≫ pullback.snd = b ≫ pullback.snd, assumption,
end

/-- Each Y ⟶ X induces a functor between the subobject categories by taking a pullback. -/
def SUB_map {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] {X Y : C} (YX : Y ⟶ X) : (sub C X) ⥤ (sub C Y) :=
begin
refine functor.mk
  (λ A : sub _ _, sub.mk (pullback A.f YX) (pullback.snd)(pullback_mono A.hf))
  (λ A B g, subtype.mk (pullback.lift (pullback.fst ≫ g) pullback.snd _) _) _ _,
show (pullback.fst ≫ g.val) ≫ B.f = pullback.snd ≫ YX,
  cases g, simp, rw g_property, rw pullback.condition,
show pullback.lift (pullback.fst ≫ g.val) pullback.snd _ ≫ pullback.snd = pullback.snd,
  cases g, simp,
rintro ⟨A,AX,mAX⟩, apply subtype.ext.2,
show pullback.lift (pullback.fst ≫ 𝟙 A) pullback.snd _ = 𝟙 (pullback AX YX),
  simp,
rintro I J K ij jk, apply subtype.ext.2,
show pullback.lift (pullback.fst ≫ ↑(ij ≫ jk)) pullback.snd _ = pullback.lift (pullback.fst ≫ ↑ij) pullback.snd _ ≫ pullback.lift (pullback.fst ≫ ↑jk) pullback.snd _,
  -- [todo]
  sorry
end

/-- sub is a functor -/
def SUB (C : Type u) [𝒞 : category.{v} C] [@has_pullbacks C 𝒞]: functor Cᵒᵖ Cat :=
{ obj := λ (X : Cᵒᵖ), bundled.mk (@sub C 𝒞 (unop X)) (begin apply sub.is_cat end)
, map := λ X Y f, SUB_map f.unop,
, map_id := _
, map_comp := _
}

class has_subobject_classifier (C : Type u) [𝒞 : category.{v} C] [@has_finite_limits C 𝒞] :=
(Ω : C)
(magic_equiv : SUB C ≅ yoneda Ω)

open category_theory.limits

end category_theory
