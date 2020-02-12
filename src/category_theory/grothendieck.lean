import .category order ..order.galois_connection ..order.complete_lattice ..data.set
import category_theory.whiskering
import category_theory.opposites

namespace category_theory
universes u v w
variables {C : Type u}

def slice (C : Type u) [category.{v} C] (X : C) := Σ Y, Y ⟶ X
variables [𝒞 : category.{v} C]
include 𝒞
@[reducible]
def slice.mk {X : C} {Y : C} (f : Y ⟶ X) : slice C X := sigma.mk Y f
def slice.fst {X : C} : slice C X → C := sigma.fst
@[simp] lemma slice.mk_fst (X Y : C) (f : Y ⟶ X) : (slice.mk f).fst = Y := rfl
@[simp] lemma slice.mk_snd (X Y : C) (f : Y ⟶ X) : (slice.mk f).snd = f := rfl
@[simp] lemma slice.fml_snd (X Y : C) (f : Y ⟶ X) : (⟨Y,f⟩ : slice C X).snd = f := rfl

structure sieve (X : C) :=
(arrows : set (slice C X))
(subs : Π (f : slice C X) (_ : f ∈ arrows) (Z : C) (g : Z ⟶ f.1), (slice.mk (g ≫ f.2)) ∈ arrows)
variable {X : C}
instance {Y : C}: has_mem (Y ⟶ X) (@sieve C 𝒞 X) := ⟨λ f S, slice.mk f ∈ S.arrows⟩
namespace sieve
instance : has_subset (@sieve C 𝒞 X) := ⟨λ S R, S.arrows ⊆ R.arrows⟩
@[ext] def sieve.extensionality : Π {R S : @sieve C 𝒞 X}, R.arrows = S.arrows → R = S
|⟨Ra,_⟩ ⟨Sa, _⟩ rfl := rfl
instance has_po : partial_order (@sieve C 𝒞 X) := {partial_order.
le := λ S R, S.arrows ⊆ R.arrows
, le_refl := λ S, set.subset.refl _
, le_trans := λ S R T, set.subset.trans
, le_antisymm := begin intros S R p q, apply sieve.extensionality, apply set.subset.antisymm; assumption end
}
instance : preorder (@sieve C 𝒞 X) := by apply_instance
def max_sieve : @sieve C 𝒞 X :=
{arrows := set.univ, subs := λ a aa Z g, ⟨⟩}
def sieve.union (S R : @sieve C 𝒞 X) : @sieve C 𝒞 X :=
{ arrows := S.arrows ∪ R.arrows, subs :=
begin
  rintros ⟨Z,f⟩ c Y g,cases c,
    left, apply sieve.subs, assumption,
    right, apply sieve.subs, assumption
end
}
instance : has_union (@sieve C 𝒞 X) := ⟨sieve.union⟩

inductive generate_sets {X : C} (𝒢 : set (slice C X)) : slice C X → Prop
|basic : Π {f : slice C X}, f ∈ 𝒢 → generate_sets f
|subs  : Π {f : slice C X} {Y} (g : Y ⟶ f.1), generate_sets f → generate_sets (slice.mk $ g ≫ f.2)
def generate {X : C} (𝒢 : set (slice C X)) : @sieve C 𝒞 X :=
{ arrows := generate_sets 𝒢
, subs := λ f h Z g, generate_sets.subs _ h
}
lemma sets_iff_generate {𝒢 : set (slice C X)} {S : @sieve C 𝒞 X} : generate 𝒢 ≤ S ↔ 𝒢 ⊆ S.arrows
:= iff.intro
    (λ H _ H2, H $ generate_sets.basic H2 )
    (λ ss g f, begin induction f, apply ss f_a, apply sieve.subs, apply f_ih end)

open order lattice
def gi_generate  :
  @galois_insertion (set (slice C X)) (@sieve C 𝒞 X) (by apply_instance) _ generate sieve.arrows :=
  {gc := λ s f, sets_iff_generate
  , choice := λ 𝒢 f, generate 𝒢
  , choice_eq := λ 𝒢 h, rfl
  , le_l_u := λ S ⟨Z,f⟩, generate_sets.basic
  }

private def original_complete_lattice : complete_lattice (@sieve C 𝒞 X) :=
(gi_generate).lift_complete_lattice
instance : complete_lattice (@sieve C 𝒞 X) := original_complete_lattice

def empty_sieve (X : C) : @sieve C 𝒞 X :=
{arrows := ∅, subs := λ a aa Z g, false.rec_on _ aa }
def empty_is_bot : empty_sieve X = ⊥ :=
begin
  ext, split, intro, cases a,
  intro h, induction h, refine false.rec_on _ h_a, apply h_ih
end
def max_is_top : @max_sieve _ _ X = ⊤ :=
begin
  suffices : ⊤ ≤ @max_sieve _ _ X,
    apply eq.symm, apply antisymm this, apply @le_top _ _ _,
  rintros ⟨Z,f⟩ h, refine ⟨⟩
end
def all_in_top {f : slice C X} : f ∈ (⊤ : @sieve C 𝒞 X).arrows := begin rw ← max_is_top, trivial end
def union_is_sup (R S : @sieve C 𝒞 X) : R ∪ S = R ⊔ S :=
begin
  have r : R ⊔ S ≤ R ∪ S, apply sup_le _ _, apply set.subset_union_left, apply set.subset_union_right,
  have l : R ∪ S ≤ R ⊔ S, apply set.union_subset, apply @le_sup_left _ _ R S, apply @le_sup_right _ _ R S,
  apply antisymm l r
end
open lattice

def yank {X Y : C} (S : @sieve C 𝒞 X) (h : Y ⟶ X) :  @sieve C 𝒞 Y :=
{ arrows := {sl | (slice.mk $ sl.2 ≫ h) ∈ S.arrows }
, subs := begin
  intros, suffices : slice.mk ((g ≫ f.snd) ≫ h) ∈ S.arrows, by apply this,
  let j := slice.mk (f.snd ≫ h),
  have jS : j ∈ S.arrows, from _x,
  suffices : slice.mk (g ≫ j.snd) ∈ S.arrows, simp, apply this,
  apply sieve.subs S j jS,
end
}
variables {Y : C} {S : @sieve C 𝒞 X}
@[simp] lemma yank_def (h : Y ⟶ X) {Z : C} {f : Z ⟶ Y}
: ((slice.mk f) ∈ (yank S h).arrows) = ((slice.mk $ f ≫ h) ∈ S.arrows) := rfl
def yank_le_map
    {X Y} {S R : @sieve C 𝒞 X} (Hss : S ≤ R) (f : Y ⟶ X) : yank S f ≤ yank R f
:= begin rintros ⟨Z,g⟩ H, apply Hss, apply H end
lemma yank_top {f : Y ⟶ X} : yank ⊤ f = ⊤ :=
begin  apply top_unique, rintros g Hg, apply all_in_top end
def has_id_max {X} {S : @sieve C 𝒞 X} : slice.mk (𝟙 _) ∈ S.arrows → S = ⊤ :=
begin
  intro h,
  apply top_unique,
  rintros ⟨Z,f⟩ _,
  rw ← category.comp_id C f,
  refine @sieve.subs _ _ _ S ⟨_,𝟙 _⟩ _ _ _,
  apply h
end

def sieve_set (C : Type u) [𝒞 : category.{v} C] :=  Π (X : C), set (@sieve C 𝒞 X)

def comp {Y : C} (R : @sieve C 𝒞 Y) (f : Y ⟶ X) : @sieve C 𝒞 X :=
{ arrows := λ gf, ∃ (g : gf.1 ⟶ Y) (_:slice.mk g ∈ R.arrows), gf.2 = g ≫ f
, subs := begin
  rintros ⟨Z,g⟩ ⟨j,ir,e⟩ W h, refine ⟨h ≫ j,_,_⟩, refine sieve.subs R ⟨_,_⟩ ir _ _,
  simp, simp at e, rw e
end
}

def le_yank_comp {R : @sieve C 𝒞 Y} {f : Y ⟶ X}
: R ≤ yank (comp R f) f :=
begin rintros ⟨Z,g⟩ b, refine ⟨g,b,rfl⟩ end

def comps
  (R : Π (f : slice C X), @sieve C 𝒞 f.1)
  (S : @sieve C 𝒞 X) : @sieve C 𝒞 X :=
  ⨆ (f ∈ S.arrows), comp (R f) f.2

def comp_le_comps
  (R : Π (f : slice C X), @sieve C 𝒞 f.1)
  (S : @sieve C 𝒞 X)
  (f ∈ S.arrows) :
  comp (R f) f.2 ≤ comps R S
  :=
  begin
    refine calc comp (R f) f.2 = _ : _ ... ≤  ⨆ (H : f ∈ S.arrows), comp (R f) f.2 : _
      ... ≤  ⨆ (f ∈ S.arrows), comp (R f) f.2 : _,
      rotate 2,
      refine lattice.le_supr _ H,
      refine lattice.le_supr _ f,
      reflexivity
   end

def comps_ss_S
  (R : Π (f : slice C X), @sieve C 𝒞 f.1)
  (S : @sieve C 𝒞 X) :
  comps R S ≤ S :=
begin
  apply lattice.supr_le _,
  rintros ⟨Z,f⟩,
  apply lattice.supr_le _,
  rintros H ⟨Y,g⟩ ⟨a,b,e⟩,
  simp at *,
  rw e,
  apply sieve.subs, apply H,
end

end sieve
open sieve

/-- Definition of a Grothendiek Topology. [todo] consider bundling. -/
class grothendieck (J : sieve_set C) :=
(max : ∀ X, ⊤ ∈ J(X))
(stab : ∀ (X Y : C) (S ∈ J(X)) (h : Y ⟶ X), yank S h ∈ J(Y))
(trans :
  ∀ ⦃X : C⦄
    (S ∈ J(X))
    (R : sieve X)
    (_ : ∀ (f : slice C X)
           (_ : f ∈ @sieve.arrows C 𝒞 X S),
         yank R f.2 ∈ J(f.1)),
    R ∈ J(X)
)
variables {J : sieve_set C} [grothendieck J]

def superset_covers {C : Type u} [𝒞 : category.{v} C]
    {J : sieve_set C} [grothendieck J]
    {X} {S R : @sieve C 𝒞 X} (Hss : S ⊆ R) (sjx : S ∈ J(X)) : (R ∈ J(X))
:= begin
  apply grothendieck.trans,
  apply sjx,
  rintros ⟨Z,h⟩ H2,
  have : slice.mk (𝟙 Z) ∈ (yank R h).arrows, apply Hss, simp, apply H2,
  have : yank R h = ⊤,  apply has_id_max this,
  rw this,
  apply grothendieck.max
end

def trans2
  (X : C)
  (S : @sieve C 𝒞 X)
  (sjx : S ∈ J(X))
  (R : Π (f : slice C X), @sieve C 𝒞 (slice.fst f))
  (hR : Π f (H:f ∈ S.arrows), (R f) ∈ J(f.1))
  : comps R S ∈ J(X) :=
  begin
    apply grothendieck.trans,
    apply sjx,
    rintros f Hf,
    apply superset_covers,
    apply yank_le_map,
    apply comp_le_comps,
    apply Hf,
    apply superset_covers,
    apply le_yank_comp,
    apply hR,
    apply Hf,
  end

structure Site :=
(C : Type u)
[𝒞 : category.{v} C]
(J : sieve_set C)
[g : @grothendieck C 𝒞 J]

def covers {Y:C} (J : sieve_set C) (S : @sieve C 𝒞 X) (f : Y ⟶ X) := yank S f ∈ J(Y)

lemma intersection_covers (R S ∈ J(X)) : R ⊓ S ∈ J(X) :=
begin
  apply grothendieck.trans R, assumption,
  intros f Hf,
  have r : yank (R⊓S) f.2 ≥ yank S f.2,
    rintros ⟨Z,g⟩ Hg,
    apply sieve.generate_sets.basic,
    split,
      apply sieve.subs, assumption,
    apply Hg,
  apply superset_covers,
  apply r,
  apply grothendieck.stab,
  assumption, assumption,
end

def sieve_set.trivial (C : Type u) [𝒞 : category.{v} C] : sieve_set C := λ X, {⊤}
instance trivial.grothendieck : grothendieck (sieve_set.trivial C) :=
{ max := λ X, set.mem_singleton _
, stab := λ X Y S HS h , begin have : S = ⊤, apply set.eq_of_mem_singleton, assumption, rw [this, yank_top], apply set.mem_singleton end
, trans := λ X S HS R HR, begin
  have : S = ⊤, apply set.eq_of_mem_singleton, assumption, subst this,
  apply set.mem_singleton_of_eq,
  apply lattice.top_unique,
  rintros ⟨Z,g⟩ Hg,
  have H, refine (ge_of_eq (set.eq_of_mem_singleton (HR _ Hg))),
  have H₂, refine H all_in_top, apply slice.mk (𝟙 _),
  simp at H₂,
  apply H₂,
  end
}

def dense (C : Type u) [𝒞 : category.{v} C] : sieve_set C :=
λ X, {S| ∀ {Y : C} (f : Y ⟶ X), ∃ (Z) (g : Z ⟶ Y), (slice.mk (g ≫ f)) ∈ S.arrows }

instance dense.grothendieck : grothendieck (dense C) :=
{ max := λ X Y f, ⟨Y,𝟙 Y, all_in_top⟩
, stab :=
    begin
      intros X Y S H h Z f,
      rcases H (f ≫ h) with ⟨W,g,H⟩,
      refine ⟨W,g,_⟩,
      simp, apply H
    end
, trans :=
    begin intros X S H₁ R H₂ Y f,
      rcases H₁ f with ⟨Z,g,H₃⟩,
      rcases H₂ _ H₃ (𝟙 Z) with ⟨W,h,H₄⟩,
      -- have y, refine , cases y with W y, cases y with h H₄,
      refine ⟨W,(h ≫ (𝟙 Z) ≫ g), _⟩,
      simp [dense] at *,
      apply H₄
    end
}

/-- The atomic sieveset just contains all of the non-empty sieves. -/
def atomic (C : Type u) [𝒞 : category.{v} C] : sieve_set C :=
λ X, {S | ∃ x, x ∈ S.arrows}

/-- The atomic sieveset is a grothendieck topology when it is inhabited and
satisfies the 'square' property. Which says that every span `Y ⟶ X ⟵ Z` forms a commuting
diagram.
-/
instance atomic.grothendieck
  (square :
    ∀ {X Y Z : C}
      (yx : Y ⟶ X)
      (zx : Z ⟶ X),
      ∃ (W : C) (wy : W ⟶ Y) (wz : W ⟶ Z),
      wy ≫ yx = wz ≫ zx)
    (inh : ∀ (X : C), inhabited (slice C X))
      : grothendieck (atomic C)
       :=
{ max := λ X, begin
    refine ⟨_,_⟩,
    apply inhabited.default,
    rw [←max_is_top],
    trivial
  end
, stab := begin
    rintros X Y S HS h,
    cases HS with f HS,
    rcases square h f.2 with ⟨a,b,c,d⟩,
    refine ⟨⟨_,b⟩,_⟩,
    simp, rw d,
    apply sieve.subs, assumption
   end
, trans := begin
    rintros _ _ ⟨f,fS⟩ _ Ra,
    rcases Ra f fS with ⟨g,h₁⟩,
    refine ⟨_,h₁⟩
  end
}

/- ... Talks about the Zariski Site for a section ... -/

/- Sheaves on a site.
I have to define presheaves again because mathlib only has them wrt topologies.
 -/

def presheaf (C : Type u) [𝒞 : category.{v} C] := (opposite C) ⥤ Type


end category_theory
