import .node
namespace rb
universes u 
variables {α : Type u} [decidable_linear_order α] 
local notation `nd` := node α
open node col nat
section
variables (c : col) (a b : α) (l r m : nd)
inductive mem (a : α) : nd → Prop
|left {c l v r} : mem l → mem (Node c l v r)
|mid {c l v r} : v = a → mem (Node c l v r)
|right {c l v r} : mem r → mem (Node c l v r)
instance : has_mem α nd := ⟨mem⟩
lemma leaf_empty {a : α} : a ∉ (@Leaf α) := λ h, by cases h

/--The given node satisfies the RB property. -/
inductive is_rb : nd → col → nat → Prop
|leaf_rb {} : is_rb Leaf Black 0
|red_rb {l v r n} (rb_l : is_rb l Black n) (rb_r : is_rb r Black n) : is_rb (Rd l v r) Red n
|black_rb {l c₁ v r c₂ n} (rb_l : is_rb l c₁ n) (rb_r : is_rb r c₂ n) : is_rb(Bk l v r) Black (succ n)

def dominates (a₁ : α) (t : nd) : Prop
:= ∀ a₂ ∈ t, a₁ > a₂
def dominated_by (a₁ : α) (t : nd) : Prop
:= ∀ a₂ ∈ t, a₁ < a₂
infix ` ⋗ `: 50 := dominates
infix ` ⋖ `: 50 := dominated_by

inductive ordered :nd → Prop
|o_leaf {} : ordered (Leaf) 
|o_node {c l} {v:α} {r} (ol:ordered l) (vdl :  v ⋗ l) (rdv : v ⋖ r) (or : ordered r) : ordered (Node c l v r)
lemma ordered.ol {c l v r} : ordered (Node c l v r :nd) → ordered l := begin intros, cases a, assumption end
lemma ordered.or {c l v r} : ordered (Node c l v r :nd) → ordered r := begin intros, cases a, assumption end

def is_wf (t : nd) : Prop := ∃ n, is_rb t Black n ∧ ordered t
end
variables {a₁ a₂ a₃ a v : α} {t l m r : nd} {c c₁ c₂ : col}
@[trans] lemma dominates.trans : a₁ > a₂ → a₂ ⋗ t → a₁ ⋗ t
:= λ p q a₃ ha, lt.trans (q _ ha) p 
lemma dominates.leaf : a₁ ⋗ (@Leaf α) := λ a₂ ha, false.rec_on _ $ leaf_empty ha
lemma dominates.node (hl : a₁ ⋗ l) (hv : a₁ > a) (hr : a₁ ⋗ r) : a₁ ⋗ (Node c l a r)
|a₂ (mem.left xl) := hl _ xl
|a₂ (mem.mid xm) := xm ▸ hv
|a₂ (mem.right xr) := hr _ xr
lemma dominates.l : a₁ ⋗ (Node c l v r) → a₁ ⋗ l := λ h a₂ hl, h a₂ (mem.left hl)
lemma dominates.r : a₁ ⋗ (Node c l v r) → a₁ ⋗ r := λ h a₂ hr, h a₂ (mem.right hr)
lemma dominates.v : a₁ ⋗ (Node c l v r) → a₁ > v := λ h, h v $ mem.mid rfl
@[trans] lemma dominated_by.trans : a₁ < a₂ → a₂ ⋖ t → a₁ ⋖ t
:= λ p q a₃ ha, lt.trans p (q _ ha)
lemma dominated_by.leaf : a₁ ⋖ (@Leaf α) := λ a₂ ha, false.rec_on _ $ leaf_empty ha
lemma dominated_by.node (hl : a₁ ⋖ l) (hv : a₁ < v) (hr : a₁ ⋖ r) : a₁ ⋖ (Node c l v r)
|a₂ (mem.left xl) := hl _ xl
|a₂ (mem.mid xm) := xm ▸ hv
|a₂ (mem.right xr) := hr _ xr
lemma dominated_by.l : a₁ ⋖ (Node c l v r) → a₁ ⋖ l := λ h a₂ hl, h a₂ (mem.left hl)
lemma dominated_by.r : a₁ ⋖ (Node c l v r) → a₁ ⋖ r := λ h a₂ hr, h a₂ (mem.right hr)
lemma dominated_by.v : a₁ ⋖ (Node c l v r) → a₁ < v := λ h, h v $ mem.mid rfl

def all_below := λ (t₁ t₂ : nd), ∀ (k₁ ∈ t₁) (k₂ ∈ t₂), k₁ < k₂
infix ` ⊏ `: 100 := all_below

lemma ordered.mk_black : ordered t → ordered (mk_black t) :=
begin
    intro o, cases o, {exact o},
    apply ordered.o_node, repeat {assumption}
end

lemma ordered.rbal : ordered l → a ⋖ r → a ⋗ l → ordered r → ordered (rbal l a r) :=
begin
    intros,
    sorry -- [TODO] write a tactic that eliminates `rbal` by expanding the function definition and then expanding all of the cases.
          -- [TODO] 
end


open ordered

end rb