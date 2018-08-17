/- The free monad defined using well_founded recursion? -/

/-Recall:
fix f := f (fix f)
free f a := a + f (free f a) === fix (λ x, a + f x)

fix (λ x, 1 + x) ≃ nat
fix (λ x, 1 + a × x) ≃ list a

What do I need to do to define the fixpoint functor?
fix : (α -> α) -> α
I can't do this. But I can do.
fix : (f : Type → Type)
      (wf : (α : Type) -> well_founded rel -> ∃ (frel : f α → f α → Prop), well_founded frel)
      (α : Type, wf) -> Type wf

How!?
    
-/

/- So:


`free id x := x + free id x === x + x + x + x + ... := nat × x`
`free (λ x, a × x) x := x + a × (x + ) === nat × x + nat`
`fre


 -/


universe u
open nat


@[simp] def step (f : Type u → Type u) (α : Type u) : (Π x : ℕ, (Π y:ℕ, y < x → Type u) → Type u)
|(0) p := α
|(succ n) p := 
  let xn := p n $ less_than_or_equal.refl $ succ n in
  f $ sum α xn
open well_founded

@[simp] def nfree (n : ℕ) (f : Type u → Type u) [functor f] (α : Type u) : Type u := fix nat.lt_wf (step f α) n

namespace nfree
variables {F : Type u → Type u} [functor F] {α β : Type u}
def pure (a : α) : nfree 0 F α := a
def from_pure : nfree 0 F α → α := begin intro fa, simp at fa, rewrite fix_eq at fa, simp at fa, assumption end
def from_roll : Π {n:ℕ}, nfree (succ n) F α → F (sum α $ nfree n F α) :=
begin intros, simp at a, rewrite fix_eq at a, simp at a, exact a end
def to_roll : Π {n:ℕ}, F (sum α $ nfree n F α) → nfree (succ n) F α := λ n fs, begin simp, rewrite fix_eq, simp, assumption end
open sum
def sumrec {n : ℕ} (f₁ : α → β) (f₂ : nfree n F α → nfree n F β) : (α ⊕ nfree n F α) → (β ⊕ nfree n F β)
:= @sum.rec α (nfree n F α) (λ _,β ⊕ nfree n F β) (λ a, inl $ f₁ a) (λ c, inr $ f₂ c)

def map (f : α → β) : Π {n : ℕ}, nfree n F α → nfree n F β
|(0) xs := pure $ f $ from_pure xs
|(succ n) xs := 
  to_roll $ (@sum.rec α (nfree n F α) (λ _,β ⊕ nfree n F β) (λ a, inl $ f a) (λ c, inr $ @map n c)) <$> from_roll xs

end nfree

