/- The free monad.-/

/- The plan:
Given a functor F and a type α.
1. Define roll : λ x, α + F(x)
2. Show that `roll^n false` injects into `roll^(succ n) false`
3. Define an equivalence rel `R` on `Σ n:ℕ, roll^n false`, they are the same when one injects to the other.
3. `free F α := quotient (Σ n:ℕ, roll^n false) R`
5. Prove that `free F α` is a monad.
 -/

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

