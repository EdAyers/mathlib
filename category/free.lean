/- The free monad.-/

/- The plan:
Given a functor F and a type α.
1. Define roll : λ x, α + F(x)
2. Show that `roll^n false` injects into `roll^(succ n) false`
3. Define an equivalence rel `R` on `Σ n:ℕ, roll^n false`, they are the same when one injects to the other.
3. `free F α := quotient (Σ n:ℕ, roll^n false) R`
5. Prove that `free F α` is a monad.
 -/
import logic.relation
universes u
def sum.imp {α β γ δ : Type u} : (α → β) → (γ → δ) → (α ⊕ γ) → (β ⊕ δ) := λ l r, @sum.rec α γ (λ _, β ⊕ δ) (sum.inl ∘ l) (sum.inr ∘ r)
open sum
open nat


@[simp] def roll (F : Type u → Type u) [functor F] (α : Type u) : ℕ → Type u
|0 :=  (ulift empty) 
|(succ n) :=  α ⊕ F (roll n)

namespace roll
variables {F : Type u → Type u} [functor F] {α β : Type u}
def inj0 : roll F α 0 → β := begin intros, simp at a, cases a, exact empty.rec _ a end
def unroll {n:ℕ} : roll F α (succ n) → α ⊕ F (roll F α n) := begin intros, simp at a, assumption end
def reroll {n:ℕ} : α ⊕ F(roll F α n) → roll F α (succ n) := begin intros, simp, assumption end 
def inj : Π {n:ℕ}, roll F α n → roll F α (succ n)
|(0) a := inj0 a
|(succ n) a := begin simp at a, simp, cases a, exact sum.inl a, apply sum.inr,have h := inj <$> a, exact h,end
def map (f : α → β) : Π {n:ℕ}, roll F α n → roll F β n
|(0) a := inj0 a
|(succ n) a := reroll $ sum.imp (f) (functor.map map) $ unroll $ a
end roll

section
variables (F : Type u → Type u) [functor F] (α : Type u)
def fr := Σ n:ℕ, roll F α n
@[simp] def R : fr F α → fr F α → Prop
|⟨n₁,r₁⟩ ⟨n₂,r₂⟩ := ∃ p : succ n₁ = n₂, (eq.rec_on p $ roll.inj r₁ : roll F α n₂) = r₂
def free := quot (R F α)
end

namespace free
variables {F : Type u → Type u} [functor F] {α β : Type u}
def pure : α → free F α
|a := quot.mk (R F α) ⟨1, inl a⟩

def map {α β : Type u} (f : α → β): free F α → free F β :=
begin
  apply quot.lift, swap,
  intros, apply quot.mk, cases a with n ra, split, apply roll.map f, assumption,
  intros a b r,
  cases a with n₁ r₁, cases b with n₂ r₂, 
  simp [R] at r, cases r with p q, simp,
  clear n₂, 

  apply quot.ind, intros,
  simp *,
  cases r_b with n₃ r₃,
  cases r_a_1,
end

end free