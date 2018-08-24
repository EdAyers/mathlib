
universe u
section
variables (F : Type u → Type u) [functor F] (X : Type u)
open nat sum
@[inline] def step : ℕ → Type u
|0 := X
|(succ n) := X ⊕ F (step n)

@[inline] def fr := Σ n:ℕ, step F X n

def inj {F : Type u → Type u} [functor F] {X : Type u} : Π n:ℕ, step F X n → step F X (succ n)
|0 x := inl x
|(succ n) (inl x) := inl x
|(succ n) (inr fx) := inr $ inj n <$> fx
end
section
open nat sum
variables {F : Type u → Type u} [functor F] [is_lawful_functor F] {X Y : Type u} (f : X → Y)
@[reducible] def step.map : Π {n:ℕ}, step F X n → step F Y n
|0 x := f x
|(succ n) (inl x) := inl $ f x
|(succ n) (inr fx) := inr $ step.map <$> fx

lemma step.map_com_inj : ∀ (n:ℕ) (x:step F X n), inj n (step.map f x) = step.map f (inj n x)
|0 x := rfl
|(succ n) (inl x) := by simp [inj]
|(succ n) (inr x) := begin simp [inj, step.map], rw <-is_lawful_functor.comp_map end

end
@[inline] def R : fr F X → fr F X → Prop
|⟨n₁,x₁⟩ ⟨n₂,x₂⟩ := ∃ p: succ n₁ = n₂, ((eq.rec_on p $ inj n₁ x₁) : step F X n₂) = x₂

@[inline] def free := quot (R F X)
end
namespace free
variables {F : Type u → Type u} [functor F] {X : Type u} {Y : Type u}

@[inline] def map_core (f : X → Y) : fr F X → free F Y
|⟨n,x⟩ := quot.mk (R F Y) $ ⟨n,step.map f x⟩
def map (f :X → Y) : free F X → free F Y := quot.lift (map_core f) (begin 
    intros, cases a with n₁ x₁, cases b with n₂ x₂,
    cases a_1 with p q,
    cases p,
    cases q,  clear q, clear p,
    simp [map_core],
    

end)
end free