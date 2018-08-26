
universe u
section step
    variables (F : Type u → Type u) [functor F] (X : Type u)
    open nat sum
    @[inline] def step : ℕ → Type u
    |0 := X
    |(succ n) := X ⊕ F (step n)

    @[inline] def fr := Σ n:ℕ, step F X n

end step
section map
    open nat sum
    variables {F : Type u → Type u} [functor F] {X Y : Type u} (f : X → Y)
    def inj {F : Type u → Type u} [functor F] {X : Type u} : Π n:ℕ, step F X n → step F X (succ n)
    |0 x := inl x
    |(succ n) (inl x) := inl x
    |(succ n) (inr fx) := inr $ inj n <$> fx
    @[reducible] def step.map : Π {n:ℕ}, step F X n → step F Y n
    |0 x := f x
    |(succ n) (inl x) := inl $ f x
    |(succ n) (inr fx) := inr $ step.map <$> fx
    #check @sum.no_confusion
    lemma step.map_com_inj {f : X → Y} [is_lawful_functor F] : ∀ (n:ℕ) (x:step F X n), inj n (step.map f x) = step.map f (inj n x)
    |0 x := rfl
    |(succ n) (inl x) := by simp [inj]
    |(succ n) (inr x) := 
        begin 
            have h₁ : inj n ∘ step.map f = step.map f ∘ inj n, by apply funext; exact step.map_com_inj n,
            simp [inj, step.map],
            repeat {rw <-is_lawful_functor.comp_map},
            rw h₁,
        end
end map
section free
    open nat
    variables (F : Type u → Type u) [functor F] [is_lawful_functor F] (X : Type u)
    @[inline] def R : fr F X → fr F X → Prop
    |⟨n₁,x₁⟩ ⟨n₂,x₂⟩ := ∃ p: succ n₁ = n₂, ((eq.rec_on p $ inj n₁ x₁) : step F X n₂) = x₂
    @[inline] def free := quot (R F X)

end free
namespace free
    variables {F : Type u → Type u} [functor F] [is_lawful_functor F] {X : Type u} {Y : Type u}
    @[inline] def map_core (f : X → Y) : fr F X → free F Y
    |⟨n,x⟩ := quot.mk (R F Y) $ ⟨n,step.map f x⟩
    lemma map_core_quot_prop  {f : X → Y} : ∀ (a b : fr F X), R F X a b → map_core f a = map_core f b
    |⟨n,x⟩ ⟨_, _⟩ ⟨rfl,rfl⟩ := calc
        map_core f ⟨n,x⟩ = quot.mk (R F Y) ⟨n, step.map f x⟩                    : by simp [map_core]
                    ...  = quot.mk (R F Y) ⟨nat.succ n, inj n $ step.map f $ x⟩ : by apply quot.sound; simp [R]; exact ⟨rfl,trivial⟩
                    ...  = quot.mk (R F Y) ⟨nat.succ n, step.map f $ inj n $ x⟩ : by rw step.map_com_inj n x
                    ...  = map_core f ⟨nat.succ n, inj n $ x⟩                   : by simp [map_core]
    def map (f :X → Y) : free F X → free F Y := quot.lift (map_core f) (map_core_quot_prop)
    instance : functor (free F) := {map := λ X Y f x, map f x}

    -- [TODO] lawful functor
    lemma id_map_aux (x : free F X) : 
    lemma id_map (x : free F X) : id <$> x = x :=
        suffices h₁ : ∀ (j : fr F X), quot.lift (map_core id) map_core_quot_prop (quot.mk (R F X) j) = (quot.mk (R F X) j), from quot.ind h₁ x,
        λ ⟨n,x⟩, begin simp [map_core, step.map], end
    instance : is_lawful_functor (free F) := {
        id_map := sorry,
        comp_map := sorry
    }
    def free.pure (x: X) : free F X := quot.mk (R F X) ⟨0,x⟩
    def free.roll (y : F(free F X)) : free F X := 
    def free.ind 
        {C : free F X → Type u} 
        (pure : Π (x:X), C(free.pure x))
        (roll : Π (y : F(free F X)) (p: C <$> y), C(free.roll y))
    -- [TODO] bind
    -- [TODO] lawful monad
    -- [TODO] univerality property.
end free