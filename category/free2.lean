

namespace free
    universe u
    constant free (F : Type u → Type u) [functor F] (X : Type u) : Type u
    variables {F : Type u → Type u} [functor F] {X : Type u}
    constant pure : X → free F X
    constant roll : F (free F X) → free F X
    variable {C : Type u} 
    constant rec : (X → C) → (F(free F X) → F C → C) → free F X → C
    variables (a : X → C) (b : F(free F X) → F C → C) {x : X} {y : F(free F X)}
    axiom pseudo_elim_pure {x : X} : rec a b (pure x) = a x
    axiom pseudo_elim_roll {y : F(free F X)} : rec a b (roll y) = b y (rec a b <$> y)
    axiom pure_or_roll : ∀ (a : free F X), (∃ (x:X), a = pure x) ∨ (∃ (y:F(free F X)), a = roll y)
    /-I don't think it's possible to construct such an object in Lean. 
    Also, interestingly you can't even write down the induction principle for this.-/

    noncomputable instance : monad (free F) := {
        map := λ X Y f, rec (pure ∘ f) (λ _, roll), 
        pure := λ X, pure, 
        bind := λ X Y a f, rec f (λ _, roll) a
    }
    lemma asdf (g : free F X) : rec pure (λ _, roll) g = id g := 
    match pure_or_roll g with
    |or.inl ⟨x,p⟩ := begin clear _match, cases p, rw pseudo_elim_pure, simp end
    |or.inr ⟨y,p⟩ := begin clear _match, cases p, rw pseudo_elim_roll, 
    end
    instance : is_lawful_functor (free F) := {
        id_map := λ X a, 
            match pure_or_roll a with
            |(or.inl ⟨x, p⟩) := begin clear _match, cases p, simp [functor.map], rw pseudo_elim_pure end
            |(or.inr ⟨y, p⟩) := begin clear _match, cases p, simp [functor.map], rw pseudo_elim_roll, sorry end -- doesn't work; need recursion :-(  
            end
        ,
        comp_map := _
    }

    -- [TODO] have a go at deriving false. I think it should be possible.

end free