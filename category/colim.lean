

variables {α β γ : Type}
variables {f g : α → β}
def equaliser (f g : α  → β ) : Type := {a : α // f a = g a}
def uniprop (h : γ → α) (p : f ∘ h = g ∘ h ) : ∃! (h' : γ → equaliser f g), subtype.val ∘ h' = h :=
    ⟨λ c, subtype.mk (h c) (have (f ∘ h) c = (g ∘ h) c, from congr_fun p c, by assumption), begin simp, intros, cases a, simp end⟩



@[inline] def coequaliser (f g : α  → β) := @quot β (λ b₁ b₂, ∃ a, f a = b₁ ∧ g a = b₂)
lemma qprop {h : β → γ} (p : h ∘ f = h ∘ g) : ∀ (b₁ b₂), (∃ (a), f a = b₁ ∧ g a = b₂) → h b₁ = h b₂
|_ _ ⟨a,⟨rfl,rfl⟩⟩ := congr_fun p a
def uprop (h : β → γ) (p : h ∘ f = h ∘ g) : ∃! (h' : coequaliser f g → γ), h' ∘ quot.mk _ = h :=
    ⟨λ z, quot.lift (h) (qprop p) z, begin simp, intros, funext, apply quot.induction_on x, intros, simp, apply congr_fun a end ⟩

-- so Type has all finite colimits. It has all small coproducts using Σ so I think that means we get all small colimits?
-- I could define the free monad by looking at the projection forget : {T : Type → Type // monad T} ->> {F : Type → Type // functor F}
-- The free monad is a function `free : Functor → Monad` which is 'left adjoint' wrt `forget`. How exactly?
-- I was hoping there would be a nice construction but I can't see it at the moment.