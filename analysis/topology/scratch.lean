import .topological_space
open set filter lattice

universes u v
variables {α : Type u} [ topological_space α]

def inclusion (s : set α) : s -> α := λ a, a
def subspace_top (s : set α) := topological_space.induced (inclusion s)

lemma not_bot_left (f g : filter α) (H1 : f ⊓ g ≠ ⊥) : f ≠ ⊥ := begin
    apply neq_bot_of_le_neq_bot,
    apply H1,
    exact inf_le_left
end

lemma compact_subset_of_t2space_is_closed 
    [t2_space α] (Y : set α) (sc : compact Y) : (is_closed Y) := begin
    cases is_closed_iff_nhds, clear mp,
    apply mpr, clear mpr, intros, rename a y,
    let f := (nhds y ⊓ principal Y),
    have H3 : (∃ a (H : a ∈ Y), f ⊓ nhds a ≠ ⊥), from sc f a_1 inf_le_right,
    apply exists.elim H3,
    intros,
    apply exists.elim a_2, intros,
    have H5 : nhds a ⊓ nhds y ≠ ⊥,
        rewrite inf_assoc at a_4, -- if I do inf_assoc first it fails?!
        rewrite inf_comm at a_4,
        rewrite inf_assoc at a_4,
        rewrite inf_comm at a_4,
        apply not_bot_left, assumption,
    have H4:  a = y, from eq_of_nhds_neq_bot H5,
    rewrite H4 at a_3,
    assumption
    end

lemma compact_subset_of_t2space_is_closed_2
    [t2_space α] (Y : set α) (sc : compact Y) : (is_closed Y) := 
    iff.elim_right is_closed_iff_nhds (λ y H1,
        exists.elim (sc (nhds y ⊓ principal Y) H1 inf_le_right) 
        (λ a H2, exists.elim H2 (λ _ _,
            suffices y = a, from by rw this; assumption,
            suffices nhds y ⊓ nhds a ⊓ principal Y ≠ ⊥, 
                from eq_of_nhds_neq_bot $ not_bot_left _ _ this,
            by cc
        )
    )
)

    
