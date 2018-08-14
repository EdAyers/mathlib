import .topological_space
open filter lattice
universes u
variables {α : Type u} [ topological_space α]

lemma not_bot_left (f g : filter α) (H1 : f ⊓ g ≠ ⊥) : f ≠ ⊥ := begin
    apply neq_bot_of_le_neq_bot,
    apply H1,
    exact inf_le_left
end

lemma compact_subset_of_t2space_is_closed_2
    [t2_space α] (Y : set α) (sc : compact Y) : (is_closed Y) := 
    iff.elim_right is_closed_iff_nhds $ assume y H1,
    let ⟨a, H2, H3⟩ := (sc (nhds y ⊓ principal Y) H1 inf_le_right) in
    suffices y = a, from by rw this; assumption,
    suffices nhds y ⊓ nhds a ⊓ principal Y ≠ ⊥, 
        from eq_of_nhds_neq_bot $ not_bot_left _ _ this,
    by cc
