import .topological_space
open filter lattice

universes u
variables {α : Type u} [ topological_space α]

lemma compact_subset_of_t2space_is_closed_2
  [t2_space α] (Y : set α) (sc : compact Y) : is_closed Y := 
is_closed_iff_nhds.2 $ assume y h₁,
  let ⟨a, _, _⟩ := sc (nhds y ⊓ principal Y) h₁ inf_le_right in
  suffices y = a, by rwa this,
  suffices nhds y ⊓ nhds a ⊓ principal Y ≠ ⊥, 
    from eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot this inf_le_left ,
  by cc
