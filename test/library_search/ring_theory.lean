import tactic.library_search
import ring_theory.principal_ideal_domain
import ring_theory.polynomial

set_option trace.silence_library_search true

example {α : Type} [euclidean_domain α] {S : ideal α} {x y : α} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
by library_search -- exact mod_mem_iff hy

variables {R : Type} [comm_ring R] [decidable_eq R]
variables {I : ideal (polynomial R)}

example {m n : ℕ} (H : m ≤ n) : I.leading_coeff_nth m ≤ I.leading_coeff_nth n :=
by library_search -- exact ideal.leading_coeff_nth_mono I H
