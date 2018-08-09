
import category_theory.natural_transformation
open category_theory
namespace category_theory.adjunction
    universes u1 u2 v1 v2
    --def nid := nat_trans.id
    variables 
        {C : Type u1} [𝒞 : category.{u1 v1} C] 
        {D : Type u2} [𝒟 : category.{u2 v2} D]
    include 𝒞 𝒟
    structure Adjunction (L : C ~> D) (R : D ~> C) :=
        (η : functor.id C ==> (L >>> R))
        (ε : (R >>> L) ==> functor.id D)
        (triangle_1 :
            let a : R ==> R >>> L >>> R := eq.rec_on (functor.comp_id R) (nat_trans.whisker_left R η) in
            let b : R >>> L >>> R ==> R := eq.rec_on (functor.id_comp R) (nat_trans.whisker_right ε R) in
            a ⊟ b = nat_trans.id R)
        (triangle_2 :
            let a11 : L ==> L >>> R >>> L := eq.rec_on (functor.comp_id L) (nat_trans.whisker_right η L) in
            let a12 : L >>> R >>> L ==> L := eq.rec_on (functor.id_comp L) (nat_trans.whisker_left L ε) in
            a11 ⊟ a12 = nat_trans.id L)
end category_theory.adjunction