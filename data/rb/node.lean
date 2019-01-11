
namespace rb

universes u

inductive col | Red | Black

inductive node (α : Type u)  : Type u
|Leaf {}: node
|Node (c:col) (l:node) (a:α) (r:node) : node
open node col
notation `Rd` := (Node Red)
notation `Bk` := (Node Black)

namespace node

variables {α : Type u} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
local notation `nd` := node α
variables (a b c : α) (l r m : nd)

def empty : nd := Leaf
def mk_black : nd → nd
|(Leaf) := Leaf
|(Node _ l a r) := Node Black l a r

def mk_red : nd → nd 
|Leaf := Leaf
|(Node _ l a r) := Node Red l a r

def lbal : nd → α → nd → nd
| (Rd (Rd a x b) y c) v r := Rd (Bk a x b) y (Bk c v r)
| (Rd a x (Rd b y c)) v r := Rd (Bk a x b) y (Bk c v r)
| l v r := Bk l v r

def rbal : nd → α → nd → nd
| l v (Rd (Rd b w c) z d) := Rd (Bk l v b) w (Bk c z d)
| l v (Rd b w (Rd c z d)) := Rd (Bk l v b) w (Bk c z d)
| l v r := Bk l v r

def ins_aux (a : α) : nd → nd 
|Leaf := Rd Leaf a Leaf
|(Rd l v r) :=
    if a < v then Rd (ins_aux l) v r 
    else if a > v then Rd l v (ins_aux r) 
    else Rd l a r 
|(Bk l v r) :=
    if a < v then lbal (ins_aux l) v r
    else if a > v then rbal l v (ins_aux r) 
    else Bk l a r 

def insert (a : α) (t : nd) : nd := mk_black $ ins_aux a t

end node

end rb