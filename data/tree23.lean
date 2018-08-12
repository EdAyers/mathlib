

meta def tree23.default_lt : tactic unit := `[apply has_lt.lt]
/- Implementation of 23-trees -/
universe u
inductive node (k : Type u) (α : Type u) : ℕ -> Type u
|Empty {} : node 0
|Two {n}: node n -> (k × α) -> node n -> node (n + 1)
|Three {n}: node n -> (k × α) -> node n -> (k × α) -> node n -> node (n + 1)

namespace node
variable {k : Type u}
variables {α β δ: Type u}
def empty : node k α 0 := node.Empty

def map (f : k -> α -> β)  : Π {n}, node k α n -> node k β n
|0 Empty := Empty
|n (Two l ⟨k,a⟩ r) := Two (map l) ⟨k, f k a⟩ (map r)
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := Three (map l) ⟨k1,f k1 a1⟩ (map m) ⟨k2,f k2 a2⟩ (map r)

def fold (f : k -> α -> β -> β) : Π {n}, node k α n -> β -> β
|0 Empty b := b
|n (Two l ⟨k,a⟩ r) b := fold r $ f k a $ fold l $ b
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) b := fold r $ f k2 a2 $ fold m $ f k1 a1 $ fold l $ b

open nat
def min : 
Π {n},  node k α n              -> option (k × α)
|(0)   Empty                   := none
|(1)   (Two Empty ka _)        := some ka
|(n+1) (Two l _ _)             := min l
|(1)   (Three Empty ka _ _ _)  := some ka
|(n+1) (Three l _ _ _ _)       := min l

def max : Π {n}, node k α n -> option (k × α)
|(0) Empty := none
|(1) (Two _ ka Empty) := some ka
|(n+1) (Two _ _ r) := max r
|(1) (Three _ _ _ ka Empty) := ka
|(n+1) (Three _ _ _ _ r) := max r

def traverse {m : Type u → Type u} [applicative m] {α β : Type u} (f : k -> α → m β) : Π {n}, node k α n → m (node k β n)
|(0) Empty := pure Empty
|(n) (Two l ⟨k,a⟩ r) := 
    pure (λ l b r, Two l ⟨k,b⟩ r) 
    <*> traverse l <*> f k a <*> traverse r
|(n) (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    pure (λ l b1 m b2 r, Three l ⟨k1,b1⟩ m ⟨k2, b2⟩ r) 
    <*> traverse l <*> f k1 a1 <*> traverse m <*> f k2 a2 <*> traverse r


def find (p : k -> α -> bool): Π {n}, node k α n -> option (k × α)
|0 Empty := none
|n (Two l ⟨k,a⟩ r) := find l <|> (if (p k a) then some ⟨k,a⟩ else none) <|> find r
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    find l 
    <|> (if (p k1 a1) then some ⟨k1,a1⟩ else none) 
    <|> find m 
    <|> (if (p k2 a2) then some ⟨k2,a2⟩ else none)
    <|> find r

variables (lt : k -> k -> Prop) [decidable_rel lt]
open ordering

def get (i : k): Π {n}, node k α n -> option α
|0 Empty := none
|n (Two l ⟨k,a⟩ r) :=
    match cmp_using lt i k with
    |ordering.lt := get l
    |ordering.eq := some a
    |ordering.gt := get r
    end
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    match cmp_using lt i k1 with
    |ordering.lt := get l 
    |ordering.eq := some a1
    |ordering.gt := match cmp_using lt i k2 with
           |ordering.lt := get m
           |ordering.eq := some a2
           |ordering.gt := get r
           end
    end

def has {n} (i : k) : node k α n -> bool := option.is_some ∘ get lt i

section
    inductive growth (k : Type u) (α : Type u) : ℕ -> Type u
    |Stay {n}: (node k α n) -> growth n
    |Sprout {n}: (node k α n) -> k × α -> (node k α n) -> growth n
    open growth
    private def modify_raw (i : k) (f : option α -> α) : Π {n}, node k α n -> growth k α n
    |0 Empty := Sprout Empty (i, f none) Empty
    |(n+1) (Two l (p@⟨k,a⟩) r) :=
        match cmp_using lt i k with
        |ordering.lt :=
            match modify_raw l with
            |(Stay l) := Stay (Two l p r)
            |(Sprout l1 q l2) := Stay (Three l1 q l2 p r)
            end
        |ordering.eq := Stay (Two l ⟨k,f (some a)⟩ r)
        |ordering.gt :=
            match modify_raw r with
            |(Stay r) := Stay (Two l p r)
            |(Sprout r1 q r2)  := Stay (Three l p r1 q r2)
            end
        end
    |(n+1) (Three l (p1@⟨k1,a1⟩) m (p2@⟨k2,a2⟩) r) :=
        match cmp_using lt i k1 with
        |ordering.lt :=
            match modify_raw l with
            |(Stay l) := Stay (Three l p1 m p2 r)
            |(Sprout l1 q l2) := Sprout (Two l1 q l2) p1 (Two m p2 r)
            end
        |ordering.eq :=
            Stay (Three l ⟨k1, f $ some a1⟩ m p2 r) 
        |ordering.gt := 
            match cmp_using lt i k2 with
            |ordering.lt :=
                match modify_raw m with
                |(Stay m) := Stay (Three l p1 m p2 r)
                |(Sprout m1 q m2) := Sprout (Two l p1 m1) q (Two m2 p2 r)
                end
            |ordering.eq := Stay (Three l p1 m ⟨k2, f $ some a2⟩ r)
            |ordering.gt :=
                match modify_raw r with
                |(Stay r) := Stay (Three l p1 m p2 r)
                |(Sprout r1 q r2) := Sprout (Two l p1 m) p2 (Two r1 q r2)
                end
            end
        end
    def grown : Type u -> Type u -> Π (n:ℕ), Type u := λ k a n, Σ (growth : ℕ), node k α (n + growth)
    def modify (i : k) (f : option α -> α) {n} (t : node k α n) : grown k α n
    := match modify_raw lt i f t with
       |(Stay n) := sigma.mk 0 n
       |(Sprout l q r) := sigma.mk 1 (Two l q r)
       end

    def set (i : k) (a : α) {n} (t : node k α n) : grown k α n := modify lt i (λ _, a) t
end

section --deletion
    private def compare : option k -> (k × α) -> ordering
    |none ⟨k2,_⟩ := ordering.lt
    |(some k1) ⟨k2,_⟩ := cmp_using lt k1 k2
    private def if_eq {β : Type u} : ordering -> β -> β -> β
    |ordering.eq x y := x
    |_ x y := y
    inductive shrinkage : Type u -> Type u -> ℕ -> Type (u+1)
    |Fail {k} {α} {n} : shrinkage k α n
    |Go {k} {α} {n}: k × α -> node k α (n) -> shrinkage k α (n+1)
    |Stop {k} {α} {n}: k × α -> node k α n -> shrinkage k α n
    open shrinkage

    private def del : option k -> Π (n), node k α n -> shrinkage k α n
    |(none) (0) (Empty) := Fail
    |(some k) (0) (Empty) := Fail
    |(none) (1) (Two Empty p Empty) := Go p Empty
    |(none) (1) (Three Empty p Empty q Empty) := Stop p (Two Empty q Empty)
    |(some k1) (1) (Two Empty (p@⟨k2,a⟩) Empty) := 
        match cmp_using lt k1 k2 with
        |ordering.eq := Go p  Empty
        |_ := Fail
        end
    |(some k1) (1) (Three Empty (p2@⟨k2,a2⟩) Empty (p3@⟨k3,a3⟩) Empty ) :=
        match (⟨cmp_using lt k1 k2, cmp_using lt k2 k3⟩ : ordering × ordering) with
        |⟨ordering.eq, _⟩ := Stop p2 (Two Empty p3 Empty)
        |⟨_, ordering.eq⟩ := Stop p3 (Two Empty p2 Empty)
        |_ := Fail
        end
    |ko (n+2) (Two l p r) :=
        match compare lt ko p with
        |ordering.lt :=
            match del ko (n+1) l with
            |Fail := Fail
            |(Stop p2 l) := Stop p2 (Two l p r)
            |(Go p2 l) :=
                match r with
                |(Two rl rp rr) := Go p2 (Three l p rl rp rr)
                |(Three rl rp rm rq rr) := Stop p2 (Two (Two l p rl) rp (Two rm rq rr))
                end
            end
        |ord :=
            match del (if_eq ord none ko) (n+1) r with
            |Fail := Fail
            |Stop p2 r := Stop p2 (Two l (if_eq ord p2 p) r)
            |Go p2 r :=
                match l with
                |(Two ll lp lr) := Go p2 (Three ll lp lr (if_eq ord p2 p) r)
                |(Three ll lp lm lq lr) := Stop p2 (Two (Two ll lp lm) lq (Two lr (if_eq ord p2 p) r))
                end
            end
        end
    |ko (n+2) (Three l p m q r) :=
        match compare lt ko q with
        |ordering.lt :=
            match compare lt ko p with
            |ordering.lt :=
                match del ko (n+1) l with
                |Fail := Fail
                |Stop p2 l := Stop p2 (Three l p m q r)
                |Go p2 l :=
                    match (⟨m, r⟩ : _ × _) with
                    |⟨(Two ml mp mr), (Two _ _ _ )⟩ := Stop p2 (Two (Three l p ml mp mr) q r)
                    |⟨(Three ml mp mm mq mr), _⟩ := Stop p2 (Three (Two l p ml) mp (Two mm mq mr) q r)
                    |⟨(Two ml mp mr), (Three rl rp rm rq rr)⟩ := Stop p2 (Three (Two l p ml) mp (Two mr q rl) rq (Two rm rq rr))
                    end
                end
            |ord :=
                match del (if_eq ord none ko) (n+1) m with
                |Fail := Fail
                |Stop p2 m := Stop p2 (Three l (if_eq ord p2 p) m q r)
                |Go p2 m :=
                    match ( ⟨l,r⟩ : _ × _  )with
                    |⟨(Two ll lp lr), (Two _ _ _)⟩ := Stop p2 (Two (Three ll lp lr (if_eq ord p2 p) m) q r)
                    |⟨(Three ll lp lm lq lr), _⟩ := Stop p2 (Three (Two ll lp lr) lq (Two lr (if_eq ord p2 p) m) q r)
                    |⟨_, (Three rl rp rm rq rr) ⟩ := Stop p2 (Three l (if_eq ord p2 p) (Two m q rl) rp (Two rm rq rr)) 
                    end
                end
            end
        |ord :=
            match del (if_eq ord none ko) (n+1) r with
            |Fail := Fail
            |Stop q2 r := Stop q2 (Three l p m (if_eq ord q2 q) r)
            |Go q2 r :=
                match (⟨l,m⟩ : _ × _) with
                |⟨Two _ _ _, Two ml mp mr⟩ := Stop q2 (Two l p (Three ml mp mr (if_eq ord q2 q) r))
                |⟨_, Three ml mp mm mq mr⟩ := Stop q2 (Three l p (Two ml mp mm) mq (Two mr (if_eq ord q2 q) r))
                |⟨Three ll lp lm lq lr, Two ml mp mr⟩ := Stop q2 (Three (Two ll lp lm) lq (Two lr p ml) mp (Two mr (if_eq ord q2 q) r))
                end
            end
        end

    def delete_type (k : Type u) (α : Type u) : ℕ -> Type _
    |0 := node k α 0 -> Σ (shrank : bool), node k α 0
    |(n+1) := node k α (n+1) -> Σ (shrank : bool), node k α (if shrank then n else (n+1))

    def delete (i : k) : Π (n : ℕ), delete_type k α n 
    |(0) := λ h : node k α 0, ⟨ff,h⟩
    |(n+1) := λ t : node k α (n+1), 
        match del lt (some i) (n+1) t with
        |Fail := ⟨ff, t⟩
        |Stop _ t := ⟨ff, t⟩
        |Go _ t := ⟨tt, t⟩
        end
end
end node

-- TODO: proof that it's ordered
-- TODO: proof that modify and delete do the right thing.
