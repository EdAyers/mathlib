

meta def tree23.default_lt : tactic unit := `[apply has_lt.lt]
/- Implementation of 23-trees -/
universe u
variable {k : Type u}
variables (lt : k -> k -> Prop) [decidable_rel lt]

inductive node (k : Type u) (α : Type u) 
|Empty {} : node 
|Two : node -> (k × α) -> node -> node 
|Three : node -> (k × α) -> node -> (k × α) -> node -> node 

namespace node
variables {α β δ: Type u}
def empty : node k α := node.Empty
def is_empty : node k α -> bool
|Empty := true
|_ := false

def map (f : k -> α -> β) : node k α -> node k β
|Empty := Empty
|(Two l ⟨k,a⟩ r) := Two (map l) ⟨k, f k a⟩ (map r)
|(Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := Three (map l) ⟨k1,f k1 a1⟩ (map m) ⟨k2,f k2 a2⟩ (map r)

def fold (f : k -> α -> β -> β) : node k α -> β -> β
|Empty b := b
|(Two l ⟨k,a⟩ r) b := fold r $ f k a $ fold l $ b
|(Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) b := fold r $ f k2 a2 $ fold m $ f k1 a1 $ fold l $ b

def min : node k α -> option (k × α)
|Empty := none
|(Two Empty ka _) := some ka
|(Two l _ _) := min l
|(Three Empty ka _ _ _) := some ka
|(Three l _ _ _ _) := min l

def max : node k α -> option (k × α)
|Empty := none
|(Two _ ka Empty) := some ka
|(Two _ _ r) := max r
|(Three _ _ _ ka Empty) := ka
|(Three _ _ _ _ r) := max r

def traverse {m : Type u → Type u} [applicative m] {α β : Type u} (f : k -> α → m β) : node k α → m (node k β)
|Empty := pure Empty
|(Two l ⟨k,a⟩ r) := 
    pure (λ l b r, Two l ⟨k,b⟩ r) 
    <*> traverse l <*> f k a <*> traverse r
|(Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    pure (λ l b1 m b2 r, Three l ⟨k1,b1⟩ m ⟨k2, b2⟩ r) 
    <*> traverse l <*> f k1 a1 <*> traverse m <*> f k2 a2 <*> traverse r


def find (p : k -> α -> bool): node k α -> option (k × α)
|Empty := none
|(Two l ⟨k,a⟩ r) := find l <|> (if (p k a) then some ⟨k,a⟩ else none) <|> find r
|(Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    find l 
    <|> (if (p k1 a1) then some ⟨k1,a1⟩ else none) 
    <|> find m 
    <|> (if (p k2 a2) then some ⟨k2,a2⟩ else none)
    <|> find r
open ordering
def get (i : k): node k α -> option α
|Empty := none
|(Two l ⟨k,a⟩ r) :=
    match cmp_using lt i k with
    |ordering.lt := get l
    |ordering.eq := some a
    |ordering.gt := get r
    end
|(Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    match cmp_using lt i k1 with
    |ordering.lt := get l 
    |ordering.eq := some a1
    |ordering.gt := match cmp_using lt i k2 with
           |ordering.lt := get m
           |ordering.eq := some a2
           |ordering.gt := get r
           end
    end

def has (i : k) : node k α -> bool := option.is_some ∘ get lt i

section
    inductive growth (k : Type u) (α : Type u)
    |Stay : (node k α) -> growth
    |Sprout : (node k α) -> k × α -> (node k α) -> growth
    open growth
    private def modify_raw (i : k) (f : option α -> α) : node k α -> growth k α
    |Empty := Sprout Empty (i, f none) Empty
    |(Two l (p@⟨k,a⟩) r) :=
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
    |(Three l (p1@⟨k1,a1⟩) m (p2@⟨k2,a2⟩) r) :=
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
    def modify (i : k) (f : option α -> α) (n : node k α) : node k α
    := match modify_raw lt i f n with
       |(Stay n) := n
       |(Sprout l q r) := Two l q r
       end

    def set (i : k) (a : α) : node k α -> node k α := modify lt i (λ _, a)
end

section --deletion
    private def compare : option k -> (k × α) -> ordering
    |none ⟨k2,_⟩ := ordering.lt
    |(some k1) ⟨k2,_⟩ := cmp_using lt k1 k2
    private def if_eq {β : Type u} : ordering -> β -> β -> β
    |ordering.eq x y := x
    |_ x y := y
    inductive shrinkage (k : Type u) (α : Type u)
    |Fail {} : shrinkage
    |Go : k × α -> node k α -> shrinkage
    |Stop : k × α -> node k α -> shrinkage
    open shrinkage

    private def del : option k -> node k α -> shrinkage k α
    |(none) (Empty) := Fail
    |(some k) (Empty) := Fail
    |none (Two Empty p Empty) := Go p Empty
    |none (Three Empty p Empty q Empty) := Stop p (Two Empty q Empty)
    |(some k1) (Two Empty (p@⟨k2,a⟩) Empty) := 
        match cmp_using lt k1 k2 with
        |ordering.eq := Go p  Empty
        |_ := Fail
        end
    |(some k1) (Three Empty (p2@⟨k2,a2⟩) Empty (p3@⟨k3,a3⟩) Empty ) :=
        match (⟨cmp_using lt k1 k2, cmp_using lt k2 k3⟩ : ordering × ordering) with
        |⟨ordering.eq, _⟩ := Stop p2 (Two Empty p3 Empty)
        |⟨_, ordering.eq⟩ := Stop p3 (Two Empty p2 Empty)
        |_ := Fail
        end
    |ko (Two l p r) :=
        match compare lt ko p with
        |ordering.lt :=
            match del ko l with
            |Fail := Fail
            |(Stop p2 l) := Stop p2 (Two l p r)
            |(Go p2 l) :=
                match r with
                |Empty := Fail
                |(Two rl rp rr) := Go p2 (Three l p rl rp rr)
                |(Three rl rp rm rq rr) := Stop p2 (Two (Two l p rl) rp (Two rm rq rr))
                end
            end
        |ord :=
            match del (if_eq ord none ko) r with
            |Fail := Fail
            |Stop p2 r := Stop p2 (Two l (if_eq ord p2 p) r)
            |Go p2 r :=
                match l with
                |Empty := Fail
                |(Two ll lp lr) := Go p2 (Three ll lp lr (if_eq ord p2 p) r)
                |(Three ll lp lm lq lr) := Stop p2 (Two (Two ll lp lm) lq (Two lr (if_eq ord p2 p) r))
                end
            end
        end
    |ko (Three l p m q r) :=
        match compare lt ko q with
        |ordering.lt :=
            match compare lt ko p with
            |ordering.lt :=
                match del ko l with
                |Fail := Fail
                |Stop p2 l := Stop p2 (Three l p m q r)
                |Go p2 l :=
                    match (⟨m, r⟩ : _ × _) with
                    |⟨(Two ml mp mr), (Two _ _ _ )⟩ := Stop p2 (Two (Three l p ml mp mr) q r)
                    |⟨(Three ml mp mm mq mr), _⟩ := Stop p2 (Three (Two l p ml) mp (Two mm mq mr) q r)
                    |⟨(Two ml mp mr), (Three rl rp rm rq rr)⟩ := Stop p2 (Three (Two l p ml) mp (Two mr q rl) rq (Two rm rq rr))
                    |_ := Fail
                    end
                end
            |ord :=
                match del (if_eq ord none ko) m with
                |Fail := Fail
                |Stop p2 m := Stop p2 (Three l (if_eq ord p2 p) m q r)
                |Go p2 m :=
                    match ( ⟨l,r⟩ : _ × _  )with
                    |⟨(Two ll lp lr), (Two _ _ _)⟩ := Stop p2 (Two (Three ll lp lr (if_eq ord p2 p) m) q r)
                    |⟨(Three ll lp lm lq lr), _⟩ := Stop p2 (Three (Two ll lp lr) lq (Two lr (if_eq ord p2 p) m) q r)
                    |⟨_, (Three rl rp rm rq rr) ⟩ := Stop p2 (Three l (if_eq ord p2 p) (Two m q rl) rp (Two rm rq rr)) 
                    |_ := Fail
                    end
                end
            end
        |ord :=
            match del (if_eq ord none ko) r with
            |Fail := Fail
            |Stop q2 r := Stop q2 (Three l p m (if_eq ord q2 q) r)
            |Go q2 r :=
                match (⟨l,m⟩ : _ × _) with
                |⟨Two _ _ _, Two ml mp mr⟩ := Stop q2 (Two l p (Three ml mp mr (if_eq ord q2 q) r))
                |⟨_, Three ml mp mm mq mr⟩ := Stop q2 (Three l p (Two ml mp mm) mq (Two mr (if_eq ord q2 q) r))
                |⟨Three ll lp lm lq lr, Two ml mp mr⟩ := Stop q2 (Three (Two ll lp lm) lq (Two lr p ml) mp (Two mr (if_eq ord q2 q) r))
                |_ := Fail
                end
            end
        end
    def delete (i : k) (n : node k α) :=
    match del lt (some i) n with
    |Fail := n
    |Go _ n := n
    |Stop _ n := n
    end
end

/--Second argument clobbers first argument. -/
def merge (t1 : node k α) (t2 : node k α) : node k α :=fold (λ k a t, set lt k a t) t2 t1

end node
