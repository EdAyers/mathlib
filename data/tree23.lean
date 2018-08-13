
meta def tree23.default_lt : tactic unit := `[apply has_lt.lt]
/- Implementation of 23-trees. Just as an exercise more than anything else. -/
universe u
inductive node (k : Type u) (α : Type u) : ℕ -> Type u
|Empty {} : node 0
|Two {n}: node n -> (k × α) -> node n -> node (n + 1)
|Three {n}: node n -> (k × α) -> node n -> (k × α) -> node n -> node (n + 1)
namespace node
variables {k : Type u} [decidable_linear_order k]
variables {α β δ: Type u}
@[simp] def mem : Π {n}, (k) -> (node k α n) -> Prop
|(0) _ Empty := false
|(n+1) i (Two l ⟨k,_⟩ r) := (mem i l) ∨ (k = i) ∨ (mem i r)
|(n+1) i (Three l ⟨k1,_⟩ m ⟨k2,_⟩ r) := (mem i l) ∨ (k1 = i) ∨ (mem i m) ∨ (k2 = i) ∨ (mem i r)

instance node_has_mem {n} : has_mem (k) (node k α n) := ⟨node.mem ⟩
open nat
@[simp] def min : 
Π {n},  node k α (n+1)         -> (k × α)
|(0)   (Two Empty ka _)        := ka
|(n+1) (Two l _ _)             := min l
|(0)   (Three Empty ka _ _ _)  := ka
|(n+1) (Three l _ _ _ _)       := min l

@[simp] def max : Π {n}, node k α (n+1) -> (k × α)
|(0) (Two _ ka Empty) := ka
|(n+1) (Two _ _ r) := max r
|(0) (Three _ _ _ ka Empty) := ka
|(n+1) (Three _ _ _ _ r) := max r

@[simp] def maxkey : Π {n}, node k α (n+1) -> k := λ n t, prod.fst (max t : k × α)
@[simp] def minkey : Π {n}, node k α (n+1) -> k := λ n t, prod.fst (min t : k × α)

open ordering

@[simp] def is_ordered : Π {n}, node k α n -> Prop 
|(0) Empty := true
|(1) (Two Empty _ Empty) := true
|(1) (Three Empty ⟨k1,_⟩ Empty ⟨k2,_⟩ Empty) := k1 < k2
|(n+2) (Two l ⟨k,_⟩ r) := 
    (is_ordered l) ∧ ((maxkey l) < k) 
    ∧ (is_ordered  r) ∧ ( k < (minkey r))
|(n+2) (Three l ⟨k1,_⟩ m ⟨k2,_⟩ r) := 
    (k1 < k2)
    ∧ (is_ordered  l) ∧ ( (maxkey l) < k1) 
    ∧ (is_ordered  m) ∧ ( k1 < (minkey m)) ∧ ((maxkey m) < k2)
    ∧ (is_ordered  r) ∧ ( k2 < (minkey r))

@[simp] def empty : node k α 0 := node.Empty
@[simp] def map (f : k -> α -> β)  : Π {n}, node k α n -> node k β n
|0 Empty := Empty
|n (Two l ⟨k,a⟩ r) := Two (map l) ⟨k, f k a⟩ (map r)
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := Three (map l) ⟨k1,f k1 a1⟩ (map m) ⟨k2,f k2 a2⟩ (map r)

lemma map_preserves_ordering {n : ℕ} (f : k -> α -> β) (t : node k α 0) 
: is_ordered t -> is_ordered (map f t) 
:= begin 
  intro H1,
  cases t,
  simp *
end

def fold (f : k -> α -> β -> β) : Π {n}, node k α n -> β -> β
|0 Empty b := b
|n (Two l ⟨k,a⟩ r) b := fold r $ f k a $ fold l $ b
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) b := fold r $ f k2 a2 $ fold m $ f k1 a1 $ fold l $ b


def traverse {m : Type u → Type u} [applicative m] {α β : Type u} (f : k -> α → m β) : Π {n}, node k α n → m (node k β n)
|(0) Empty := pure Empty
|(n) (Two l ⟨k,a⟩ r) := 
    pure (λ l b r, Two l ⟨k,b⟩ r) 
    <*> traverse l <*> f k a <*> traverse r
|(n) (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    pure (λ l b1 m b2 r, Three l ⟨k1,b1⟩ m ⟨k2, b2⟩ r) 
    <*> traverse l <*> f k1 a1 <*> traverse m <*> f k2 a2 <*> traverse r

-- TODO; what does an ordering proof look like for traverse?

def find (p : k -> α -> bool): Π {n}, node k α n -> option (k × α)
|0 Empty := none
|n (Two l ⟨k,a⟩ r) := find l <|> (if (p k a) then some ⟨k,a⟩ else none) <|> find r
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    find l 
    <|> (if (p k1 a1) then some ⟨k1,a1⟩ else none) 
    <|> find m 
    <|> (if (p k2 a2) then some ⟨k2,a2⟩ else none)
    <|> find r

@[simp] def get (i : k): Π {n}, node k α n -> option α
|0 Empty := none
|n (Two l ⟨k,a⟩ r) :=
    if i < k then get l
    else if i = k then some a
    else get r
|n (Three l ⟨k1,a1⟩ m ⟨k2,a2⟩ r) := 
    if i < k1 then get l
    else if i = k1 then some a1
    else if i < k2 then get m
    else if i = k2 then some a2
    else get r

@[simp] def has {n} (i : k) : node k α n -> bool := option.is_some ∘ get i

section 
variables {n : ℕ} (t : node k α (n+1)) (io : is_ordered t)
variables (i k₁ k₂ : k)

lemma minkey_lt_maxkey : (is_ordered t) -> (minkey t ≤ maxkey t) := begin
    intros,
    induction n,
    cases t, cases t_a, cases t_a_1, cases t_a_2,
    simp [*] at *,
    cases t_a, cases t_a_1, cases t_a_2, cases t_a_3, cases t_a_4,
    simp [*] at *, apply le_of_lt, assumption,
    cases t with _ l p r,
    cases p,
    repeat {cases a with _ a},
    apply le_trans, apply n_ih, assumption,
    repeat {apply le_trans, apply le_of_lt, assumption},
    apply n_ih, assumption,
    cases t_a_1, cases t_a_3,
    repeat {cases a with _ a},
    apply le_trans, apply n_ih, assumption,
    repeat {apply le_trans, apply le_of_lt, assumption},
    apply n_ih, assumption,
end

lemma lt_minkey_imp_outside : (is_ordered t) -> (i < minkey t) -> (i ∉ t) := begin
    intros, 
    simp [has_mem.mem],
    induction n,
    cases t with _ l p r _ l p m q r,
    cases p, cases l, cases r,
    repeat {cases a with _ a},
    simp * at *,
    apply ne_of_gt, assumption,
    cases p, cases q, cases l, cases m, cases r,
    repeat {cases a with _ a},
    simp * at *,
    apply not_or, apply ne_of_gt, assumption,
    apply ne_of_gt, apply gt_trans, assumption, assumption,
    -- n+2 case
    cases t with _ l p r _ l p m q r,
    cases p,
    simp * at *,
    repeat {cases a with _ a},
    have H1 : p_fst > i, from begin
        apply lt_trans,assumption,
        apply lt_of_le_of_lt, apply minkey_lt_maxkey, assumption, assumption,
    end,
    apply not_or, apply ne_of_gt,
    assumption,

    apply n_ih, assumption,
    apply lt_of_lt_of_le, apply H1, apply le_of_lt, assumption,
    
    cases p, cases q,
    repeat {cases a with _ a},
    simp * at *,
    have H2 : i < p_fst, from begin
        transitivity, apply a_1,
        apply lt_of_le_of_lt, apply minkey_lt_maxkey, assumption,
        assumption,         
    end,
    have H3 : p_fst < q_fst, from calc
        p_fst < minkey m : by assumption
        ...   ≤ maxkey m : by apply minkey_lt_maxkey; assumption
        ...   < q_fst    : by assumption
        ,
    have H4 : q_fst < minkey r, from by assumption,
    
    apply not_or, apply ne_of_gt, apply H2,
    apply not_or, apply n_ih, assumption,

    show  i < minkey m, from calc
          i < p_fst : H2
        ... < minkey m : by assumption,
    
    apply not_or, apply ne_of_gt,
    from calc
         i  < p_fst : H2
        ... < q_fst : H3,
    apply n_ih, assumption,
    from calc
        i    < p_fst : H2
         ... < q_fst : H3
         ... < minkey r : by assumption,
end
end
section
    inductive growth (k : Type u) (α : Type u) : ℕ -> Type u
    |Stay {n}: (node k α n) -> growth n
    |Sprout {n}: (node k α n) -> k × α -> (node k α n) -> growth n
    open growth
    private def modify_raw (i : k) (f : option α -> α) : Π {n}, node k α n -> growth k α n
    |0 Empty := Sprout Empty (i, f none) Empty
    |(n+1) (Two l (p@⟨k,a⟩) r) :=
        if i < k then 
            match modify_raw l with
            |(Stay l) := Stay (Two l p r)
            |(Sprout l1 q l2) := Stay (Three l1 q l2 p r)
            end
        else if i = k then Stay (Two l ⟨k,f (some a)⟩ r)
        else -- i > k
            match modify_raw r with
            |(Stay r) := Stay (Two l p r)
            |(Sprout r1 q r2)  := Stay (Three l p r1 q r2)
            end
    |(n+1) (Three l (p1@⟨k1,a1⟩) m (p2@⟨k2,a2⟩) r) :=
        if i < k1 then 
            match modify_raw l with
            |(Stay l) := Stay (Three l p1 m p2 r)
            |(Sprout l1 q l2) := Sprout (Two l1 q l2) p1 (Two m p2 r)
            end
        else if i = k1 then Stay (Three l ⟨k1, f $ some a1⟩ m p2 r)
        else if i < k2 then 
            match modify_raw m with
            |(Stay m) := Stay (Three l p1 m p2 r)
            |(Sprout m1 q m2) := Sprout (Two l p1 m1) q (Two m2 p2 r)
            end
        else if i = k2 then Stay (Three l p1 m ⟨k2, f $ some a2⟩ r)
        else -- i > k2
            match modify_raw r with
            |(Stay r) := Stay (Three l p1 m p2 r)
            |(Sprout r1 q r2) := Sprout (Two l p1 m) p2 (Two r1 q r2)
            end
    def grown : Type u -> Type u -> Π (n:ℕ), Type u := λ k a n, Σ (growth : ℕ), node k α (n + growth)
    def modify (i : k) (f : option α -> α) {n} (t : node k α n) : grown k α n
    := match modify_raw i f t with
       |(Stay n) := sigma.mk 0 n
       |(Sprout l q r) := sigma.mk 1 (Two l q r)
       end
    def set (i : k) (a : α) {n} (t : node k α n) : grown k α n := modify i (λ _, a) t
end

section --deletion
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
        if k1 = k2 then Go p Empty else Fail
    |(some k1) (1) (Three Empty (p2@⟨k2,a2⟩) Empty (p3@⟨k3,a3⟩) Empty ) :=
        if k1 = k2 then Stop p2 (Two Empty p3 Empty)
        else if k1 = k3 then Stop p3 (Two Empty p2 Empty)
        else Fail
    |none (n+2) (Two l p r) :=
            match del none (n+1) l with
            |Fail := Fail
            |(Stop p2 l) := Stop p2 (Two l p r)
            |(Go p2 l) :=
                match r with
                |(Two rl rp rr) := Go p2 (Three l p rl rp rr)
                |(Three rl rp rm rq rr) := Stop p2 (Two (Two l p rl) rp (Two rm rq rr))
                end
            end
    |(some k1) (n+2) (Two l (p@⟨k2,_⟩) r) :=
        if k1 < k2 then
            match del (some k1) (n+1) l with
            |Fail := Fail
            |(Stop p2 l) := Stop p2 (Two l p r)
            |(Go p2 l) :=
                match r with
                |(Two rl rp rr) := Go p2 (Three l p rl rp rr)
                |(Three rl rp rm rq rr) := Stop p2 (Two (Two l p rl) rp (Two rm rq rr))
                end
            end
        else 
            match del (if k1 = k2 then none else some k1) (n+1) r with
            |Fail := Fail
            |Stop p2 r := Stop p2 (Two l (if k1 = k2 then p2 else p) r)
            |Go p2 r :=
                let p' := if k1 = k2 then p2 else p in
                match l with
                |(Two ll lp lr) := Go p2 (Three ll lp lr p' r)
                |(Three ll lp lm lq lr) := Stop p2 (Two (Two ll lp lm) lq (Two lr p' r))
                end
            end
    |none (n+2) (Three l p m q r) :=
        match del none (n+1) l with
            |Fail := Fail
            |Stop p2 l := Stop p2 (Three l p m q r)
            |Go p2 l :=
                match (⟨m, r⟩ : _ × _) with
                |⟨(Two ml mp mr), (Two _ _ _ )⟩ := Stop p2 (Two (Three l p ml mp mr) q r)
                |⟨(Three ml mp mm mq mr), _⟩ := Stop p2 (Three (Two l p ml) mp (Two mm mq mr) q r)
                |⟨(Two ml mp mr), (Three rl rp rm rq rr)⟩ := Stop p2 (Three (Two l p ml) mp (Two mr q rl) rq (Two rm rq rr))
                end
        end
    |(some k1) (n+2) (Three l (p@⟨kp,_⟩) m (q@⟨kq,_⟩) r) :=
        if k1 < kq then
            if k1 < kp then
                match del (some k1) (n+1) l with
                |Fail := Fail
                |Stop p2 l := Stop p2 (Three l p m q r)
                |Go p2 l :=
                    match (⟨m, r⟩ : _ × _) with
                    |⟨(Two ml mp mr), (Two _ _ _ )⟩ := Stop p2 (Two (Three l p ml mp mr) q r)
                    |⟨(Three ml mp mm mq mr), _⟩ := Stop p2 (Three (Two l p ml) mp (Two mm mq mr) q r)
                    |⟨(Two ml mp mr), (Three rl rp rm rq rr)⟩ := Stop p2 (Three (Two l p ml) mp (Two mr q rl) rq (Two rm rq rr))
                    end
                end
            else
                match del (if k1 = kp then none else some k1) (n+1) m with
                |Fail := Fail
                |Stop p2 m := Stop p2 (Three l (if k1 = kp then p2 else p) m q r)
                |Go p2 m :=
                    let p' := if k1 = kp then p2 else p in
                    match ( ⟨l,r⟩ : _ × _  )with
                    |⟨(Two ll lp lr), (Two _ _ _)⟩ := Stop p2 (Two (Three ll lp lr p' m) q r)
                    |⟨(Three ll lp lm lq lr), _⟩ := Stop p2 (Three (Two ll lp lr) lq (Two lr p' m) q r)
                    |⟨_, (Three rl rp rm rq rr) ⟩ := Stop p2 (Three l p' (Two m q rl) rp (Two rm rq rr)) 
                    end
                end
        else
            match del (if k1 = kq then none else some k1) (n+1) r with
            |Fail := Fail
            |Stop q2 r := Stop q2 (Three l p m (if k1 = kq then q2 else q) r)
            |Go q2 r :=
                let q' := if k1 = kq then q2 else q in
                match (⟨l,m⟩ : _ × _) with
                |⟨Two _ _ _, Two ml mp mr⟩ := Stop q2 (Two l p (Three ml mp mr q' r))
                |⟨_, Three ml mp mm mq mr⟩ := Stop q2 (Three l p (Two ml mp mm) mq (Two mr q' r))
                |⟨Three ll lp lm lq lr, Two ml mp mr⟩ := Stop q2 (Three (Two ll lp lm) lq (Two lr p ml) mp (Two mr q' r))
                end
            end

    def delete_type (k : Type u) (α : Type u) : ℕ -> Type _
    |0 := node k α 0 -> Σ (shrank : bool), node k α 0
    |(n+1) := node k α (n+1) -> Σ (shrank : bool), node k α (if shrank then n else (n+1))

    def delete (i : k) : Π (n : ℕ), delete_type k α n 
    |(0) := λ h : node k α 0, ⟨ff,h⟩
    |(n+1) := λ t : node k α (n+1), 
        match del (some i) (n+1) t with
        |Fail := ⟨ff, t⟩
        |Stop _ t := ⟨ff, t⟩
        |Go _ t := ⟨tt, t⟩
        end
end
end node

def tree (k : Type u) [decidable_linear_order k] (α : Type u) (n : ℕ) := {t : node k α n // node.is_ordered t}
namespace tree
variables {k : Type u} [decidable_linear_order k] (α : Type u)
def empty : tree k α 0 := ⟨node.empty, by simp * ⟩

end tree

-- TODO: proof that it's ordered
-- TODO: proof that modify and delete do the right thing.
