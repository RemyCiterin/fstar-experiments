module BinTree 

open FStar.Classical


// #set-options "--z3rlimit 50"

type ordering = 
    | GT
    | LT
    | EQ


let is_GE a = GT? a || EQ? a 
let is_LE a = LT? a || EQ? a


let reflexivity     #a (f: a -> a -> ordering) = forall x. EQ? (f x x)
let symmetry_EQ     #a (f: a -> a -> ordering) = forall x y. EQ? (f x y) <==> EQ? (f y x)
let anti_symetry    #a (f: a -> a -> ordering) = forall x y. LT? (f x y) <==> GT? (f y x)
let transitivity_LT #a (f: a -> a -> ordering) = forall x y z. (LT? (f x y) /\ LT? (f y z)) ==> LT? (f x z)
let transitivity_GT #a (f: a -> a -> ordering) = forall x y z. (GT? (f x y) /\ GT? (f y z)) ==> GT? (f x z)
let transitivity_EQ #a (f: a -> a -> ordering) = forall x y z. (EQ? (f x y) /\ EQ? (f y z)) ==> EQ? (f x z)
let transitivity    #a (f: a -> a -> ordering) = transitivity_EQ f /\ transitivity_GT f /\ transitivity_LT f


let comparaison a = f: (a -> a -> ordering) {reflexivity f /\ transitivity f /\ symmetry_EQ f /\ anti_symetry f}


type set #a (compare: comparaison a) = 
    | Node : left: set compare -> a -> nat -> set compare -> set compare
    | Leaf : set compare

let height #a (#f: comparaison a) (s: set f): nat = match s with 
    | Node l k s r -> s 
    | Leaf -> 0 

let key #a (#f: comparaison a) (s: set f{Node? s}) = match s with 
    | Node _ k _ _ -> k


let left #a (#f: comparaison a) (input: set f {Node? input}) : set f = 
    match input with Node l _ _ _ -> l 


let right #a (#f: comparaison a) (input: set f {Node? input}) : set f = 
    match input with Node _ _ _ r -> r 


let max x y = if x > y then x else y


let rec member #a (#f: comparaison a) (x:a) (input: set f) : Tot bool (decreases input) = 
    match input with 
    | Leaf -> false 
    | Node l k _ r -> 
    begin 
        EQ? (f x k) || member x l || member x r
    end



let delta #a (#f: comparaison a) (l: set f) (r: set f): nat = 
    if height l > height r 
    then height l - height r
    else height r - height l


let rec is_avl #a (#f: comparaison a) (input: set f): prop = match input with 
    | Node l k s r -> 
        s = max (height l) (height r) + 1 /\ 
        delta l r < 2 /\ is_avl l /\ is_avl r /\ 
        (forall x. member x l ==> LT? (f x k)) /\ 
        (forall x. member x r ==> GT? (f x k)) 
    | Leaf -> true


let make #a (#f: comparaison a) (l: set f) k (r: set f) : 
    out:set f{Node? out /\ left out == l /\ right out == r /\ key out == k /\ height out = 1 + max (height l) (height r)} 
    
    = Node l k (1 + max (height l) (height r)) r

let make_lemma #a (#f: comparaison a) (l: set f) k (r: set f) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            delta l r <= 1
        )
        
        (ensures (let out = make l k r in 
            is_avl out /\ height out == 1+max (height l) (height r) /\ 
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k))) /\ 
            Node? out /\ left out == l /\ right out == r /\ key out == k /\ height out = 1 + max (height l) (height r)
        )) = 
    
    ()


