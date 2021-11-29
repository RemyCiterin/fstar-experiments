module BinTree 

open FStar.Pervasives.Native
open FStar.Classical
open Compare 

let cmp (#a:eqtype) (#b:eqtype) (f: comparaison a) (x:a&b) (y:a&b) : ordering = f (fst x) (fst y)

noeq
type set (a: eqtype) (b: eqtype) (compare: comparaison a) = 
    | Node : set a b compare -> (a&b) -> nat -> set a b compare -> set a b compare
    | Leaf : set a b compare

let height (#a:eqtype) (#b:eqtype) (#f: comparaison a) (s: set a b f): nat = match s with 
    | Node l k s r -> s
    | Leaf -> 0

let key (#a:eqtype) (#b:eqtype) (#f: comparaison a) (s: set a b f{Node? s}) = match s with 
    | Node _ k _ _ -> k


let left (#a:eqtype) (#b:eqtype) (#f: comparaison a) (input: set a b f {Node? input}) : set a b f = 
    match input with Node l _ _ _ -> l 


let right (#a:eqtype) (#b:eqtype) (#f: comparaison a) (input: set a b f {Node? input}) : set a b f = 
    match input with Node _ _ _ r -> r 


let max x y = if x > y then x else y


let rec member (#a:eqtype) (#b:eqtype) (#f: comparaison a) (x:a&b) (input: set a b f) : Tot prop (decreases input) = 
    match input with 
    | Leaf -> false 
    | Node l k _ r -> 
    begin 
        x == k \/ member x l \/ member x r
    end


let delta (#a:eqtype) (#b:eqtype) (#f: comparaison a) (l: set a b f) (r: set a b f): nat = 
    if height l > height r 
    then height l - height r
    else height r - height l


let rec is_avl (#a:eqtype) (#b:eqtype) (#f: comparaison a) (input: set a b f): prop = match input with 
    | Node l k s r -> 
        s = max (height l) (height r) + 1 /\ 
        delta l r < 2 /\ is_avl l /\ is_avl r /\ 
        (forall x. member x l ==> LT? (cmp f x k)) /\
        (forall x. member x r ==> GT? (cmp f x k))
    | Leaf -> true


let make (#a:eqtype) (#b:eqtype) (#f: comparaison a) (l: set a b f) k (r: set a b f) : 
    out:set a b f{Node? out /\ left out == l /\ right out == r /\ key out == k /\ height out = 1 + max (height l) (height r)} 
    
    = Node l k (1 + max (height l) (height r)) r

let make_lemma (#a:eqtype) (#b:eqtype) (#f: comparaison a) (l: set a b f) k (r: set a b f) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (cmp f x k)) /\
            (forall x. member x r ==> GT? (cmp f x k)) /\
            delta l r <= 1
        )
        
        (ensures (let out = make l k r in 
            is_avl out /\ height out == 1+max (height l) (height r) /\ 
            (forall x. member x out <==> (member x l \/ member x r \/ x == k)) /\
            Node? out /\ left out == l /\ right out == r /\ key out == k /\ height out = 1 + max (height l) (height r)
        )) = 
    
    ()

