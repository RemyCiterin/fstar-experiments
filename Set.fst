module Set 

module C  = Compare 
module BT = BinTree

open BinTree

let ordering = C.ordering

let comparaison a = C.comparaison a

type set #a (compare: comparaison a) = s: BT.set compare {BT.is_avl s}

let mem #a (#f: comparaison a) (x:a) (input: set f) : b:bool{b <==> BT.member x input} = 
    AVL.mem_lemma x input; AVL.mem x input

let add #a (#f: comparaison a) (x:a) (input: set f) : out:set f{
        forall y. mem y out <==> mem y input || C.EQ? (f x y)
    } = AVL.add_lemma x input; AVL.add x input

let remove #a (#f: comparaison a) (x:a) (input: set f) : out:set f {
        forall y. mem y out <==> (mem y input /\ ~(C.EQ? (f x y)))
    } = AVL.remove_lemma x input; AVL.remove x input

let find_min #a (#f:comparaison a) (input: set f) : out:option a { match out with 
        | Some m -> mem m input /\ (forall x. member x input ==> C.is_GE (f x m))
        | None -> Leaf? input 
    } 

    = match input with
    | Leaf -> None 
    | Node l k _ r -> 
        AVL.find_min_lemma input;
        Some (AVL.find_min input)

let find_max #a (#f:comparaison a) (input: set f) : out:option a { match out with 
        | Some m -> mem m input /\ (forall x. member x input ==> C.is_LE (f x m))
        | None -> Leaf? input
    } 

    = match input with
    | Leaf -> None 
    | Node l k _ r -> 
        AVL.find_max_lemma input;
        Some (AVL.find_max input)

let remove_min #a (#f: comparaison a) (input: set f) : out:set f {match find_min input with 
        | Some m -> forall y. mem y out <==> (mem y input /\ ~(C.EQ? (f m y)))
        | None -> Leaf? input /\ Leaf? out
    } = 
    match input with 
    | Leaf -> Leaf 
    | Node l k _ r ->
        AVL.remove_min_lemma input;
        AVL.remove_min input

let remove_max #a (#f: comparaison a) (input: set f) : out:set f {match find_max input with 
        | Some m -> forall y. mem y out <==> (mem y input /\ ~(C.EQ? (f m y)))
        | None -> Leaf? input /\ Leaf? out
    } = 
    match input with
    | Leaf -> Leaf
    | Node l k _ r ->
        AVL.remove_max_lemma input;
        AVL.remove_max input

// todo : 
// union 
// split 
// intersection
// difference 
// mais ce n'est pas important pour des BDD...seul add l'est x)