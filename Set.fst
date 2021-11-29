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
