module SetAVL

module BT = BinTree

open Compare

type set (a:eqtype) (f: comparaison a) = s:BT.set a unit f{BT.is_avl s}

let mem (#a: eqtype) (#f: comparaison a) (x:a) (input: set a f) : out:bool{out <==> (
        exists y. BT.member (y, ()) input /\ EQ? (f x y)
    )} = AVL.mem_lemma x input; AVL.mem x input

let member (#a: eqtype) (#f: comparaison a) (x:a) (input: set a f) : out:bool{
        out <==> BT.member (x, ()) input
    } = 
    AVL.find_lemma x input;
    AVL.lemma_EQ (x, ()) input;

    match AVL.find x input with 
    | Some (k, _) -> k = x
    | None -> false

let find (#a: eqtype) (#f: comparaison a) (x:a) (input: set a f) : out:option a {
        match out with 
        | None -> ~(mem x input)
        | Some y -> member y input /\ EQ? (f x y)
    } = 
    AVL.find_lemma x input; 

    match AVL.find x input with 
    | Some (y, _) -> Some y
    | None -> None


let add (#a: eqtype) (#f: comparaison a) (s:set a f) (x:a) : (out:set a f {
        forall y. member y out <==> (if EQ? (f x y) then x == y else  member y s)
    }) = 
    AVL.add_lemma (x, ()) s;
    AVL.add (x, ()) s


let remove (#a: eqtype) (#f: comparaison a) (s:set a f) (x:a) : (out:set a f {
        forall y. member y out <==> (member y s /\ ~(EQ? (f x y)))
    }) = 
    AVL.remove_lemma x s; 
    AVL.remove x s

