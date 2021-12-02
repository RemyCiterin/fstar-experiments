module MapAVL

open Compare 

module BT = BinTree 

type map (a:eqtype) (b:eqtype) (f:comparaison a) = s:BT.set a b f{BT.is_avl s}

let mem (#a: eqtype) (#b:eqtype) (#f: comparaison a) (x:a) (input: map a b f) : out:bool{out <==> (
        exists y z. BT.member (y, z) input /\ EQ? (f x y)
    )} = AVL.mem_lemma x input; AVL.mem x input

let member_key (#a:eqtype) (#b:eqtype) (#f:comparaison a) (x:a) (input: map a b f) : out:bool{
        out <==> (exists y. BT.member (x, y) input)
    } = 
    AVL.find_lemma x input;
    
    let aux (y:b) : 
        Lemma 
            (
                BT.member (x, y) input ==> (
                    forall z. (EQ? (f x (fst z)) /\ BT.member z input) <==> (x, y) == z
            ))
        = AVL.lemma_EQ (x, y) input
    in 

    FStar.Classical.ghost_lemma aux; 

    match AVL.find x input with 
    | Some (k, _) -> k = x
    | None -> false

let member (#a:eqtype) (#b:eqtype) (#f:comparaison a) (x:a) (y:b) (input: map a b f) : out:bool{
        out <==> BT.member (x, y) input
    } =
    AVL.find_lemma x input;
    AVL.lemma_EQ (x, y) input;

    match AVL.find x input with 
    | Some (k, v) -> (k, v) = (x, y)
    | None -> false 

let find (#a: eqtype) (#b:eqtype) (#f: comparaison a) (x:a) (input: map a b f) : out:option (a&b) {
        match out with 
        | None -> ~(mem x input)
        | Some (y, z) -> member y z input /\ EQ? (f x y)
    } = 
    AVL.find_lemma x input;
    AVL.find x input

let add (#a: eqtype) (#b:eqtype) (#f: comparaison a) (s:map a b f) (x:a) (y:b) : (out:map a b f {
        forall z t. member z t out <==> (if EQ? (f x z) then (x, y) == (z, t) else member z t s)
    }) = 

    AVL.add_lemma (x, y) s;
    AVL.add (x, y) s


let remove (#a: eqtype) (#b:eqtype) (#f: comparaison a) (s:map a b f) (x:a) : (out:map a b f {
        forall y z. member y z out <==> (member y z s /\ ~(EQ? (f x y)))
    }) = 

    AVL.remove_lemma x s; 
    AVL.remove x s
