module BDD2 

open Compare 
module M = MapAVL
module S = SetAVL 

(** type of typed bdd and it's tag for memoization *)
type bdd': eqtype = {tag: nat; node: node'}

(** sign of the bdd *)
and sign: eqtype = | INVERSE | IDENTITY

(** a node can be a leaf with it's sign or a node of the form
sign (low <- var -> high) = (sign low <- var -> sign high) *)
and node': eqtype = 
    | Leaf: sign -> node'
    | Node: sign -> bdd' -> nat -> bdd' -> node'

(** give the low bdd of a given bdd *)
let get_low (bdd: bdd'{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> l

(** give the low bdd of a given bdd *)
let get_high (bdd: bdd'{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> h

(** give the low bdd of a given bdd *)
let get_var (bdd: bdd'{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> v

(** give the low bdd of a given bdd *)
let get_sign (bdd: bdd'{Node? bdd.node}) = match bdd.node with
    | Node s l v h -> s
    | Leaf s -> s

(** one of the conditions that solve all valid bdd *)
let rec is_obdd (node:node') : prop = 
    match node with
    | Leaf s -> true 
    | Node s l v h -> l =!= h /\ 
        (Leaf? l.node || get_var l < v) /\ 
        (Leaf? h.node || get_var h < v) /\ 
        is_obdd l.node /\ is_obdd h.node

(** type for a valid bdd *)
type bdd  = bdd:bdd'  {is_obdd bdd.node}

(** type for a valid node *)
type node = node:node'{is_obdd node}

let rec eval_node (f: nat -> bool) (node:node') : bool
    = match node with 
    | Leaf IDENTITY -> true
    | Leaf INVERSE -> false
    | Node IDENTITY l v h -> 
        if f v then eval_node f h.node else eval_node f l.node
    | Node INVERSE  l v h -> 
        not (if f v then eval_node f h.node else eval_node f l.node)

(** comparaison function for integer *)
private let compareInt : comparaison int = fun x y -> 
    if x > y then GT else if x < y then LT else EQ 

(** comparaison function for node *)
let compareNode : comparaison node = fun (l:node) (h:node) ->
    match l, h with
    | Node ls ll lv lh, Node hs hl hv hh ->  
    begin
        match ls, hs with 
        | IDENTITY, INVERSE -> LT 
        | INVERSE, IDENTITY -> GT 
        | _, _ -> 
        begin 
            match compareInt ll.tag hl.tag with 
            | EQ -> begin match compareInt lh.tag hh.tag with 
                | EQ ->  compareInt lv hv 
                | x -> x end 
            | x -> x
        end 
    end 
    | Leaf ls, Leaf hs -> 
    begin
        match ls, hs with 
        | IDENTITY, INVERSE -> LT 
        | INVERSE, IDENTITY -> GT 
        | _, _ -> EQ 
    end 
    | Leaf ls, _ -> GT 
    | _, Leaf hs -> LT

(** a table of node/bdd and it's cardinal *)
type global_table' = {
    map: M.map node bdd compareNode; 
    size: nat;
}

(** a good memoization table !!! *)
let is_valid_table (table:global_table') : prop = 
    M.member (Leaf IDENTITY) ({tag=0; node=Leaf IDENTITY}) table.map /\
    M.member (Leaf INVERSE)  ({tag=1; node=Leaf INVERSE }) table.map /\
    (forall (node:node) (bdd:bdd). M.member node bdd table.map ==> (

        (* each pair bdd node is valid *)
        bdd.node == node /\
        
        (* ==> easy to create a new tag *)
        bdd.tag < table.size /\ 

        (* unicity of tag *)
        (forall n b. M.member n b table.map ==> (
            bdd.tag == b.tag ==> bdd == b
        )) /\

        (* recursivity property *)
        (Leaf? node \/ (
            let l = get_low  bdd in 
            let h = get_high bdd in 
            M.member l.node l table.map /\ 
            M.member h.node h table.map
        ))
    ))

(** type of valid table *)
type global_table = table:global_table'{is_valid_table table}


let compatible_node (table:global_table) (node:node): prop = 
    match node with 
    | Leaf s -> true
    | Node s l v h -> 
        M.member l.node l table.map /\ 
        M.member h.node h table.map


let contain_lemma1 (table:global_table) (node:node) : 
    Lemma 
        (requires compatible_node table node) 

        (ensures (
            match M.find node table.map with
            | Some (n, b) -> n == node /\ b.node == node
            | None -> true
        ))
    
    = match M.find node table.map with
    | None -> ()

    | Some (n, b) ->
    begin
        assert (EQ? (compareNode n node));

        match node with
        | Leaf s -> ()
        | Node s l v h -> begin
            assert (M.member l.node l table.map);
            assert (M.member h.node h table.map);

            assert (get_sign b == s);
            assert (Node? n);

            assert ((get_low  b).tag == l.tag);
            assert ((get_high b).tag == h.tag);
            assert (get_var b == v)
        end
    end

let contain_lemma2 (table:global_table) (node:node) :
    Lemma
        (requires compatible_node table node)

        (ensures (
            M.mem node table.map <==> M.member_key node table.map
        ))
    
    = contain_lemma1 table node

let inv (s:sign) = match s with 
    | INVERSE -> IDENTITY
    | IDENTITY -> INVERSE

#push-options "--z3rlimit 50"
let rec makeNode (table: global_table) (node:node') : 
    Pure
        (bdd&global_table)

        (requires (
            match node with 
            | Leaf s -> true 
            | Node s l v h -> 
                is_obdd l.node /\ 
                is_obdd h.node /\
                M.member l.node l table.map /\
                M.member h.node h table.map /\
                (Leaf? l.node || get_var l < v) /\
                (Leaf? h.node || get_var h < v)
        ))

        (ensures fun out -> (
            let bdd, table' = out in 
            M.member bdd.node bdd table'.map /\ // (Leaf? l.node || get_var l < v) /\
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall f. eval_node f bdd.node == eval_node f node)
        ))

        (decreases (
            match node with 
            | Leaf s -> 0 
            | Node s l v h -> v + 1
        ))
    
    = match node with 
    | Leaf IDENTITY -> ({tag=0; node=node}, table)
    | Leaf INVERSE  -> ({tag=1; node=node}, table)
    | Node s l v h -> 
    begin 
        if l.tag = h.tag then 
        begin 
            match s, l.node with 
            | IDENTITY, _ -> (l, table)
            | INVERSE, Node ls ll lv lh -> makeNode table (Node (inv ls) ll lv lh) 
            | INVERSE, Leaf ls          -> makeNode table (Leaf (inv ls))
        end 
        else 
        begin 
            assert (is_obdd node);

            match M.find node table.map with 
            | Some (n, b) -> 
            begin 
                contain_lemma1 table node; 
                (b, table)
            end 
            | None -> 
            begin 
                let bdd = {tag=table.size; node=node} in 
                let table' = {map=M.add table.map node bdd; size=table.size+1} in
                (bdd, table') 
            end 
        end 
    end 
#pop-options 

let notBDD (table:global_table) (input:bdd) : 
    Pure 
        (bdd&global_table)

        (requires M.member input.node input table.map) 

        (ensures fun out -> (
            let bdd', table' = out in 
            M.member bdd'.node bdd' table'.map /\ 
            (forall f. eval_node f bdd'.node == not (eval_node f input.node)) /\ 
            (forall n b. M.member n b table.map ==> M.member n b table'.map) 
        ))
    
    = match input.node with 
    | Leaf s       -> makeNode table (Leaf (inv s))
    | Node s l v h -> makeNode table (Node (inv s) l v h)


let apply (table: global_table) (f : bool -> bool -> bool) (l: bdd) (r : bdd) : 
    Pure 
        (bdd&global_table)

        (requires 
            M.member l.node l table.map /\ 
            M.member r.node r table.map 
        )

        (ensures fun out -> (
            let bdd', table' = out in 
            M.member bdd'.node bdd' table'.map /\ 
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall g. eval_node g bdd'.node == f (eval_node g l.node) (eval_node g r.node))
        ))
    
    = admit ()

let restrict (table:global_table) (n:nat) (b:bool) (input:bdd) : 
    Pure 
        (bdd&global_table)

        (requires M.member input.node input table.map)

        (ensures fun out -> (
            let bdd', table' = out in 
            M.member bdd'.node bdd' table'.map /\ 
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall f. eval_node f bdd'.node == eval_node (fun i -> if i = n then b else f i) input.node)
        ))
    
    = admit ()