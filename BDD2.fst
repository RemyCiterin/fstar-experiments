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
    | Node s l v h -> 
        (Leaf? l.node || get_var l < v) /\ 
        (Leaf? h.node || get_var h < v) /\ 
        is_obdd l.node /\ is_obdd h.node

(** type for a valid bdd *)
type bdd  = bdd:bdd'  {is_obdd bdd.node}

(** type for a valid node *)
type node = node:node'{is_obdd node}

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
    forall (node:node) (bdd:bdd). M.member node bdd table.map ==> (

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
    )

(** type of valid table *)
type global_table = table:global_table'{is_valid_table table}

