module BDD2

open FStar.List
module S = FStar.Set
module M = FStar.Map 

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

(** search is a children of a bdd have the same tag *)
let rec find_tag (bdd:bdd') (tag:nat) : bool =
    (Node? bdd.node && find_tag (get_low  bdd) tag) ||
    (Node? bdd.node && find_tag (get_high bdd) tag) ||
    tag = bdd.tag

(** one of the conditions that solve all valid bdd *)
let rec is_obdd (node:node') : prop = 
    match node with
    | Leaf s -> true 
    | Node s l v h -> 
        (Leaf? l.node || get_var l < v) /\ 
        (Leaf? h.node || get_var h < v) /\ 
        is_obdd l.node /\ is_obdd h.node

(** more safety type for bdd *)
type bdd  = bdd:bdd'  {is_obdd bdd.node}
type node = node:node'{is_obdd node}

(** allow to compare bdd without deep comparaison *)
type hash_type = bool & bool & nat & nat & nat
private let node_hash (node:node) : hash_type = 
    match node with 
    | Node INVERSE l v h  -> true, true,  l.tag, v, h.tag 
    | Node IDENTITY l v h -> true, false, l.tag, v, h.tag 
    | Leaf INVERSE  -> false, true,  0, 0, 0
    | Leaf IDENTITY -> false, false, 0, 0, 0


noeq
type global_table = {
    map: M.t hash_type bdd;
    size: nat
}