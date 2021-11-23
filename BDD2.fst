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

let is_correct_table (table:global_table) : prop = 
    forall hash. M.contains table.map hash ==> (
        let bdd = M.sel table.map hash in 

        (* on veut pouvoir en conclure une relation du type
            bdd == (M.sel table.map (node_hash bdd.node))  *)
        node_hash bdd.node == hash /\ 

        (* pour la génération de futur bdd *)
        bdd.tag < table.size /\ 

        (* unicité des bdd dans la table à leurs tag près *)
        (forall hash'. 
            M.contains table.map hash' ==> (
            let bdd' = M.sel table.map hash' in 
            (bdd'.tag = bdd.tag ==> bdd' == bdd) /\ 
            (bdd'.node == bdd.node ==> bdd' == bdd)
        )) /\

        (* les fils d'un noeud doivent être dans la table *)
        begin match bdd.node with 
        | Node s l v h -> 
            M.contains table.map (node_hash l.node) /\ 
            M.contains table.map (node_hash h.node) /\ 
            M.sel table.map (node_hash l.node) == l /\
            M.sel table.map (node_hash h.node) == h
        | Leaf s -> true 
        end 
    )

type valid_table = table:global_table{is_correct_table table}

let contains_prop (table:valid_table) (bdd:bdd) : prop = 
    M.contains table.map (node_hash bdd.node) /\ (M.sel table.map (node_hash bdd.node)) == bdd

let is_compatible_node (table:valid_table) (node:node) : prop = 
    match node with 
    | Leaf s -> true 
    | Node s l v h -> 
        contains_prop table l /\ contains_prop table h