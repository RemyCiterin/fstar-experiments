module BDD 

open FStar.List
module S = FStar.Set
module M = FStar.Map 


type bdd: eqtype = {hash: nat; node: node}

(** sign of the bdd *)
and sign: eqtype = | INVERSE | IDENTITY

(** a node can be a leaf with it's sign or a node of the form
sign (low <- var -> high) = (sign low <- var -> sign high) *)
and node: eqtype = 
    | Leaf: sign -> node 
    | Node: sign -> bdd -> nat -> bdd -> node

(** give the low bdd of a given bdd *)
let get_low (bdd: bdd{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> l

(** give the low bdd of a given bdd *)
let get_high (bdd: bdd{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> h

(** give the low bdd of a given bdd *)
let get_var (bdd: bdd{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> v

(** give the low bdd of a given bdd *)
let get_sign (bdd: bdd{Node? bdd.node}) = match bdd.node with 
    | Node s l v h -> s
    | Leaf s -> s 


(** allow to compare bdd without deep comparaison *)
type hash_type = bool & bool & nat & nat & nat
private let node_hash (node:node) : hash_type = 
    match node with 
    | Node INVERSE l v h  -> true, true,  l.hash, v, h.hash 
    | Node IDENTITY l v h -> true, false, l.hash, v, h.hash 
    | Leaf INVERSE  -> false, true,  0, 0, 0
    | Leaf IDENTITY -> false, false, 0, 0, 0


noeq
type global_table = {
    map: M.t hash_type bdd;
    size: nat
}

let is_correct_table (table: global_table) : prop = 
    forall (hash:hash_type). M.contains table.map hash ==> (
        let bdd = M.sel table.map hash in 
        node_hash bdd.node == hash /\ 
        bdd.hash < table.size /\
        begin match bdd.node with 
        | Node sign l v h -> 
        begin 
            M.contains table.map (node_hash l.node) /\ 
            M.contains table.map (node_hash h.node) /\ 
            M.sel table.map (node_hash l.node) == l /\
            M.sel table.map (node_hash h.node) == h /\
            (Leaf? l.node || get_var l < v) /\
            (Leaf? h.node || get_var h < v)
        end 
        | Leaf sign -> true 
        end
    )

type valid_table = table:global_table{is_correct_table table}

let contains_prop (table:valid_table) (bdd:bdd) : prop = 
    M.contains table.map (node_hash bdd.node) /\ (M.sel table.map (node_hash bdd.node)) == bdd

let is_compatible_node (table:valid_table) (node:node) : prop = 
    match node with 
    | Leaf s -> true 
    | Node s l v h -> 
        contains_prop table l /\ contains_prop table h /\
        (Leaf? l.node || get_var l < v) /\ 
        (Leaf? h.node || get_var h < v)

let measure (node:node) = 
    match node with 
    | Node s l v h -> v+1
    | Leaf s -> 0 

let measure_lemma (table:valid_table) (node:node{Node? node /\ is_compatible_node table node}) = 
    assert (measure (get_high (Mkbdd 0 node)).node < measure node);
    assert (measure (get_low  (Mkbdd 0 node)).node < measure node)

let rec contains_lemma1 (table:valid_table) (node:node) : 
    Lemma 
        (requires M.contains table.map (node_hash node))

        (ensures (contains_prop table (M.sel table.map (node_hash node))))

        (decreases (match node with | Node s l v r -> v+1 | Leaf s -> 0))
    = 

    let bdd = M.sel table.map (node_hash node) in 
    match bdd.node with 
    | Leaf s -> ()
    | Node s l v h -> 
        assert (Leaf? l.node || get_var l < v);
        assert (Leaf? l.node || get_var l < v);
        contains_lemma1 table l.node;
        contains_lemma1 table h.node

let contains_lemma2 (table:valid_table) (hash:hash_type) : 
    Lemma 
        (requires M.contains table.map hash)

        (ensures (contains_prop table (M.sel table.map hash)))

    = let bdd = M.sel table.map hash in 
    
    assert (node_hash bdd.node == hash);
    assert (M.contains table.map (node_hash bdd.node));
    assert (M.sel table.map (node_hash bdd.node) == bdd);
    contains_lemma1 table bdd.node

let inv (sign:sign) = match sign with 
    | INVERSE -> IDENTITY
    | IDENTITY -> INVERSE


let bdd_of_node (table:valid_table) (node:node{is_compatible_node table node}) : 
    out:(bdd&valid_table){(fst out).node == node /\ (
        forall (b:bdd). contains_prop (snd out) b <==> (contains_prop table b \/ b == fst out)
    )} = 

    if M.contains table.map (node_hash node) then begin 
        let bdd = M.sel table.map (node_hash node) in 

        contains_lemma1 table node;
        assert (contains_prop table bdd);
        //assert (bdd.node == node);
        admit()//bdd, table 
    end else admit ()

(** for proof *)
type bool_function = n:nat -> l:list bool{length l = n} -> bool