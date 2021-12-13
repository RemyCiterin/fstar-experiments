module BDD

open Compare 
module M = MapAVL
module S = SetAVL 

(** type of typed bdd and it's tag for memoization *)
type bdd': eqtype = {tag: nat; node: node'}

(** a node can be a leaf with it's sign or a node of the form
sign (low <- var -> high) = (sign low <- var -> sign high) *)
and node': eqtype = 
    | One:  node'
    | Zero: node'
    | Node: bdd' -> nat -> bdd' -> node'

(** give the low bdd of a given bdd *)
let get_low (bdd: bdd'{Node? bdd.node}) = match bdd.node with 
    | Node l v h -> l

(** give the low bdd of a given bdd *)
let get_high (bdd: bdd'{Node? bdd.node}) = match bdd.node with 
    | Node l v h -> h

(** give the low bdd of a given bdd *)
let get_var (bdd: bdd'{Node? bdd.node}) = match bdd.node with 
    | Node l v h -> v

let is_leaf (n: node') : bool = match n with 
    | Zero | One -> true 
    | Node _ _ _ -> false 

(** one of the conditions that solve all valid bdd *)
let rec is_obdd (node:node') : prop = 
    match node with
    | Zero | One -> true 
    | Node l v h -> l =!= h /\ 
        (is_leaf l.node || get_var l < v) /\ 
        (is_leaf h.node || get_var h < v) /\ 
        is_obdd l.node /\ is_obdd h.node

(** type for a valid bdd *)
type bdd  = bdd:bdd'  {is_obdd bdd.node}

(** type for a valid node *)
type node = node:node'{is_obdd node}

let rec eval_node (f: nat -> bool) (node:node') : bool
    = match node with 
    | One  -> true 
    | Zero -> false 
    | Node l v h -> 
        if f v then eval_node f h.node else eval_node f l.node

(** comparaison function for integer *)
private let compareInt : comparaison int = fun x y -> 
    if x > y then GT else if x < y then LT else EQ 

(** comparaison function for node *)
let compareNode : comparaison node = fun (l:node) (h:node) ->
    match l, h with
    | Node ll lv lh, Node hl hv hh ->  
    begin
        match compareInt ll.tag hl.tag with 
        | EQ -> begin match compareInt lh.tag hh.tag with 
            | EQ ->  compareInt lv hv 
            | x -> x end 
        | x -> x
    end 
    | Zero, Node _ _ _ -> GT 
    | One , Node _ _ _ -> GT 
    | Node _ _ _, Zero -> LT 
    | Node _ _ _, One  -> LT 
    | Zero, One -> LT 
    | One, Zero -> GT 
    | _, _ -> EQ 

(** a table of node/bdd and it's cardinal *)
type global_table' = {
    map: M.map node bdd compareNode; 
    size: nat;
}

(** a good memoization table !!! *)
let is_valid_table (table:global_table') : prop = 
    M.member (One)  ({tag=1; node=One }) table.map /\
    M.member (Zero) ({tag=0; node=Zero}) table.map /\
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
        (is_leaf node \/ (
            let l = get_low  bdd in 
            let h = get_high bdd in 
            M.member l.node l table.map /\ 
            M.member h.node h table.map
        ))
    ))

(** type of valid table *)
type global_table = table:global_table'{is_valid_table table}


let measure (node:node') : nat = match node with 
    | Zero | One -> 0 | Node _ v _ -> v + 1

let compatible_node (table:global_table) (node:node): prop = 
    match node with 
    | Zero | One -> true 
    | Node l v h -> 
        M.member l.node l table.map /\ 
        M.member h.node h table.map

#push-options "--z3rlimit 50"
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
        | Zero | One -> ()
        | Node l v h -> begin
            assert (M.member l.node l table.map);
            assert (M.member h.node h table.map);
            assert (Node? n); 

            assert ((get_low  b).tag == l.tag);
            assert ((get_high b).tag == h.tag);

            assert (get_var b == v)
        end
    end
#pop-options


let contain_lemma2 (table:global_table) (node:node) :
    Lemma
        (requires compatible_node table node)

        (ensures (
            M.mem node table.map <==> M.member_key node table.map
        ))
    
    = contain_lemma1 table node

#push-options "--z3rlimit 50"
let makeNode (table: global_table) (node:node') : 
    Pure
        (bdd&global_table)

        (requires (
            match node with 
            | Zero | One -> true 
            | Node l v h -> 
                is_obdd l.node /\ 
                is_obdd h.node /\
                M.member l.node l table.map /\
                M.member h.node h table.map /\
                (is_leaf l.node || get_var l < v) /\
                (is_leaf h.node || get_var h < v)
        ))

        (ensures fun out -> (
            let bdd, table' = out in 
            M.member bdd.node bdd table'.map /\ // (Leaf? l.node || get_var l < v) /\
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall f. eval_node f bdd.node == eval_node f node) /\ 
            (measure node >= measure bdd.node)
        ))
    
    = match node with 
    | One  -> ({tag=1; node=node}, table)
    | Zero -> ({tag=0; node=node}, table)
    | Node l v h -> 
    begin 
        if l.tag = h.tag then (l, table) else 
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


let rec notBDD (table:global_table) (input:bdd) : 
    Pure 
        (bdd&global_table)

        (requires M.member input.node input table.map) 

        (ensures fun out -> (
            let bdd', table' = out in 
            M.member bdd'.node bdd' table'.map /\ 
            (forall f. eval_node f bdd'.node == not (eval_node f input.node)) /\ 
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (measure input.node >= measure bdd'.node)
        ))

        (decreases (measure input.node))
    
    = match input.node with 
    | One -> makeNode table Zero
    | Zero -> makeNode table One
    | Node l v h -> 
    begin 
        let (l', table1) = notBDD table  l in
        let (h', table2) = notBDD table1 h in 
        assert (is_obdd l'.node); assert (is_obdd h'.node); 
        assert (M.member l'.node l' table2.map); 
        assert (M.member h'.node h' table2.map);

        makeNode table2 (Node l' v h')
        
    end 
#pop-options 

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