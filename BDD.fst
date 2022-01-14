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
irreducible let makeNode (table: global_table) (node:node') : 
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


irreducible let rec notBDD (table:global_table) (input:bdd) : 
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

let max x y = if x > y then x else y

type apply_map (f:bool->bool->bool) = m:M.map (bdd&bdd) bdd (
        fun (b1, b2) (b3, b4) -> match compareInt b1.tag b3.tag with 
        | EQ -> compareInt b2.tag b4.tag 
        | x -> x
    )


let is_valid_apply_map (#f:bool->bool->bool) (table:global_table) (map: apply_map f) : prop = 
    forall (b1:bdd) (b2:bdd) (b3:bdd). M.member (b1, b2) b3 map ==> (
            (measure b3.node <= max (measure b1.node) (measure b2.node)) /\
            (forall g. f (eval_node g b1.node) (eval_node g b2.node) == eval_node g b3.node) /\
            M.member b1.node b1 table.map /\
            M.member b2.node b2 table.map /\
            M.member b3.node b3 table.map
    )

let from_bool : bool -> bdd = fun b -> 
    if b then {tag=1; node=One} else {tag=0; node=Zero}

#push-options "--z3rlimit 200"
irreducible let rec apply_with (table: global_table) (f:bool->bool->bool) (local:apply_map f) (l:bdd) (r:bdd) : 
    Pure 
        (bdd&global_table&apply_map f)

        (requires 
            is_valid_apply_map table local /\ 
            M.member l.node l table.map /\ 
            M.member r.node r table.map
        )

        (ensures fun out -> (
            let bdd', table', local' = out in
            is_valid_apply_map table' local' /\ 
            M.member bdd'.node bdd' table'.map /\ 
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall g. eval_node g bdd'.node == f (eval_node g l.node) (eval_node g r.node)) /\ 
            (measure bdd'.node <= max (measure l.node) (measure r.node))
        )) 
        
        (decreases (
            measure l.node + measure r.node
        ))
        
        = 

        match l.node, r.node with 
        | One, One   -> from_bool (f true  true ), table, local
        | Zero, One  -> from_bool (f false true ), table, local
        | One, Zero  -> from_bool (f true  false), table, local
        | Zero, Zero -> from_bool (f false false), table, local
        | Zero, _ -> 
        begin 
            match f false true, f false false with 
            | false, false -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) == false); {tag=0; node=Zero}, table, local end 
            | true , true  -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) == true ); {tag=1; node=One }, table, local end  
            | true , false -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) == eval_node g n); r, table, local end 
            | false, true  -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) <> eval_node g n); 
                let r', table' = notBDD table r in 
                r', table', local
            end
        end
        | One, _ ->
        begin 
            match f true true, f true false with 
            | false, false -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) == false); {tag=0; node=Zero}, table, local end 
            | true , true  -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) == true ); {tag=1; node=One }, table, local end  
            | true , false -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) == eval_node g n); r, table, local end 
            | false, true  -> begin assert (forall n g. f (eval_node g l.node) (eval_node g n) <> eval_node g n); 
                let r', table' = notBDD table r in 
                r', table', local
            end
        end 
        | _, Zero -> 
        begin 
            match f true false, f false false with 
            | false, false -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) == false); {tag=0; node=Zero}, table, local end 
            | true , true  -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) == true ); {tag=1; node=One }, table, local end  
            | true , false -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) == eval_node g n); l, table, local end 
            | false, true  -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) <> eval_node g n); 
                let l', table' = notBDD table l in 
                l', table', local
            end
        end
        | _, One ->
        begin 
            match f true true, f false true with 
            | false, false -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) == false); {tag=0; node=Zero}, table, local end 
            | true , true  -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) == true ); {tag=1; node=One }, table, local end  
            | true , false -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) == eval_node g n); l, table, local end 
            | false, true  -> begin assert (forall n g. f (eval_node g n) (eval_node g r.node) <> eval_node g n); 
                let l', table' = notBDD table l in 
                l', table', local
            end
        end 
        | Node ll lv lh, Node rl rv rh -> 
        begin 
            match M.find (l, r) local with
            | None -> 
            begin 
                let out, table', local' =
                    if lv = rv then 
                    begin
                        let l', table1, local1 = apply_with table  f local  ll rl in
                        let r', table2, local2 = apply_with table1 f local1 lh rh in  
                        let out, table3 = makeNode table2 (Node l' lv r') in 
                        out, table3, local2

                    end 
                    else if lv > rv then 
                    begin 
                        let l', table1, local1 = apply_with table  f local  ll r in
                        let r', table2, local2 = apply_with table1 f local1 lh r in
                        let out, table3 = makeNode table2 (Node l' lv r') in 
                        out, table3, local2
                    end 
                    else 
                    begin 
                        let l', table1, local1 = apply_with table  f local  l rl in
                        let r', table2, local2 = apply_with table1 f local1 l rh in
                        let out, table3 = makeNode table2 (Node l' rv r') in 
                        out, table3, local2
                    end 
                in 
                let local42 = M.add local' (l, r) out in 
                assert (forall g. eval_node g out.node == f (eval_node g l.node) (eval_node g r.node));
                out, table', local42
            end 
            | Some (n, b) -> 
            begin 
                assert (M.member n b local); 
                assert (M.member (fst n).node (fst n) table.map);
                assert (M.member (snd n).node (snd n) table.map);
                assert ((fst n).tag == l.tag); 
                assert ((snd n).tag == r.tag); 
                assert (n == (l, r));
                b, table, local
            end 
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
    
    = let bdd', table', _ = apply_with table f (BinTree.Leaf) l r in 
    bdd', table'

type restrict_map (n: nat) (b:bool) = m:M.map bdd bdd (
        fun b1 b2 -> compareInt b1.tag b2.tag
    )

let is_valid_restrict_map (#n: nat) (#b:bool) (table:global_table) (map: restrict_map n b) : prop = 
    forall (b1:bdd) (b2:bdd). M.member b1 b2 map ==> (
            (forall f. eval_node f b2.node == eval_node (fun i -> if i = n then b else f i) b1.node) /\
            measure b2.node <= measure b1.node /\
            M.member b1.node b1 table.map /\
            M.member b2.node b2 table.map
    )

#push-options "--z3rlimit 100"
irreducible let add_in_restrict_map_lemma 
    (#n: nat) (#b:bool) (table:global_table) (map: restrict_map n b) (input:bdd) (out:bdd) : 
    Pure 
        (restrict_map n b)
        (requires 
            is_valid_restrict_map #n #b table map /\
            (forall f. eval_node f out.node == eval_node (fun i -> if i = n then b else f i) input.node) /\
            measure out.node <= measure input.node /\ 
            M.member input.node input table.map /\
            M.member out.node out table.map
        )
        (ensures fun map' -> (
            is_valid_restrict_map #n #b table map'
        ))
    = M.add map input out
#pop-options


let rec measure_lemma (#n: nat) (#b:bool) (input:bdd) :
    Lemma 
        (forall f. measure input.node < n+1 ==> eval_node (fun i -> if i = n then b else f i) input.node == eval_node f input.node)
    
    = match input.node with 
    | Zero | One -> ()
    | Node l k h -> 
    begin 
        assert (measure l.node < measure input.node);
        assert (measure h.node < measure input.node);
        measure_lemma #n #b h;
        measure_lemma #n #b l
    end 

#push-options "--z3rlimit 200"
irreducible let rec restrict_with (table:global_table) (n:nat) (b:bool) (map:restrict_map n b) (input:bdd) :
    Pure 
        (bdd&global_table&restrict_map n b)

        (requires is_valid_restrict_map table map /\  M.member input.node input table.map)

        (ensures fun out -> (
            let bdd', table', map' = out in 
            is_valid_restrict_map table' map'  /\
            M.member bdd'.node bdd' table'.map /\
            measure bdd'.node <= measure input.node /\
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall f. eval_node f bdd'.node == eval_node (fun i -> if i = n then b else f i) input.node)
        ))

        (decreases (measure input.node))
    
    = if measure input.node < n+1 then 
    begin 
        measure_lemma #n #b input;
        (input, table, map) 
    end else begin 
        match input.node with 
        | Node l k h -> 
        begin
            measure_lemma #n #b l;
            measure_lemma #n #b h;
            if k = n then if b then (h, table, map) else (l, table, map) else 
            let (out, table', map') = 
                let (l', table1, map1) = restrict_with table  n b map  l in 
                let (h', table2, map2) = restrict_with table1 n b map1 h in 
                let (out, table3) = makeNode table2 (Node l' k h') in
                (out, table3, map2)
            in 
            let map42 = M.add map' input out in 
            assert (forall f. eval_node f out.node == eval_node (fun i -> if i = n then b else f i) input.node);
            assert (forall x y. (M.member x.node x table'.map /\ M.member y.node y table'.map) ==> (x.tag == y.tag ==> x == y));
            assert (forall x y. M.member x y map42 ==> (M.member x.node x table'.map /\ M.member y.node y table'.map));
            assert (forall x y. M.member x y map42 <==> (if x.tag = input.tag then (x == input /\ y == out) else M.member x y map'));

            assert (is_valid_restrict_map #n #b table' map');
            //assert (forall x y. M.member x y map'  ==> (forall f. eval_node f y.node == eval_node (fun i -> if n = i then b else f i) x.node));
            //assert (forall x y. M.member x y map42 ==> (forall f. eval_node f y.node == eval_node (fun i -> if n = i then b else f i) x.node));


            //assert (is_valid_restrict_map #n #b table' map42);
            (out, table', map42)
        end 
    end 

#pop-options 

let restrict (table:global_table) (n:nat) (b:bool) (input:bdd) :
    Pure 
        (bdd&global_table)

        (requires M.member input.node input table.map)

        (ensures fun out -> (
            let bdd', table' = out in 
            M.member bdd'.node bdd' table'.map /\
            measure bdd'.node <= measure input.node /\ 
            (forall n b. M.member n b table.map ==> M.member n b table'.map) /\ 
            (forall f. eval_node f bdd'.node == eval_node (fun i -> if i = n then b else f i) input.node)
        ))
    
    = let (bdd', table', _) = restrict_with table n b BinTree.Leaf input in (bdd', table')

let rec measure_lemma_with (#n: nat) (#b:bool) (f:nat->bool) (input:bdd) :
    Lemma 
        (measure input.node < n+1 ==> eval_node (fun i -> if i = n then b else f i) input.node == eval_node f input.node)

        //[SMTPat (eval_node (fun i -> if i = n then b else f i))]
    
    = match input.node with 
    | Zero | One -> ()
    | Node l k h -> 
    begin 
        assert (measure l.node < measure input.node);
        assert (measure h.node < measure input.node);
        measure_lemma_with #n #b f h;
        measure_lemma_with #n #b f l
    end 

#push-options "--z3rlimit 100"
let rec simplify (table:global_table) (b1:bdd) (b2:bdd) : 
    Pure 
        (bdd&global_table)

        (requires 
            b2.node <> Zero /\
            M.member b1.node b1 table.map /\
            M.member b2.node b2 table.map
        )

        (ensures fun out -> (
            let bdd', table' = out  in 
            M.member bdd'.node bdd' table'.map /\ 
            measure bdd'.node <= (max (measure b1.node) (measure b2.node)) /\
            (forall x y. M.member x y table.map ==> M.member x y table'.map) /\
            (forall f. (eval_node f b1.node /\ eval_node f b2.node) ==> (eval_node f bdd'.node) ==> (eval_node f b2.node ==> eval_node f b1.node))
        ))

        (decreases (
            measure b1.node + measure b2.node
        ))
    
    = match b1.node, b2.node with
    | Zero, _ | One, _ | _, One -> (b1, table)
    | Node l1 v1 h1, Node l2 v2 h2 -> begin 
        if v1 > v2 then begin 
            measure_lemma #v1 #false b2;
            measure_lemma #v1 #true  b2;
            let l, table1 = simplify table  l1 b2 in 
            let h, table2 = simplify table1 h1 b2 in 
            makeNode table2 (Node l v1 h)


        end else if v2 > v1 then begin
            measure_lemma #v2 #false b1;
            measure_lemma #v2 #true  b1;

            if l2.node = Zero then begin
                assert (h2.node <> Zero);
                simplify table b1 h2
            end else 
            if h2.node = Zero then begin
                assert (l2.node <> Zero);
                simplify table b1 l2
            end else
            
            let h, table1 = simplify table  b1 h2 in 
            let l, table2 = simplify table1 b1 l2 in 
            makeNode table2 (Node l v2 h)

        end else begin 
            if l2.node = Zero then begin 
                assert (h2.node <> Zero);
                simplify table h1 h2
            end else 
            if h2.node = Zero then begin 
                assert (l2.node <> Zero);
                simplify table l1 l2 
            end else 

            let h, table1 = simplify table  h1 h2 in 
            let l, table2 = simplify table1 l1 l2 in 
            makeNode table2 (Node l v2 h)
        end 
    end 
#pop-options