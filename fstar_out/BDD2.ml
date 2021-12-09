open Prims
type bdd' = {
  tag: Prims.nat ;
  node: node' }
and sign =
  | INVERSE 
  | IDENTITY 
and node' =
  | Leaf of sign 
  | Node of sign * bdd' * Prims.nat * bdd' 
let (__proj__Mkbdd'__item__tag : bdd' -> Prims.nat) =
  fun projectee -> match projectee with | { tag; node;_} -> tag
let (__proj__Mkbdd'__item__node : bdd' -> node') =
  fun projectee -> match projectee with | { tag; node;_} -> node
let (uu___is_INVERSE : sign -> Prims.bool) =
  fun projectee -> match projectee with | INVERSE -> true | uu___ -> false
let (uu___is_IDENTITY : sign -> Prims.bool) =
  fun projectee -> match projectee with | IDENTITY -> true | uu___ -> false
let (uu___is_Leaf : node' -> Prims.bool) =
  fun projectee -> match projectee with | Leaf _0 -> true | uu___ -> false
let (__proj__Leaf__item___0 : node' -> sign) =
  fun projectee -> match projectee with | Leaf _0 -> _0
let (uu___is_Node : node' -> Prims.bool) =
  fun projectee ->
    match projectee with | Node (_0, _1, _2, _3) -> true | uu___ -> false
let (__proj__Node__item___0 : node' -> sign) =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _0
let (__proj__Node__item___1 : node' -> bdd') =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _1
let (__proj__Node__item___2 : node' -> Prims.nat) =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _2
let (__proj__Node__item___3 : node' -> bdd') =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _3
let (get_low : bdd' -> bdd') =
  fun bdd -> match bdd.node with | Node (s, l, v, h) -> l
let (get_high : bdd' -> bdd') =
  fun bdd -> match bdd.node with | Node (s, l, v, h) -> h
let (get_var : bdd' -> Prims.nat) =
  fun bdd -> match bdd.node with | Node (s, l, v, h) -> v
let (get_sign : bdd' -> sign) =
  fun bdd -> match bdd.node with | Node (s, l, v, h) -> s | Leaf s -> s
type 'node is_obdd = Obj.t
type bdd = bdd'
type node = node'
let rec (eval_node : (Prims.nat -> Prims.bool) -> node' -> Prims.bool) =
  fun f ->
    fun node1 ->
      match node1 with
      | Leaf (IDENTITY) -> true
      | Leaf (INVERSE) -> false
      | Node (IDENTITY, l, v, h) ->
          if f v then eval_node f h.node else eval_node f l.node
      | Node (INVERSE, l, v, h) ->
          Prims.op_Negation
            (if f v then eval_node f h.node else eval_node f l.node)
let (compareInt : Prims.int Compare.comparaison) =
  fun x ->
    fun y ->
      if x > y then Compare.GT else if x < y then Compare.LT else Compare.EQ
let (compareNode : node Compare.comparaison) =
  fun l ->
    fun h ->
      match (l, h) with
      | (Node (ls, ll, lv, lh), Node (hs, hl, hv, hh)) ->
          (match (ls, hs) with
           | (IDENTITY, INVERSE) -> Compare.LT
           | (INVERSE, IDENTITY) -> Compare.GT
           | (uu___, uu___1) ->
               (match compareInt ll.tag hl.tag with
                | Compare.EQ ->
                    (match compareInt lh.tag hh.tag with
                     | Compare.EQ -> compareInt lv hv
                     | x -> x)
                | x -> x))
      | (Leaf ls, Leaf hs) ->
          (match (ls, hs) with
           | (IDENTITY, INVERSE) -> Compare.LT
           | (INVERSE, IDENTITY) -> Compare.GT
           | (uu___, uu___1) -> Compare.EQ)
      | (Leaf ls, uu___) -> Compare.GT
      | (uu___, Leaf hs) -> Compare.LT
type global_table' = {
  map: (node, bdd, unit) MapAVL.map ;
  size: Prims.nat }
let (__proj__Mkglobal_table'__item__map :
  global_table' -> (node, bdd, unit) MapAVL.map) =
  fun projectee -> match projectee with | { map; size;_} -> map
let (__proj__Mkglobal_table'__item__size : global_table' -> Prims.nat) =
  fun projectee -> match projectee with | { map; size;_} -> size
type 'table is_valid_table = unit
type global_table = global_table'
type ('table, 'node1) compatible_node = Obj.t


let (inv : sign -> sign) =
  fun s -> match s with | INVERSE -> IDENTITY | IDENTITY -> INVERSE
let rec (makeNode : global_table -> node' -> (bdd * global_table)) =
  fun table ->
    fun node1 ->
      match node1 with
      | Leaf (IDENTITY) -> ({ tag = Prims.int_zero; node = node1 }, table)
      | Leaf (INVERSE) -> ({ tag = Prims.int_one; node = node1 }, table)
      | Node (s, l, v, h) ->
          if l.tag = h.tag
          then
            (match (s, (l.node)) with
             | (IDENTITY, uu___) -> (l, table)
             | (INVERSE, Node (ls, ll, lv, lh)) ->
                 makeNode table (Node ((inv ls), ll, lv, lh))
             | (INVERSE, Leaf ls) -> makeNode table (Leaf (inv ls)))
          else
            (match MapAVL.find compareNode node1 table.map with
             | FStar_Pervasives_Native.Some (n, b) -> (b, table)
             | FStar_Pervasives_Native.None ->
                 let bdd1 = { tag = (table.size); node = node1 } in
                 let table' =
                   {
                     map = (MapAVL.add compareNode table.map node1 bdd1);
                     size = (table.size + Prims.int_one)
                   } in
                 (bdd1, table'))
let (notBDD : global_table -> bdd -> (bdd * global_table)) =
  fun table ->
    fun input ->
      match input.node with
      | Leaf s -> makeNode table (Leaf (inv s))
      | Node (s, l, v, h) -> makeNode table (Node ((inv s), l, v, h))
let (apply :
  global_table ->
    (Prims.bool -> Prims.bool -> Prims.bool) ->
      bdd -> bdd -> (bdd * global_table))
  = fun table -> fun f -> fun l -> fun r -> Prims.admit ()
let (restrict :
  global_table -> Prims.nat -> Prims.bool -> bdd -> (bdd * global_table)) =
  fun table -> fun n -> fun b -> fun input -> Prims.admit ()