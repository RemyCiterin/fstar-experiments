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
type hash_type =
  (Prims.bool * Prims.bool * Prims.nat * Prims.nat * Prims.nat)
let (node_hash : node -> hash_type) =
  fun node1 ->
    match node1 with
    | Node (INVERSE, l, v, h) -> (true, true, (l.tag), v, (h.tag))
    | Node (IDENTITY, l, v, h) -> (true, false, (l.tag), v, (h.tag))
    | Leaf (INVERSE) ->
        (false, true, Prims.int_zero, Prims.int_zero, Prims.int_zero)
    | Leaf (IDENTITY) ->
        (false, false, Prims.int_zero, Prims.int_zero, Prims.int_zero)
type global_table = {
  map: (hash_type, bdd) FStar_Map.t ;
  size: Prims.nat }
let (__proj__Mkglobal_table__item__map :
  global_table -> (hash_type, bdd) FStar_Map.t) =
  fun projectee -> match projectee with | { map; size;_} -> map
let (__proj__Mkglobal_table__item__size : global_table -> Prims.nat) =
  fun projectee -> match projectee with | { map; size;_} -> size
type 'table is_valid = unit