open Prims
type bdd = {
  hash: Prims.nat ;
  node: node }
and sign =
  | INVERSE 
  | IDENTITY 
and node =
  | Leaf of sign 
  | Node of sign * bdd * Prims.nat * bdd 
let (__proj__Mkbdd__item__hash : bdd -> Prims.nat) =
  fun projectee -> match projectee with | { hash; node = node1;_} -> hash
let (__proj__Mkbdd__item__node : bdd -> node) =
  fun projectee -> match projectee with | { hash; node = node1;_} -> node1
let (uu___is_INVERSE : sign -> Prims.bool) =
  fun projectee -> match projectee with | INVERSE -> true | uu___ -> false
let (uu___is_IDENTITY : sign -> Prims.bool) =
  fun projectee -> match projectee with | IDENTITY -> true | uu___ -> false
let (uu___is_Leaf : node -> Prims.bool) =
  fun projectee -> match projectee with | Leaf _0 -> true | uu___ -> false
let (__proj__Leaf__item___0 : node -> sign) =
  fun projectee -> match projectee with | Leaf _0 -> _0
let (uu___is_Node : node -> Prims.bool) =
  fun projectee ->
    match projectee with | Node (_0, _1, _2, _3) -> true | uu___ -> false
let (__proj__Node__item___0 : node -> sign) =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _0
let (__proj__Node__item___1 : node -> bdd) =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _1
let (__proj__Node__item___2 : node -> Prims.nat) =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _2
let (__proj__Node__item___3 : node -> bdd) =
  fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _3
let (get_low : bdd -> bdd) =
  fun bdd1 -> match bdd1.node with | Node (s, l, v, h) -> l
let (get_high : bdd -> bdd) =
  fun bdd1 -> match bdd1.node with | Node (s, l, v, h) -> h
let (get_var : bdd -> Prims.nat) =
  fun bdd1 -> match bdd1.node with | Node (s, l, v, h) -> v
let (get_sign : bdd -> sign) =
  fun bdd1 -> match bdd1.node with | Node (s, l, v, h) -> s | Leaf s -> s
type hash_type =
  (Prims.bool * Prims.bool * Prims.nat * Prims.nat * Prims.nat)
let (node_hash : node -> hash_type) =
  fun node1 ->
    match node1 with
    | Node (INVERSE, l, v, h) -> (true, true, (l.hash), v, (h.hash))
    | Node (IDENTITY, l, v, h) -> (true, false, (l.hash), v, (h.hash))
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
type 'table is_correct_table = unit
type valid_table = global_table
type ('table, 'bdd1) contains_prop = unit
type ('table, 'node1) is_compatible_node = Obj.t
let (measure : node -> Prims.int) =
  fun node1 ->
    match node1 with
    | Node (s, l, v, h) -> v + Prims.int_one
    | Leaf s -> Prims.int_zero



let (inv : sign -> sign) =
  fun sign1 -> match sign1 with | INVERSE -> IDENTITY | IDENTITY -> INVERSE
let (bdd_of_node : valid_table -> node -> (bdd * valid_table)) =
  fun table ->
    fun node1 ->
      if FStar_Map.contains table.map (node_hash node1)
      then
        let bdd1 = FStar_Map.sel table.map (node_hash node1) in
        Prims.admit ()
      else Prims.admit ()
type bool_function = Prims.nat -> Prims.bool Prims.list -> Prims.bool