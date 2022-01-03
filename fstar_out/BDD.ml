open Prims
type bdd' = {
  tag: Prims.nat ;
  node: node' }
and node' =
  | One 
  | Zero 
  | Node of bdd' * Prims.nat * bdd' 
let (__proj__Mkbdd'__item__tag : bdd' -> Prims.nat) =
  fun projectee -> match projectee with | { tag; node;_} -> tag
let (__proj__Mkbdd'__item__node : bdd' -> node') =
  fun projectee -> match projectee with | { tag; node;_} -> node
let (uu___is_One : node' -> Prims.bool) =
  fun projectee -> match projectee with | One -> true | uu___ -> false
let (uu___is_Zero : node' -> Prims.bool) =
  fun projectee -> match projectee with | Zero -> true | uu___ -> false
let (uu___is_Node : node' -> Prims.bool) =
  fun projectee ->
    match projectee with | Node (_0, _1, _2) -> true | uu___ -> false
let (__proj__Node__item___0 : node' -> bdd') =
  fun projectee -> match projectee with | Node (_0, _1, _2) -> _0
let (__proj__Node__item___1 : node' -> Prims.nat) =
  fun projectee -> match projectee with | Node (_0, _1, _2) -> _1
let (__proj__Node__item___2 : node' -> bdd') =
  fun projectee -> match projectee with | Node (_0, _1, _2) -> _2
let (get_low : bdd' -> bdd') =
  fun bdd -> match bdd.node with | Node (l, v, h) -> l
let (get_high : bdd' -> bdd') =
  fun bdd -> match bdd.node with | Node (l, v, h) -> h
let (get_var : bdd' -> Prims.nat) =
  fun bdd -> match bdd.node with | Node (l, v, h) -> v
let (is_leaf : node' -> Prims.bool) =
  fun n ->
    match n with
    | Zero -> true
    | One -> true
    | Node (uu___, uu___1, uu___2) -> false
type 'node is_obdd = Obj.t
type bdd = bdd'
type node = node'
let rec (eval_node : (Prims.nat -> Prims.bool) -> node' -> Prims.bool) =
  fun f ->
    fun node1 ->
      match node1 with
      | One -> true
      | Zero -> false
      | Node (l, v, h) ->
          if f v then eval_node f h.node else eval_node f l.node
let (compareInt : Prims.int Compare.comparaison) =
  fun x ->
    fun y ->
      if x > y then Compare.GT else if x < y then Compare.LT else Compare.EQ
let (compareNode : node Compare.comparaison) =
  fun l ->
    fun h ->
      match (l, h) with
      | (Node (ll, lv, lh), Node (hl, hv, hh)) ->
          (match compareInt ll.tag hl.tag with
           | Compare.EQ ->
               (match compareInt lh.tag hh.tag with
                | Compare.EQ -> compareInt lv hv
                | x -> x)
           | x -> x)
      | (Zero, Node (uu___, uu___1, uu___2)) -> Compare.GT
      | (One, Node (uu___, uu___1, uu___2)) -> Compare.GT
      | (Node (uu___, uu___1, uu___2), Zero) -> Compare.LT
      | (Node (uu___, uu___1, uu___2), One) -> Compare.LT
      | (Zero, One) -> Compare.LT
      | (One, Zero) -> Compare.GT
      | (uu___, uu___1) -> Compare.EQ
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
let (measure : node' -> Prims.nat) =
  fun node1 ->
    match node1 with
    | Zero -> Prims.int_zero
    | One -> Prims.int_zero
    | Node (uu___, v, uu___1) -> v + Prims.int_one
type ('table, 'node1) compatible_node = Obj.t


let (makeNode : global_table -> node' -> (bdd * global_table)) =
  fun table ->
    fun node1 ->
      match node1 with
      | One -> ({ tag = Prims.int_one; node = node1 }, table)
      | Zero -> ({ tag = Prims.int_zero; node = node1 }, table)
      | Node (l, v, h) ->
          if l.tag = h.tag
          then (l, table)
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
let rec (notBDD : global_table -> bdd -> (bdd * global_table)) =
  fun table ->
    fun input ->
      match input.node with
      | One -> makeNode table Zero
      | Zero -> makeNode table One
      | Node (l, v, h) ->
          let uu___ = notBDD table l in
          (match uu___ with
           | (l', table1) ->
               let uu___1 = notBDD table1 h in
               (match uu___1 with
                | (h', table2) -> makeNode table2 (Node (l', v, h'))))
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then x else y
type 'f apply_map = ((bdd * bdd), bdd, unit) MapAVL.map
type ('f, 'table, 'map) is_valid_apply_map = unit
let (from_bool : Prims.bool -> bdd) =
  fun b ->
    if b
    then { tag = Prims.int_one; node = One }
    else { tag = Prims.int_zero; node = Zero }
let rec (apply_with :
  global_table ->
    (Prims.bool -> Prims.bool -> Prims.bool) ->
      unit apply_map -> bdd -> bdd -> (bdd * global_table * unit apply_map))
  =
  fun table ->
    fun f ->
      fun local ->
        fun l ->
          fun r ->
            match ((l.node), (r.node)) with
            | (One, One) -> ((from_bool (f true true)), table, local)
            | (Zero, One) -> ((from_bool (f false true)), table, local)
            | (One, Zero) -> ((from_bool (f true false)), table, local)
            | (Zero, Zero) -> ((from_bool (f false false)), table, local)
            | (Zero, uu___) ->
                (match ((f false true), (f false false)) with
                 | (false, false) ->
                     ({ tag = Prims.int_zero; node = Zero }, table, local)
                 | (true, true) ->
                     ({ tag = Prims.int_one; node = One }, table, local)
                 | (true, false) -> (r, table, local)
                 | (false, true) ->
                     let uu___1 = notBDD table r in
                     (match uu___1 with | (r', table') -> (r', table', local)))
            | (One, uu___) ->
                (match ((f true true), (f true false)) with
                 | (false, false) ->
                     ({ tag = Prims.int_zero; node = Zero }, table, local)
                 | (true, true) ->
                     ({ tag = Prims.int_one; node = One }, table, local)
                 | (true, false) -> (r, table, local)
                 | (false, true) ->
                     let uu___1 = notBDD table r in
                     (match uu___1 with | (r', table') -> (r', table', local)))
            | (uu___, Zero) ->
                (match ((f true false), (f false false)) with
                 | (false, false) ->
                     ({ tag = Prims.int_zero; node = Zero }, table, local)
                 | (true, true) ->
                     ({ tag = Prims.int_one; node = One }, table, local)
                 | (true, false) -> (l, table, local)
                 | (false, true) ->
                     let uu___1 = notBDD table l in
                     (match uu___1 with | (l', table') -> (l', table', local)))
            | (uu___, One) ->
                (match ((f true true), (f false true)) with
                 | (false, false) ->
                     ({ tag = Prims.int_zero; node = Zero }, table, local)
                 | (true, true) ->
                     ({ tag = Prims.int_one; node = One }, table, local)
                 | (true, false) -> (l, table, local)
                 | (false, true) ->
                     let uu___1 = notBDD table l in
                     (match uu___1 with | (l', table') -> (l', table', local)))
            | (Node (ll, lv, lh), Node (rl, rv, rh)) ->
                (match MapAVL.find
                         (fun uu___ ->
                            fun uu___1 ->
                              match (uu___, uu___1) with
                              | ((b1, b2), (b3, b4)) ->
                                  (match compareInt b1.tag b3.tag with
                                   | Compare.EQ -> compareInt b2.tag b4.tag
                                   | x -> x)) (l, r) local
                 with
                 | FStar_Pervasives_Native.None ->
                     let uu___ =
                       if lv = rv
                       then
                         let uu___1 = apply_with table f local ll rl in
                         match uu___1 with
                         | (l', table1, local1) ->
                             let uu___2 = apply_with table1 f local1 lh rh in
                             (match uu___2 with
                              | (r', table2, local2) ->
                                  let uu___3 =
                                    makeNode table2 (Node (l', lv, r')) in
                                  (match uu___3 with
                                   | (out, table3) -> (out, table3, local2)))
                       else
                         if lv > rv
                         then
                           (let uu___2 = apply_with table f local ll r in
                            match uu___2 with
                            | (l', table1, local1) ->
                                let uu___3 = apply_with table1 f local1 lh r in
                                (match uu___3 with
                                 | (r', table2, local2) ->
                                     let uu___4 =
                                       makeNode table2 (Node (l', lv, r')) in
                                     (match uu___4 with
                                      | (out, table3) ->
                                          (out, table3, local2))))
                         else
                           (let uu___3 = apply_with table f local l rl in
                            match uu___3 with
                            | (l', table1, local1) ->
                                let uu___4 = apply_with table1 f local1 l rh in
                                (match uu___4 with
                                 | (r', table2, local2) ->
                                     let uu___5 =
                                       makeNode table2 (Node (l', rv, r')) in
                                     (match uu___5 with
                                      | (out, table3) ->
                                          (out, table3, local2)))) in
                     (match uu___ with
                      | (out, table', local') ->
                          let local42 =
                            MapAVL.add
                              (fun uu___1 ->
                                 fun uu___2 ->
                                   match (uu___1, uu___2) with
                                   | ((b1, b2), (b3, b4)) ->
                                       (match compareInt b1.tag b3.tag with
                                        | Compare.EQ ->
                                            compareInt b2.tag b4.tag
                                        | x -> x)) local' (l, r) out in
                          (out, table', local42))
                 | FStar_Pervasives_Native.Some (n, b) -> (b, table, local))
let (apply :
  global_table ->
    (Prims.bool -> Prims.bool -> Prims.bool) ->
      bdd -> bdd -> (bdd * global_table))
  =
  fun table ->
    fun f ->
      fun l ->
        fun r ->
          let uu___ = apply_with table f BinTree.Leaf l r in
          match uu___ with | (bdd'1, table', uu___1) -> (bdd'1, table')
type ('n, 'b) restrict_map = (bdd, bdd, unit) MapAVL.map
type ('n, 'b, 'table, 'map) is_valid_restrict_map = unit
let (add_in_restrict_map_lemma :
  Prims.nat ->
    Prims.bool ->
      global_table ->
        (unit, unit) restrict_map -> bdd -> bdd -> (unit, unit) restrict_map)
  =
  fun n ->
    fun b ->
      fun table ->
        fun map ->
          fun input ->
            fun out ->
              MapAVL.add (fun b1 -> fun b2 -> compareInt b1.tag b2.tag) map
                input out

let rec (restrict_with :
  global_table ->
    Prims.nat ->
      Prims.bool ->
        (unit, unit) restrict_map ->
          bdd -> (bdd * global_table * (unit, unit) restrict_map))
  =
  fun table ->
    fun n ->
      fun b ->
        fun map ->
          fun input ->
            if (measure input.node) < (n + Prims.int_one)
            then (input, table, map)
            else
              (match input.node with
               | Node (l, k, h) ->
                   if k = n
                   then (if b then (h, table, map) else (l, table, map))
                   else
                     (let uu___2 =
                        let uu___3 = restrict_with table n b map l in
                        match uu___3 with
                        | (l', table1, map1) ->
                            let uu___4 = restrict_with table1 n b map1 h in
                            (match uu___4 with
                             | (h', table2, map2) ->
                                 let uu___5 =
                                   makeNode table2 (Node (l', k, h')) in
                                 (match uu___5 with
                                  | (out, table3) -> (out, table3, map2))) in
                      match uu___2 with
                      | (out, table', map') ->
                          let map42 =
                            MapAVL.add
                              (fun b1 -> fun b2 -> compareInt b1.tag b2.tag)
                              map' input out in
                          (out, table', map42)))
let (restrict :
  global_table -> Prims.nat -> Prims.bool -> bdd -> (bdd * global_table)) =
  fun table ->
    fun n ->
      fun b ->
        fun input ->
          let uu___ = restrict_with table n b BinTree.Leaf input in
          match uu___ with | (bdd'1, table', uu___1) -> (bdd'1, table')