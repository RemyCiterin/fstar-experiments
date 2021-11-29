open Prims
let cmp :
  'a 'b .
    'a Compare.comparaison -> ('a * 'b) -> ('a * 'b) -> Compare.ordering
  =
  fun f ->
    fun x ->
      fun y ->
        f (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y)
type ('a, 'b, 'compare) set =
  | Node of ('a, 'b, unit) set * ('a * 'b) * Prims.nat * ('a, 'b, unit) set 
  | Leaf 
let uu___is_Node :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> Prims.bool =
  fun compare ->
    fun projectee ->
      match projectee with | Node (_0, _1, _2, _3) -> true | uu___ -> false
let __proj__Node__item___0 :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> ('a, 'b, unit) set
  =
  fun compare ->
    fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _0
let __proj__Node__item___1 :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> ('a * 'b) =
  fun compare ->
    fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _1
let __proj__Node__item___2 :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> Prims.nat =
  fun compare ->
    fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _2
let __proj__Node__item___3 :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> ('a, 'b, unit) set
  =
  fun compare ->
    fun projectee -> match projectee with | Node (_0, _1, _2, _3) -> _3
let uu___is_Leaf :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> Prims.bool =
  fun compare ->
    fun projectee -> match projectee with | Leaf -> true | uu___ -> false
let height :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> Prims.nat =
  fun f ->
    fun s -> match s with | Node (l, k, s1, r) -> s1 | Leaf -> Prims.int_zero
let key : 'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> ('a * 'b) =
  fun f -> fun s -> match s with | Node (uu___, k, uu___1, uu___2) -> k
let left :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> ('a, 'b, unit) set
  =
  fun f ->
    fun input -> match input with | Node (l, uu___, uu___1, uu___2) -> l
let right :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) set -> ('a, 'b, unit) set
  =
  fun f ->
    fun input -> match input with | Node (uu___, uu___1, uu___2, r) -> r
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then x else y
type ('a, 'b, 'f, 'x, 'input) member = Obj.t
let delta :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) set -> ('a, 'b, unit) set -> Prims.nat
  =
  fun f ->
    fun l ->
      fun r ->
        if (height f l) > (height f r)
        then (height f l) - (height f r)
        else (height f r) - (height f l)
type ('a, 'b, 'f, 'input) is_avl = Obj.t
let make :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) set ->
        ('a * 'b) -> ('a, 'b, unit) set -> ('a, 'b, unit) set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          Node (l, k, (Prims.int_one + (max (height f l) (height f r))), r)
