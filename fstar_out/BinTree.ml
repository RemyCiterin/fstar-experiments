open Prims
type ('a, 'compare) set =
  | Node of ('a, unit) set * 'a * Prims.nat * ('a, unit) set 
  | Leaf 
let uu___is_Node :
  'a . 'a Compare.comparaison -> ('a, unit) set -> Prims.bool =
  fun compare ->
    fun projectee ->
      match projectee with | Node (left, _1, _2, _3) -> true | uu___ -> false
let __proj__Node__item__left :
  'a . 'a Compare.comparaison -> ('a, unit) set -> ('a, unit) set =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> left
let __proj__Node__item___1 :
  'a . 'a Compare.comparaison -> ('a, unit) set -> 'a =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> _1
let __proj__Node__item___2 :
  'a . 'a Compare.comparaison -> ('a, unit) set -> Prims.nat =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> _2
let __proj__Node__item___3 :
  'a . 'a Compare.comparaison -> ('a, unit) set -> ('a, unit) set =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> _3
let uu___is_Leaf :
  'a . 'a Compare.comparaison -> ('a, unit) set -> Prims.bool =
  fun compare ->
    fun projectee -> match projectee with | Leaf -> true | uu___ -> false
let height : 'a . 'a Compare.comparaison -> ('a, unit) set -> Prims.nat =
  fun f ->
    fun s -> match s with | Node (l, k, s1, r) -> s1 | Leaf -> Prims.int_zero
let key : 'a . 'a Compare.comparaison -> ('a, unit) set -> 'a =
  fun f -> fun s -> match s with | Node (uu___, k, uu___1, uu___2) -> k
let left : 'a . 'a Compare.comparaison -> ('a, unit) set -> ('a, unit) set =
  fun f ->
    fun input -> match input with | Node (l, uu___, uu___1, uu___2) -> l
let right : 'a . 'a Compare.comparaison -> ('a, unit) set -> ('a, unit) set =
  fun f ->
    fun input -> match input with | Node (uu___, uu___1, uu___2, r) -> r
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then x else y
let rec member :
  'a . 'a Compare.comparaison -> 'a -> ('a, unit) set -> Prims.bool =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | Leaf -> false
        | Node (l, k, uu___, r) ->
            ((Compare.uu___is_EQ (f x k)) || (member f x l)) ||
              (member f x r)
let delta :
  'a .
    'a Compare.comparaison -> ('a, unit) set -> ('a, unit) set -> Prims.nat
  =
  fun f ->
    fun l ->
      fun r ->
        if (height f l) > (height f r)
        then (height f l) - (height f r)
        else (height f r) - (height f l)
type ('a, 'f, 'input) is_avl = Obj.t
let make :
  'a .
    'a Compare.comparaison ->
      ('a, unit) set -> 'a -> ('a, unit) set -> ('a, unit) set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          Node (l, k, (Prims.int_one + (max (height f l) (height f r))), r)

