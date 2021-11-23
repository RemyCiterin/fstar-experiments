open Prims
type ordering =
  | GT 
  | LT 
  | EQ 
let (uu___is_GT : ordering -> Prims.bool) =
  fun projectee -> match projectee with | GT -> true | uu___ -> false
let (uu___is_LT : ordering -> Prims.bool) =
  fun projectee -> match projectee with | LT -> true | uu___ -> false
let (uu___is_EQ : ordering -> Prims.bool) =
  fun projectee -> match projectee with | EQ -> true | uu___ -> false
let (is_GE : ordering -> Prims.bool) =
  fun a -> (uu___is_GT a) || (uu___is_EQ a)
let (is_LE : ordering -> Prims.bool) =
  fun a -> (uu___is_LT a) || (uu___is_EQ a)
type ('a, 'f) reflexivity = unit
type ('a, 'f) symmetry_EQ = unit
type ('a, 'f) anti_symetry = unit
type ('a, 'f) transitivity_LT = unit
type ('a, 'f) transitivity_GT = unit
type ('a, 'f) transitivity_EQ = unit
type ('a, 'f) transitivity = unit
type 'a comparaison = 'a -> 'a -> ordering
type ('a, 'compare) set =
  | Node of ('a, unit) set * 'a * Prims.nat * ('a, unit) set 
  | Leaf 
let uu___is_Node : 'a . 'a comparaison -> ('a, unit) set -> Prims.bool =
  fun compare ->
    fun projectee ->
      match projectee with | Node (left, _1, _2, _3) -> true | uu___ -> false
let __proj__Node__item__left :
  'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> left
let __proj__Node__item___1 : 'a . 'a comparaison -> ('a, unit) set -> 'a =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> _1
let __proj__Node__item___2 :
  'a . 'a comparaison -> ('a, unit) set -> Prims.nat =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> _2
let __proj__Node__item___3 :
  'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set =
  fun compare ->
    fun projectee -> match projectee with | Node (left, _1, _2, _3) -> _3
let uu___is_Leaf : 'a . 'a comparaison -> ('a, unit) set -> Prims.bool =
  fun compare ->
    fun projectee -> match projectee with | Leaf -> true | uu___ -> false
let height : 'a . 'a comparaison -> ('a, unit) set -> Prims.nat =
  fun f ->
    fun s -> match s with | Node (l, k, s1, r) -> s1 | Leaf -> Prims.int_zero
let key : 'a . 'a comparaison -> ('a, unit) set -> 'a =
  fun f -> fun s -> match s with | Node (uu___, k, uu___1, uu___2) -> k
let left : 'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set =
  fun f ->
    fun input -> match input with | Node (l, uu___, uu___1, uu___2) -> l
let right : 'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set =
  fun f ->
    fun input -> match input with | Node (uu___, uu___1, uu___2, r) -> r
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x -> fun y -> if x > y then x else y
let rec member : 'a . 'a comparaison -> 'a -> ('a, unit) set -> Prims.bool =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | Leaf -> false
        | Node (l, k, uu___, r) ->
            ((uu___is_EQ (f x k)) || (member f x l)) || (member f x r)
let delta :
  'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set -> Prims.nat =
  fun f ->
    fun l ->
      fun r ->
        if (height f l) > (height f r)
        then (height f l) - (height f r)
        else (height f r) - (height f l)
type ('a, 'f, 'input) is_avl = Obj.t
let make :
  'a .
    'a comparaison ->
      ('a, unit) set -> 'a -> ('a, unit) set -> ('a, unit) set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          Node (l, k, (Prims.int_one + (max (height f l) (height f r))), r)
