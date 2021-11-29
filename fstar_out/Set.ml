open Prims
type ordering = Compare.ordering
type 'a comparaison = 'a Compare.comparaison
type ('a, 'compare) set = ('a, unit) BinTree.set
let mem : 'a . 'a comparaison -> 'a -> ('a, unit) set -> Prims.bool =
  fun f -> fun x -> fun input -> AVL.mem f x input
let add : 'a . 'a comparaison -> 'a -> ('a, unit) set -> ('a, unit) set =
  fun f -> fun x -> fun input -> AVL.add f x input
let remove : 'a . 'a comparaison -> 'a -> ('a, unit) set -> ('a, unit) set =
  fun f -> fun x -> fun input -> AVL.remove f x input