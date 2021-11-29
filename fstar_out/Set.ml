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
let find_min :
  'a . 'a comparaison -> ('a, unit) set -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun input ->
      match input with
      | BinTree.Leaf -> FStar_Pervasives_Native.None
      | BinTree.Node (l, k, uu___, r) ->
          FStar_Pervasives_Native.Some (AVL.find_min f input)
let find_max :
  'a . 'a comparaison -> ('a, unit) set -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun input ->
      match input with
      | BinTree.Leaf -> FStar_Pervasives_Native.None
      | BinTree.Node (l, k, uu___, r) ->
          FStar_Pervasives_Native.Some (AVL.find_max f input)
let remove_min : 'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set =
  fun f ->
    fun input ->
      match input with
      | BinTree.Leaf -> BinTree.Leaf
      | BinTree.Node (l, k, uu___, r) -> AVL.remove_min f input
let remove_max : 'a . 'a comparaison -> ('a, unit) set -> ('a, unit) set =
  fun f ->
    fun input ->
      match input with
      | BinTree.Leaf -> BinTree.Leaf
      | BinTree.Node (l, k, uu___, r) -> AVL.remove_max f input