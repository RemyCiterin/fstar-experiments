open Prims
type ('a, 'f) set = ('a, unit, unit) BinTree.set
let mem : 'a . 'a Compare.comparaison -> 'a -> ('a, unit) set -> Prims.bool =
  fun f -> fun x -> fun input -> AVL.mem f x input
let member :
  'a . 'a Compare.comparaison -> 'a -> ('a, unit) set -> Prims.bool =
  fun f ->
    fun x ->
      fun input ->
        match AVL.find f x input with
        | FStar_Pervasives_Native.Some (k, uu___) -> k = x
        | FStar_Pervasives_Native.None -> false
let find :
  'a .
    'a Compare.comparaison ->
      'a -> ('a, unit) set -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      fun input ->
        match AVL.find f x input with
        | FStar_Pervasives_Native.Some (y, uu___) ->
            FStar_Pervasives_Native.Some y
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let add :
  'a . 'a Compare.comparaison -> ('a, unit) set -> 'a -> ('a, unit) set =
  fun f -> fun s -> fun x -> AVL.add f (x, ()) s
let remove :
  'a . 'a Compare.comparaison -> ('a, unit) set -> 'a -> ('a, unit) set =
  fun f -> fun s -> fun x -> AVL.remove f x s