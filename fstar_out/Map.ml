open Prims
type ('a, 'b, 'f) map = ('a, 'b, unit) BinTree.set
let mem :
  'a 'b . 'a Compare.comparaison -> 'a -> ('a, 'b, unit) map -> Prims.bool =
  fun f -> fun x -> fun input -> AVL.mem f x input
let member_key :
  'a 'b . 'a Compare.comparaison -> 'a -> ('a, 'b, unit) map -> Prims.bool =
  fun f ->
    fun x ->
      fun input ->
        match AVL.find f x input with
        | FStar_Pervasives_Native.Some (k, uu___) -> k = x
        | FStar_Pervasives_Native.None -> false
let member :
  'a 'b .
    'a Compare.comparaison -> 'a -> 'b -> ('a, 'b, unit) map -> Prims.bool
  =
  fun f ->
    fun x ->
      fun y ->
        fun input ->
          match AVL.find f x input with
          | FStar_Pervasives_Native.Some (k, v) -> (k, v) = (x, y)
          | FStar_Pervasives_Native.None -> false
let find :
  'a 'b .
    'a Compare.comparaison ->
      'a -> ('a, 'b, unit) map -> ('a * 'b) FStar_Pervasives_Native.option
  = fun f -> fun x -> fun input -> AVL.find f x input
let add :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) map -> 'a -> 'b -> ('a, 'b, unit) map
  = fun f -> fun s -> fun x -> fun y -> AVL.add f (x, y) s
let remove :
  'a 'b .
    'a Compare.comparaison -> ('a, 'b, unit) map -> 'a -> ('a, 'b, unit) map
  = fun f -> fun s -> fun x -> AVL.remove f x s