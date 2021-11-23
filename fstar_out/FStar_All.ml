open Prims
type all_pre = unit
type ('a, 'pre) all_post' = unit
type 'a all_post = unit
type 'a all_wp = unit
type ('a, 'wp, 'p, 'uuuuu) lift_state_all = 'wp
type ('a, 'wp, 'p, 'h) lift_exn_all = 'wp
let pipe_right : 'a 'b . 'a -> ('a -> 'b) -> 'b = fun x -> fun f -> f x
let pipe_left : 'a 'b . ('a -> 'b) -> 'a -> 'b = fun f -> fun x -> f x
let exit : 'a . Prims.int -> 'a =
  fun uu___ -> failwith "Not yet implemented:exit"
let try_with : 'a . (unit -> 'a) -> (Prims.exn -> 'a) -> 'a =
  fun uu___ -> fun uu___1 -> failwith "Not yet implemented:try_with"
exception Failure of Prims.string 
let (uu___is_Failure : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Failure uu___ -> true | uu___ -> false
let (__proj__Failure__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | Failure uu___ -> uu___
let failwith : 'a . Prims.string -> 'a =
  fun uu___ -> failwith "Not yet implemented:failwith"