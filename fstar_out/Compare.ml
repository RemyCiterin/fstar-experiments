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