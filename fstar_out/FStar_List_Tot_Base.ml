open Prims
let isEmpty : 'a . 'a Prims.list -> Prims.bool =
  fun l -> match l with | [] -> true | uu___ -> false
let hd : 'a . 'a Prims.list -> 'a =
  fun uu___ -> match uu___ with | hd1::uu___1 -> hd1
let tail : 'a . 'a Prims.list -> 'a Prims.list =
  fun uu___ -> match uu___ with | uu___1::tl -> tl
let tl : 'a . 'a Prims.list -> 'a Prims.list = tail
let rec last : 'a . 'a Prims.list -> 'a =
  fun uu___ -> match uu___ with | hd1::[] -> hd1 | uu___1::tl1 -> last tl1
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    match uu___ with | uu___1::[] -> [] | hd1::tl1 -> hd1 :: (init tl1)
let rec length : 'a . 'a Prims.list -> Prims.nat =
  fun uu___ ->
    match uu___ with
    | [] -> Prims.int_zero
    | uu___1::tl1 -> Prims.int_one + (length tl1)
let rec nth :
  'a . 'a Prims.list -> Prims.nat -> 'a FStar_Pervasives_Native.option =
  fun l ->
    fun n ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd1::tl1 ->
          if n = Prims.int_zero
          then FStar_Pervasives_Native.Some hd1
          else nth tl1 (n - Prims.int_one)
let rec index : 'a . 'a Prims.list -> Prims.nat -> 'a =
  fun l ->
    fun i ->
      if i = Prims.int_zero then hd l else index (tl l) (i - Prims.int_one)
let rec count : 'a . 'a -> 'a Prims.list -> Prims.nat =
  fun x ->
    fun uu___ ->
      match uu___ with
      | [] -> Prims.int_zero
      | hd1::tl1 ->
          if x = hd1 then Prims.int_one + (count x tl1) else count x tl1
let rec rev_acc : 'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun l ->
    fun acc ->
      match l with | [] -> acc | hd1::tl1 -> rev_acc tl1 (hd1 :: acc)
let rev : 'a . 'a Prims.list -> 'a Prims.list = fun l -> rev_acc l []
let rec append : 'a . 'a Prims.list -> 'a Prims.list -> 'a Prims.list =
  fun x -> fun y -> match x with | [] -> y | a1::tl1 -> a1 :: (append tl1 y)
let op_At :
  'uuuuu . 'uuuuu Prims.list -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun x -> fun y -> append x y
let snoc : 'a . ('a Prims.list * 'a) -> 'a Prims.list =
  fun uu___ -> match uu___ with | (l, x) -> append l [x]
let rec flatten : 'a . 'a Prims.list Prims.list -> 'a Prims.list =
  fun l -> match l with | [] -> [] | hd1::tl1 -> append hd1 (flatten tl1)
let rec map : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun x -> match x with | [] -> [] | a1::tl1 -> (f a1) :: (map f tl1)
let rec mapi_init :
  'a 'b .
    (Prims.int -> 'a -> 'b) -> 'a Prims.list -> Prims.int -> 'b Prims.list
  =
  fun f ->
    fun l ->
      fun i ->
        match l with
        | [] -> []
        | hd1::tl1 -> (f i hd1) :: (mapi_init f tl1 (i + Prims.int_one))
let mapi : 'a 'b . (Prims.int -> 'a -> 'b) -> 'a Prims.list -> 'b Prims.list
  = fun f -> fun l -> mapi_init f l Prims.int_zero
let rec concatMap :
  'a 'b . ('a -> 'b Prims.list) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | a1::tl1 ->
          let fa = f a1 in let ftl = concatMap f tl1 in append fa ftl
let rec fold_left : 'a 'b . ('a -> 'b -> 'a) -> 'a -> 'b Prims.list -> 'a =
  fun f ->
    fun x ->
      fun l -> match l with | [] -> x | hd1::tl1 -> fold_left f (f x hd1) tl1
let rec fold_right : 'a 'b . ('a -> 'b -> 'b) -> 'a Prims.list -> 'b -> 'b =
  fun f ->
    fun l ->
      fun x ->
        match l with | [] -> x | hd1::tl1 -> f hd1 (fold_right f tl1 x)


let rec fold_left2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> 'a) -> 'a -> 'b Prims.list -> 'c Prims.list -> 'a
  =
  fun f ->
    fun accu ->
      fun l1 ->
        fun l2 ->
          match (l1, l2) with
          | ([], []) -> accu
          | (a1::l11, a2::l21) -> fold_left2 f (f accu a1 a2) l11 l21
type ('a, 'x, 'l) memP = Obj.t
let rec mem : 'a . 'a -> 'a Prims.list -> Prims.bool =
  fun x ->
    fun uu___ ->
      match uu___ with
      | [] -> false
      | hd1::tl1 -> if hd1 = x then true else mem x tl1
let contains : 'uuuuu . unit -> 'uuuuu -> 'uuuuu Prims.list -> Prims.bool =
  fun uu___ -> mem
let rec existsb : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> false
      | hd1::tl1 -> if f hd1 then true else existsb f tl1
let rec find :
  'a .
    ('a -> Prims.bool) -> 'a Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd1::tl1 ->
          if f hd1 then FStar_Pervasives_Native.Some hd1 else find f tl1
let rec filter : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | hd1::tl1 -> if f hd1 then hd1 :: (filter f tl1) else filter f tl1


let rec for_all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | hd1::tl1 -> if f hd1 then for_all f tl1 else false

let rec collect :
  'a 'b . ('a -> 'b Prims.list) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l ->
      match l with | [] -> [] | hd1::tl1 -> append (f hd1) (collect f tl1)
let rec tryFind :
  'a .
    ('a -> Prims.bool) -> 'a Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun p ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd1::tl1 ->
          if p hd1 then FStar_Pervasives_Native.Some hd1 else tryFind p tl1
let rec tryPick :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd1::tl1 ->
          (match f hd1 with
           | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some x
           | FStar_Pervasives_Native.None -> tryPick f tl1)
let rec choose :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd1::tl1 ->
          (match f hd1 with
           | FStar_Pervasives_Native.Some x -> x :: (choose f tl1)
           | FStar_Pervasives_Native.None -> choose f tl1)
let rec partition :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> ([], [])
      | hd1::tl1 ->
          let uu___1 = partition f tl1 in
          (match uu___1 with
           | (l1, l2) ->
               if f hd1 then ((hd1 :: l1), l2) else (l1, (hd1 :: l2)))
let rec subset : 'a . 'a Prims.list -> 'a Prims.list -> Prims.bool =
  fun la ->
    fun lb ->
      match la with | [] -> true | h::tl1 -> (mem h lb) && (subset tl1 lb)
let rec noRepeats : 'a . 'a Prims.list -> Prims.bool =
  fun la ->
    match la with
    | [] -> true
    | h::tl1 -> (Prims.op_Negation (mem h tl1)) && (noRepeats tl1)
type ('a, 'la) no_repeats_p = Obj.t
let rec assoc :
  'a 'b . 'a -> ('a * 'b) Prims.list -> 'b FStar_Pervasives_Native.option =
  fun x ->
    fun uu___ ->
      match uu___ with
      | [] -> FStar_Pervasives_Native.None
      | (x', y)::tl1 ->
          if x = x' then FStar_Pervasives_Native.Some y else assoc x tl1
let rec split :
  'a 'b . ('a * 'b) Prims.list -> ('a Prims.list * 'b Prims.list) =
  fun l ->
    match l with
    | [] -> ([], [])
    | (hd1, hd2)::tl1 ->
        let uu___ = split tl1 in
        (match uu___ with | (tl11, tl2) -> ((hd1 :: tl11), (hd2 :: tl2)))
let unzip :
  'uuuuu 'uuuuu1 .
    ('uuuuu * 'uuuuu1) Prims.list -> ('uuuuu Prims.list * 'uuuuu1 Prims.list)
  = fun l -> split l
let rec unzip3 :
  'a 'b 'c .
    ('a * 'b * 'c) Prims.list ->
      ('a Prims.list * 'b Prims.list * 'c Prims.list)
  =
  fun l ->
    match l with
    | [] -> ([], [], [])
    | (hd1, hd2, hd3)::tl1 ->
        let uu___ = unzip3 tl1 in
        (match uu___ with
         | (tl11, tl2, tl3) -> ((hd1 :: tl11), (hd2 :: tl2), (hd3 :: tl3)))
let rec splitAt :
  'a . Prims.nat -> 'a Prims.list -> ('a Prims.list * 'a Prims.list) =
  fun n ->
    fun l ->
      if n = Prims.int_zero
      then ([], l)
      else
        (match l with
         | [] -> ([], l)
         | x::xs ->
             let uu___1 = splitAt (n - Prims.int_one) xs in
             (match uu___1 with | (l1, l2) -> ((x :: l1), l2)))

let unsnoc : 'a . 'a Prims.list -> ('a Prims.list * 'a) =
  fun l ->
    let uu___ = splitAt ((length l) - Prims.int_one) l in
    match uu___ with | (l1, l2) -> (l1, (hd l2))
let split3 :
  'a . 'a Prims.list -> Prims.nat -> ('a Prims.list * 'a * 'a Prims.list) =
  fun l ->
    fun i ->
      let uu___ = splitAt i l in
      match uu___ with
      | (a1, as1) ->
          let uu___1 = as1 in (match uu___1 with | b::c -> (a1, b, c))

let bool_of_compare : 'a . ('a -> 'a -> Prims.int) -> 'a -> 'a -> Prims.bool
  = fun f -> fun x -> fun y -> (f x y) > Prims.int_zero
let compare_of_bool : 'a . ('a -> 'a -> Prims.bool) -> 'a -> 'a -> Prims.int
  =
  fun rel ->
    fun x ->
      fun y ->
        if rel x y
        then Prims.int_one
        else if x = y then Prims.int_zero else (Prims.of_int (-1))

let rec sortWith :
  'a . ('a -> 'a -> Prims.int) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | pivot::tl1 ->
          let uu___1 = partition (bool_of_compare f pivot) tl1 in
          (match uu___1 with
           | (hi, lo) -> append (sortWith f lo) (pivot :: (sortWith f hi)))
type ('a, 'l1, 'l2) strict_prefix_of = Obj.t
let rec list_unref : 'a 'p . 'a Prims.list -> 'a Prims.list =
  fun l -> match l with | [] -> [] | x::xs -> x :: (list_unref xs)
let rec list_refb : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list
  =
  fun p ->
    fun l -> match l with | hd1::tl1 -> hd1 :: (list_refb p tl1) | [] -> []
let rec list_ref : 'a 'p . 'a Prims.list -> 'a Prims.list =
  fun l -> match l with | hd1::tl1 -> hd1 :: (list_ref tl1) | [] -> []