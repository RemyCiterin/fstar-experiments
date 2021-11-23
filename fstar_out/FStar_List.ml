open Prims
let hd : 'a . 'a Prims.list -> 'a =
  fun uu___ ->
    match uu___ with
    | hd1::tl -> hd1
    | uu___1 -> failwith "head of empty list"
let tail : 'a . 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    match uu___ with
    | hd1::tl -> tl
    | uu___1 -> failwith "tail of empty list"
let tl : 'a . 'a Prims.list -> 'a Prims.list = fun l -> tail l
let rec last : 'a . 'a Prims.list -> 'a =
  fun uu___ ->
    match uu___ with
    | hd1::[] -> hd1
    | uu___1::tl1 -> last tl1
    | uu___1 -> failwith "last of empty list"
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun uu___ ->
    match uu___ with
    | uu___1::[] -> []
    | hd1::tl1 -> let uu___1 = init tl1 in hd1 :: uu___1
    | uu___1 -> failwith "init of empty list"
let rec nth : 'a . 'a Prims.list -> Prims.int -> 'a =
  fun l ->
    fun n ->
      if n < Prims.int_zero
      then failwith "nth takes a non-negative integer as input"
      else
        if n = Prims.int_zero
        then
          (match l with
           | [] -> failwith "not enough elements"
           | hd1::uu___1 -> hd1)
        else
          (match l with
           | [] -> failwith "not enough elements"
           | uu___2::tl1 -> nth tl1 (n - Prims.int_one))
let rec iter : 'a . ('a -> unit) -> 'a Prims.list -> unit =
  fun f -> fun x -> match x with | [] -> () | a1::tl1 -> (f a1; iter f tl1)
let rec iteri_aux :
  'a . Prims.int -> (Prims.int -> 'a -> unit) -> 'a Prims.list -> unit =
  fun i ->
    fun f ->
      fun x ->
        match x with
        | [] -> ()
        | a1::tl1 -> (f i a1; iteri_aux (i + Prims.int_one) f tl1)
let iteri : 'a . (Prims.int -> 'a -> unit) -> 'a Prims.list -> unit =
  fun f -> fun x -> iteri_aux Prims.int_zero f x
let rec map : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun x ->
      match x with
      | [] -> []
      | a1::tl1 ->
          let uu___ = f a1 in let uu___1 = map f tl1 in uu___ :: uu___1
let mapT : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  FStar_List_Tot_Base.map
let rec mapi_init :
  'a 'b .
    (Prims.int -> 'a -> 'b) -> 'a Prims.list -> Prims.int -> 'b Prims.list
  =
  fun f ->
    fun l ->
      fun i ->
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu___ = f i hd1 in
            let uu___1 = mapi_init f tl1 (i + Prims.int_one) in uu___ ::
              uu___1
let mapi : 'a 'b . (Prims.int -> 'a -> 'b) -> 'a Prims.list -> 'b Prims.list
  = fun f -> fun l -> mapi_init f l Prims.int_zero
let rec concatMap :
  'a 'b . ('a -> 'b Prims.list) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | a1::tl1 ->
          let fa = f a1 in
          let ftl = concatMap f tl1 in FStar_List_Tot_Base.op_At fa ftl
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> 'c) -> 'a Prims.list -> 'b Prims.list -> 'c Prims.list
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> []
        | (hd1::tl1, hd2::tl2) ->
            let uu___ = f hd1 hd2 in
            let uu___1 = map2 f tl1 tl2 in uu___ :: uu___1
        | (uu___, uu___1) -> failwith "The lists do not have the same length"
let rec map3 :
  'a 'b 'c 'd .
    ('a -> 'b -> 'c -> 'd) ->
      'a Prims.list -> 'b Prims.list -> 'c Prims.list -> 'd Prims.list
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        fun l3 ->
          match (l1, l2, l3) with
          | ([], [], []) -> []
          | (hd1::tl1, hd2::tl2, hd3::tl3) ->
              let uu___ = f hd1 hd2 hd3 in
              let uu___1 = map3 f tl1 tl2 tl3 in uu___ :: uu___1
          | (uu___, uu___1, uu___2) ->
              failwith "The lists do not have the same length"
let rec fold_left : 'a 'b . ('a -> 'b -> 'a) -> 'a -> 'b Prims.list -> 'a =
  fun f ->
    fun x ->
      fun y ->
        match y with
        | [] -> x
        | hd1::tl1 -> let uu___ = f x hd1 in fold_left f uu___ tl1
let rec fold_left2 :
  'a 'b 's .
    ('s -> 'a -> 'b -> 's) -> 's -> 'a Prims.list -> 'b Prims.list -> 's
  =
  fun f ->
    fun a1 ->
      fun l1 ->
        fun l2 ->
          match (l1, l2) with
          | ([], []) -> a1
          | (hd1::tl1, hd2::tl2) ->
              let uu___ = f a1 hd1 hd2 in fold_left2 f uu___ tl1 tl2
          | (uu___, uu___1) ->
              failwith "The lists do not have the same length"
let rec fold_right : 'a 'b . ('a -> 'b -> 'b) -> 'a Prims.list -> 'b -> 'b =
  fun f ->
    fun l ->
      fun x ->
        match l with
        | [] -> x
        | hd1::tl1 -> let uu___ = fold_right f tl1 x in f hd1 uu___
let rec filter : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | hd1::tl1 ->
          let uu___1 = f hd1 in
          if uu___1
          then let uu___2 = filter f tl1 in hd1 :: uu___2
          else filter f tl1
let rec for_all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f ->
    fun l ->
      match l with
      | [] -> true
      | hd1::tl1 ->
          let uu___ = f hd1 in if uu___ then for_all f tl1 else false
let rec forall2 :
  'a 'b .
    ('a -> 'b -> Prims.bool) -> 'a Prims.list -> 'b Prims.list -> Prims.bool
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> true
        | (hd1::tl1, hd2::tl2) ->
            let uu___ = f hd1 hd2 in
            if uu___ then forall2 f tl1 tl2 else false
        | (uu___, uu___1) -> failwith "The lists do not have the same length"
let rec collect :
  'a 'b . ('a -> 'b Prims.list) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l ->
      match l with
      | [] -> []
      | hd1::tl1 ->
          let uu___ = f hd1 in
          let uu___1 = collect f tl1 in
          FStar_List_Tot_Base.append uu___ uu___1
let rec tryFind :
  'a .
    ('a -> Prims.bool) -> 'a Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun p ->
    fun l ->
      match l with
      | [] -> FStar_Pervasives_Native.None
      | hd1::tl1 ->
          let uu___ = p hd1 in
          if uu___ then FStar_Pervasives_Native.Some hd1 else tryFind p tl1
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
          let uu___ = f hd1 in
          (match uu___ with
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
          let uu___ = f hd1 in
          (match uu___ with
           | FStar_Pervasives_Native.Some x ->
               let uu___1 = choose f tl1 in x :: uu___1
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
               let uu___2 = f hd1 in
               if uu___2 then ((hd1 :: l1), l2) else (l1, (hd1 :: l2)))
let rec zip : 'a 'b . 'a Prims.list -> 'b Prims.list -> ('a * 'b) Prims.list
  =
  fun l1 ->
    fun l2 ->
      match (l1, l2) with
      | ([], []) -> []
      | (hd1::tl1, hd2::tl2) ->
          let uu___ = zip tl1 tl2 in (hd1, hd2) :: uu___
      | (uu___, uu___1) -> failwith "The lists do not have the same length"
let rec sortWith :
  'a . ('a -> 'a -> Prims.int) -> 'a Prims.list -> 'a Prims.list =
  fun f ->
    fun uu___ ->
      match uu___ with
      | [] -> []
      | pivot::tl1 ->
          let uu___1 =
            partition
              (fun x -> let uu___2 = f pivot x in uu___2 > Prims.int_zero)
              tl1 in
          (match uu___1 with
           | (hi, lo) ->
               let uu___2 = sortWith f lo in
               let uu___3 = let uu___4 = sortWith f hi in pivot :: uu___4 in
               FStar_List_Tot_Base.op_At uu___2 uu___3)
let rec splitAt :
  'a . Prims.nat -> 'a Prims.list -> ('a Prims.list * 'a Prims.list) =
  fun n ->
    fun l ->
      if n = Prims.int_zero
      then ([], l)
      else
        (match l with
         | [] -> failwith "splitAt index is more that list length"
         | hd1::tl1 ->
             let uu___1 = splitAt (n - Prims.int_one) tl1 in
             (match uu___1 with | (l1, l2) -> ((hd1 :: l1), l2)))
let filter_map :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list
  =
  fun f ->
    fun l ->
      let rec filter_map_acc acc l1 =
        match l1 with
        | [] -> FStar_List_Tot_Base.rev acc
        | hd1::tl1 ->
            let uu___ = f hd1 in
            (match uu___ with
             | FStar_Pervasives_Native.Some hd2 ->
                 filter_map_acc (hd2 :: acc) tl1
             | FStar_Pervasives_Native.None -> filter_map_acc acc tl1) in
      filter_map_acc [] l
let index : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.int =
  fun f ->
    fun l ->
      let rec index1 l1 i =
        match l1 with
        | [] -> failwith "List.index: not found"
        | hd1::tl1 ->
            let uu___ = f hd1 in
            if uu___ then i else index1 tl1 (i + Prims.int_one) in
      index1 l Prims.int_zero