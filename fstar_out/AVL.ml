open Prims
let rec mem :
  'a 'b .
    'a Compare.comparaison -> 'a -> ('a, 'b, unit) BinTree.set -> Prims.bool
  =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | BinTree.Leaf -> false
        | BinTree.Node (l, k, uu___, r) ->
            (match f x (FStar_Pervasives_Native.fst k) with
             | Compare.LT -> mem f x l
             | Compare.GT -> mem f x r
             | Compare.EQ -> true)
let balanceLL :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set ->
        ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          match l with
          | BinTree.Node (ll, lk, ls, lr) ->
              BinTree.make f ll lk (BinTree.make f lr k r)
let balanceRR :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set ->
        ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          match r with
          | BinTree.Node (rl, rk, rs, rr) ->
              BinTree.make f (BinTree.make f l k rl) rk rr
let balanceLR :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set ->
        ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          match l with
          | BinTree.Node (ll, lk, uu___, lr) ->
              (match lr with
               | BinTree.Node (lrl, lrk, uu___1, lrr) ->
                   BinTree.make f (BinTree.make f ll lk lrl) lrk
                     (BinTree.make f lrr k r))
let balanceRL :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set ->
        ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          match r with
          | BinTree.Node (rl, rk, uu___, rr) ->
              (match rl with
               | BinTree.Node (rll, rlk, uu___1, rlr) ->
                   BinTree.make f (BinTree.make f l k rll) rlk
                     (BinTree.make f rlr rk rr))
let all_balanceL :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set ->
        ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          if
            (BinTree.height f l) >=
              ((Prims.of_int (2)) + (BinTree.height f r))
          then
            (if
               (BinTree.height f (BinTree.left f l)) <
                 (BinTree.height f (BinTree.right f l))
             then balanceLR f l k r
             else balanceLL f l k r)
          else BinTree.make f l k r
let all_balanceR :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set ->
        ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          if
            (BinTree.height f r) >=
              ((BinTree.height f l) + (Prims.of_int (2)))
          then
            (if
               (BinTree.height f (BinTree.left f r)) >
                 (BinTree.height f (BinTree.right f r))
             then balanceRL f l k r
             else balanceRR f l k r)
          else BinTree.make f l k r
let rec add :
  'a 'b .
    'a Compare.comparaison ->
      ('a * 'b) -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | BinTree.Leaf -> BinTree.make f BinTree.Leaf x BinTree.Leaf
        | BinTree.Node (l, k, uu___, r) ->
            (match BinTree.cmp f x k with
             | Compare.EQ -> BinTree.make f l x r
             | Compare.LT -> let l' = add f x l in all_balanceL f l' k r
             | Compare.GT -> let r' = add f x r in all_balanceR f l k r')
let rec find_min :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) BinTree.set -> ('a * 'b) =
  fun f ->
    fun input ->
      match input with
      | BinTree.Node (BinTree.Leaf, k, h, r) -> k
      | BinTree.Node (l, k, uu___, r) -> find_min f l
let rec find_max :
  'a 'b . 'a Compare.comparaison -> ('a, 'b, unit) BinTree.set -> ('a * 'b) =
  fun f ->
    fun input ->
      match input with
      | BinTree.Node (l, k, h, BinTree.Leaf) -> k
      | BinTree.Node (l, k, uu___, r) -> find_max f r
let rec remove_min :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun input ->
      match input with
      | BinTree.Node (BinTree.Leaf, k, uu___, r) -> r
      | BinTree.Node (l, k, uu___, r) ->
          let l' = remove_min f l in
          if
            (BinTree.height f r) >=
              ((BinTree.height f l') + (Prims.of_int (2)))
          then
            (if
               (BinTree.height f (BinTree.left f r)) >
                 (BinTree.height f (BinTree.right f r))
             then balanceRL f l' k r
             else balanceRR f l' k r)
          else BinTree.make f l' k r
let rec remove_max :
  'a 'b .
    'a Compare.comparaison ->
      ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun input ->
      match input with
      | BinTree.Node (l, k, uu___, BinTree.Leaf) -> l
      | BinTree.Node (l, k, uu___, r) ->
          let r' = remove_max f r in
          if
            (BinTree.height f l) >=
              ((BinTree.height f r') + (Prims.of_int (2)))
          then
            (if
               (BinTree.height f (BinTree.left f l)) <
                 (BinTree.height f (BinTree.right f l))
             then balanceLR f l k r'
             else balanceLL f l k r')
          else BinTree.make f l k r'
let rec remove :
  'a 'b .
    'a Compare.comparaison ->
      'a -> ('a, 'b, unit) BinTree.set -> ('a, 'b, unit) BinTree.set
  =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | BinTree.Leaf -> input
        | BinTree.Node (l, k, uu___, r) ->
            (match f x (FStar_Pervasives_Native.fst k) with
             | Compare.LT ->
                 let l' = remove f x l in
                 if BinTree.uu___is_Leaf f r
                 then BinTree.make f l' k r
                 else all_balanceR f l' k r
             | Compare.GT ->
                 let r' = remove f x r in
                 if BinTree.uu___is_Leaf f l
                 then BinTree.make f l k r'
                 else all_balanceL f l k r'
             | Compare.EQ ->
                 if BinTree.uu___is_Leaf f l
                 then r
                 else
                   if BinTree.uu___is_Leaf f r
                   then l
                   else
                     (let k' = find_min f r in
                      let r' = remove f (FStar_Pervasives_Native.fst k') r in
                      if BinTree.uu___is_Leaf f l
                      then BinTree.make f l k' r'
                      else all_balanceL f l k' r'))













