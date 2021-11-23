open Prims
let rec mem :
  'a . 'a BinTree.comparaison -> 'a -> ('a, unit) BinTree.set -> Prims.bool =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | BinTree.Leaf -> false
        | BinTree.Node (l, k, uu___, r) ->
            (match f x k with
             | BinTree.LT -> mem f x l
             | BinTree.GT -> mem f x r
             | BinTree.EQ -> true)
let balanceLL :
  'a .
    'a BinTree.comparaison ->
      ('a, unit) BinTree.set ->
        'a -> ('a, unit) BinTree.set -> ('a, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          match l with
          | BinTree.Node (ll, lk, ls, lr) ->
              BinTree.make f ll lk (BinTree.make f lr k r)
let balanceRR :
  'a .
    'a BinTree.comparaison ->
      ('a, unit) BinTree.set ->
        'a -> ('a, unit) BinTree.set -> ('a, unit) BinTree.set
  =
  fun f ->
    fun l ->
      fun k ->
        fun r ->
          match r with
          | BinTree.Node (rl, rk, rs, rr) ->
              BinTree.make f (BinTree.make f l k rl) rk rr
let balanceLR :
  'a .
    'a BinTree.comparaison ->
      ('a, unit) BinTree.set ->
        'a -> ('a, unit) BinTree.set -> ('a, unit) BinTree.set
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
  'a .
    'a BinTree.comparaison ->
      ('a, unit) BinTree.set ->
        'a -> ('a, unit) BinTree.set -> ('a, unit) BinTree.set
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
type intSet = (Prims.int, unit) BinTree.set
let rec add :
  'a .
    'a BinTree.comparaison ->
      'a -> ('a, unit) BinTree.set -> ('a, unit) BinTree.set
  =
  fun f ->
    fun x ->
      fun input ->
        match input with
        | BinTree.Leaf -> BinTree.make f BinTree.Leaf x BinTree.Leaf
        | BinTree.Node (l, k, uu___, r) ->
            (match f x k with
             | BinTree.EQ -> BinTree.make f l x r
             | BinTree.LT ->
                 let l' = add f x l in
                 if (BinTree.delta f l' r) >= (Prims.of_int (2))
                 then
                   (if
                      (BinTree.height f (BinTree.left f l')) <
                        (BinTree.height f (BinTree.right f l'))
                    then balanceLR f l' k r
                    else balanceLL f l' k r)
                 else BinTree.make f l' k r
             | BinTree.GT ->
                 let r' = add f x r in
                 if (BinTree.delta f l r') >= (Prims.of_int (2))
                 then
                   (if
                      (BinTree.height f (BinTree.left f r')) >
                        (BinTree.height f (BinTree.right f r'))
                    then balanceRL f l k r'
                    else balanceRR f l k r')
                 else BinTree.make f l k r')




