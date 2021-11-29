module Compare 

type ordering = 
    | GT
    | LT
    | EQ


let is_GE a = GT? a || EQ? a 
let is_LE a = LT? a || EQ? a


let reflexivity     #a (f: a -> a -> ordering) = forall x. EQ? (f x x)
let symmetry_EQ     #a (f: a -> a -> ordering) = forall x y. EQ? (f x y) <==> EQ? (f y x)
let anti_symetry    #a (f: a -> a -> ordering) = forall x y. LT? (f x y) <==> GT? (f y x)
let transitivity_LT #a (f: a -> a -> ordering) = forall x y z. (LT? (f x y) /\ LT? (f y z)) ==> LT? (f x z)
let transitivity_GT #a (f: a -> a -> ordering) = forall x y z. (GT? (f x y) /\ GT? (f y z)) ==> GT? (f x z)
let transitivity_EQ #a (f: a -> a -> ordering) = forall x y z. (EQ? (f x y) /\ EQ? (f y z)) ==> EQ? (f x z)
let transitivity    #a (f: a -> a -> ordering) = transitivity_EQ f /\ transitivity_GT f /\ transitivity_LT f


let comparaison a = f: (a -> a -> ordering) {reflexivity f /\ transitivity f /\ symmetry_EQ f /\ anti_symetry f}
