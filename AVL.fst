module AVL
open Compare
open BinTree 
open FStar.Classical

(* definitions *)

let rec mem #a (#f: comparaison a) (x:a) (input: set f) : bool = 
    match input with 
    | Leaf -> false 
    | Node l k _ r -> match f x k with 
        | LT -> mem x l 
        | GT -> mem x r 
        | EQ -> true 


private let balanceLL #a (#f: comparaison a) (l: set f{Node? l}) (k:a) (r:set f) : 
    out:set f{Node? out /\ Node? (right out) /\ left out == left l}

    = match l with 
    Node ll lk ls lr -> make ll lk (make lr k r)


private let balanceRR #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r}) : 
    out:set f{Node? out /\ Node? (left out) /\ right out == right r}

    = match r with 
    | Node rl rk rs rr -> make (make l k rl) rk rr


private let balanceLR #a (#f: comparaison a) (l: set f{Node? l /\ Node? (right l)}) (k:a) (r:set f) : 
    out:set f{Node? out /\ Node? (left out) /\ Node? (right out)} 
    
    = match l with 
    | Node ll lk _ lr -> match lr with 
        | Node lrl lrk _ lrr -> make (make ll lk lrl) lrk (make lrr k r)


private let balanceRL #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r /\ Node? (left r)}) :
    out:set f{Node? out /\ Node? (left out) /\ Node? (right out)} 
    
     = match r with 
    | Node rl rk _ rr -> match rl with 
        | Node rll rlk _ rlr -> make (make l k rll) rlk (make rlr rk rr)

let all_balanceL #a (#f: comparaison a) (l: set f{Node? l}) (k:a) (r:set f): set f = 
    if height l >= 2 + height r then begin assert(Node? l);
        if height (left l) < height (right l) 
        then balanceLR l k r
        else balanceLL l k r
    end else make l k r

let all_balanceR #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r}): set f = 
    if height r >= height l + 2 then begin assert(Node? r);
        if height (left r) > height (right r) 
        then balanceRL l k r
        else balanceRR l k r
    end else make l k r


let rec add #a (#f: comparaison a) (x:a) (input:set f): 
    Tot (out:set f{Node? out /\ 
        (GT? (f x (key out)) ==> Node? (right out)) /\
        (LT? (f x (key out)) ==> Node? (left  out))
    }) (decreases input)

    = match input with 
    | Leaf -> make Leaf x Leaf 
    | Node l k _ r -> match f x k with 
        | EQ -> make l x r 
        | LT -> 
        begin 
            let l' = add x l in 
            all_balanceL l' k r 
        end 
        | GT -> 
        begin 
            let r' = add x r in 
            all_balanceR l k r'
        end 

let rec find_min #a (#f: comparaison a) (input: set f{Node? input}) : a = 
    match input with 
    | Node Leaf k h r -> k
    | Node l k _ r -> find_min l

let rec find_max #a (#f: comparaison a) (input: set f{Node? input}) : a = 
    match input with
    | Node l k h Leaf -> k
    | Node l k _ r -> find_max r


let rec remove_min #a (#f: comparaison a) (input:set f{Node? input}): Tot (out: set f) (decreases input) = 
    match input with 
    | Node Leaf k _ r -> r 
    | Node l k _ r -> 
    begin 
        let l' = remove_min l in
        if height r >= height l' + 2 then begin
            if height (left r) > height (right r) 
            then balanceRL l' k r
            else balanceRR l' k r
        end else make l' k r
    end 

let rec remove_max #a (#f: comparaison a) (input:set f{Node? input}): Tot (out: set f) (decreases input) = 
    match input with 
    | Node l k _ Leaf -> l
    | Node l k _ r -> 
    begin 
        let r' = remove_max r in
        if height l >= height r' + 2 then begin 
            if height (left l) < height (right l) 
            then balanceLR l k r' 
            else balanceLL l k r'
        end else make l k r'
    end


let rec remove #a (#f: comparaison a) (x:a) (input:set f): Tot (out: set f) (decreases input) = 

    match input with 
    | Leaf -> input
    | Node l k _ r -> match f x k with 
        | LT -> 
        begin 
            let l' = remove x l in
            if Leaf? r then make l' k r else all_balanceR l' k r
        end 
        | GT -> 
        begin
            let r' = remove x r in 
            if Leaf? l then make l k r' else all_balanceL l k r'
        end 
        | EQ -> 
            if Leaf? l then r else 
            if Leaf? r then l else begin

            let k' = find_min r in 
            let r' = remove k' r in
            if Leaf? l then make l k' r' else all_balanceL l k' r'
        end 

(* proof *)

#push-options "--z3rlimit 60"

let rec mem_lemma #a (#f: comparaison a) (x:a) (input:set f) : 
    Lemma 
        (requires is_avl input)
        (ensures (member x input <==> mem x input))
    
    = match input with 
    | Node l k _ r -> begin 
        match f x k with 
        | LT -> begin 
            assert (forall y. member y r ==> LT? (f x y));
            mem_lemma x l
        end 
        | GT -> begin 
            assert (forall y. member y l ==> GT? (f x y));
            mem_lemma x r
        end 
        | EQ -> ()
    end 
    | Leaf -> ()

let rec find_min_lemma #a (#f: comparaison a) (input: set f{Node? input}) : 
    Lemma 
        (requires is_avl input)
        (ensures (
            member (find_min input) input  /\
            (forall x. member x input ==> (GT? (f x (find_min input)) \/ EQ? (f x (find_min input))))
        ))
     = match input with 
    | Node Leaf k h r -> ()
    | Node l k _ r -> find_min_lemma l

let rec find_max_lemma #a (#f: comparaison a) (input: set f{Node? input}) : 
    Lemma 
        (requires is_avl input)
        (ensures (
            member (find_max input) input  /\
            (forall x. member x input ==> (LT? (f x (find_max input)) \/ EQ? (f x (find_max input))))
        ))
     = match input with 
    | Node l k h Leaf -> ()
    | Node l k _ r -> find_max_lemma r


private let balanceLL_lemma #a (#f: comparaison a) (l: set f{Node? l}) (k:a) (r:set f) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            height (left l) > height (right l) /\
            height l = height r + 2 
        )

        (ensures (
            let out = balanceLL l k r in 
            is_avl out /\ height out == 1+max (height l-1) (1+height r) /\ 
            height (left out) = height l - 1 /\ height (right out) = 1+height r /\
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k)))
        ))
    = match l with 
    | Node ll lk ls lr -> make_lemma lr k r; make_lemma ll lk (make lr k r)

private let balanceLL_lemma2 #a (#f: comparaison a) (l: set f{Node? l}) (k:a) (r:set f) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            height (left l) = height (right l) /\
            height l = height r + 2 
        )

        (ensures (
            let out = balanceLL l k r in
            is_avl out /\ height out == 1+ height l /\ 
            height (left out) = height l - 1 /\ height (right out) = height l/\
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k)))
        ))
    = match l with 
    | Node ll lk ls lr -> make_lemma lr k r; make_lemma ll lk (make lr k r)

private let balanceRR_lemma #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r}) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            height (right r) > height (left r) /\
            height r = height l + 2 
        )

        (ensures (
            let out = balanceRR l k r in 
            is_avl out /\ height out == 1+max (height r-1) (1+height l) /\ 
            height (left out) = 1+height l /\ height (right out) = height r - 1 /\
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k)))
        ))
    = match r with 
    | Node rl rk rs rr -> make_lemma l k rl; make_lemma (make l k rl) rk rr

private let balanceRR_lemma2 #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r}) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            height (right r) = height (left r) /\
            height r = height l + 2 
        )

        (ensures (
            let out = balanceRR l k r in 
            is_avl out /\ height out == 1 + height r /\ 
            height (left out) = height r /\ height (right out) = height r - 1 /\
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k)))
        ))
    = match r with 
    | Node rl rk rs rr -> make_lemma l k rl; make_lemma (make l k rl) rk rr

private let balanceLR_lemma #a (#f: comparaison a) (l: set f{Node? l /\ Node? (right l)}) (k:a) (r:set f) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            height (left l) < height (right l) /\
            height l = height r + 2 
        )

        (ensures (
            let out = balanceLR l k r in
            is_avl out /\ height out == 1+max (height l-1) (1+height r) /\ 
            height (left out) = height l - 1 /\ height (right out) = height r + 1 /\
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k)))
        ))
    
    = match l with 
    | Node ll lk _ lr -> match lr with 
        | Node lrl lrk _ lrr -> 
            make_lemma ll lk lrl; make_lemma lrr k r; 
            make_lemma (make ll lk lrl) lrk (make lrr k r)

private let balanceRL_lemma #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r /\ Node? (left r)}) :
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\ 
            (forall x. member x r ==> GT? (f x k)) /\ 
            height (right r) < height (left r) /\
            height r = height l + 2 
        )

        (ensures (
            let out = balanceRL l k r in 
            is_avl out /\ height out == 1+max (height r-1) (1+height l) /\ 
            height (left out) = height l + 1 /\ height (right out) = height r - 1 /\
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k)))
        ))
    
     = match r with 
    | Node rl rk rs rr -> match rl with 
        | Node rll rlk rls rlr -> 
            make_lemma l k rll; make_lemma rlr rk rr; 
            make_lemma (make l k rll) rlk (make rlr rk rr)

let all_balanceL_lemma #a (#f: comparaison a) (l: set f{Node? l}) (k:a) (r:set f): 
    Lemma
        (requires
            is_avl l /\ is_avl r /\ 
            (forall x. member x l ==> LT? (f x k)) /\
            (forall x. member x r ==> GT? (f x k)) /\
            height l >= height r - 1 /\ height l <= height r + 2
        )
        (ensures (
            let out = all_balanceL l k r in is_avl out /\ 
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k))) /\ 
            
            (height l = height r + 2 ==> (
                height out <= 1 + height l /\ height out >= height l
            )) /\

            (height l < height r + 2 ==> (
                height out = 1 + max (height r) (height l)
            ))
        )) = 

    if delta l r >= 2 then begin
        if height (left l) < height (right l) 
        then balanceLR_lemma l k r
        else begin 
            if height (left l) = height (right l)
            then balanceLL_lemma2 l k r 
            else balanceLL_lemma  l k r
    end end else make_lemma l k r
    
let all_balanceR_lemma #a (#f: comparaison a) (l: set f) (k:a) (r:set f{Node? r}) : 
    Lemma 
        (requires 
            is_avl l /\ is_avl r /\
            (forall x. member x l ==> LT? (f x k)) /\
            (forall x. member x r ==> GT? (f x k)) /\
            height r >= height l - 1 /\ height r <= 2 + height l
        )
        (ensures (
            let out = all_balanceR l k r in is_avl out /\ 
            (forall x. member x out <==> (member x l \/ member x r \/ EQ? (f x k))) /\

            (height r = height l + 2 ==> (
                height out <= 1 + height r /\ height out >= height r
            )) /\

            (height r < height l + 2 ==> (
                height out = 1 + max (height l) (height r)
            ))

        )) = 

    if delta l r >= 2 then begin
        if height (left r) > height (right r)
        then balanceRL_lemma l k r
        else begin
            if height (left r) = height (right r)
            then balanceRR_lemma2 l k r
            else balanceRR_lemma  l k r
    end end else make_lemma l k r

let rec add_lemma #a (#f: comparaison a) (x:a) (input:set f): 
    Lemma 
        (requires is_avl input)
        (ensures (
            let out = add x input in 
            is_avl out /\ height out >= height input /\ height out <= height input + 1 /\
            //(height out > height input ==> height (left out) <> height (right out) || height out <= 1) /\ 
            (forall y. member y out <==> (member y input \/ EQ? (f x y)))
        ))
    
    = match input with 
    | Leaf -> () 
    | Node l k _ r -> match f x k with 
        | EQ -> make_lemma l x r
        | LT -> 
        begin 
            add_lemma x l; 
            let l' = add x l in 
            all_balanceL_lemma l' k r
        end 
        | GT -> 
        begin 
            add_lemma x r; 
            let r' = add x r in 
            all_balanceR_lemma l k r'
        end 

let rec remove_min_lemma #a (#f: comparaison a) (input:set f{Node? input}): 
    Lemma 
        (requires is_avl input) 

        (ensures (
            let out = remove_min input in 
            is_avl out /\ height out <= height input /\ 
            height out >= height input - 1 /\ 

            (forall y. member y out <==> (
                member y input /\ ~(EQ? (f (find_min input) y))
            ))
        ))
        
        (decreases input)
    
    = match input with 
    | Node Leaf k _ r -> assert (EQ? (f (find_min input) k))
    | Node l k _ r -> 
    begin

        let l' = remove_min l in


        find_min_lemma l; 
        lemma_EQ l; lemma_EQ l'; 
        assert (find_min l == find_min input);
        assert (forall x. member x r ==> GT? (f x (find_min l)));
        remove_min_lemma l; 

        if height r >= height l' + 2 then begin
                if height (left r) > height (right r) 
                then balanceRL_lemma l' k r
                else begin 
                    if height (left r) = height (right r)
                    then balanceRR_lemma2 l' k r
                    else balanceRR_lemma  l' k r   
                end
            end else make_lemma l' k r
    end

let rec remove_max_lemma #a (#f: comparaison a) (input:set f{Node? input}): 
    Lemma 
        (requires is_avl input) 

        (ensures (
            let out = remove_max input in 
            is_avl out /\ height out <= height input /\ 
            height out >= height input - 1 /\ 

            (forall y. member y out <==> (
                member y input /\ ~(EQ? (f (find_max input) y))
            ))
        ))
        
        (decreases input)
    
    = match input with 
    | Node l k _ Leaf -> assert (EQ? (f (find_max input) k))
    | Node l k _ r -> 
    begin

        let r' = remove_max r in


        find_max_lemma r; 
        lemma_EQ r; lemma_EQ r'; 
        assert (find_max r == find_max input);
        assert (forall x. member x l ==> LT? (f x (find_max r)));
        remove_max_lemma r;

        if height l >= height r' + 2 then begin
                if height (left l) < height (right l) 
                then balanceLR_lemma l k r'
                else begin 
                    if height (left l) = height (right l)
                    then balanceLL_lemma2 l k r'
                    else balanceLL_lemma  l k r'   
                end
            end else make_lemma l k r'
    end

let rec remove_lemma #a (#f: comparaison a) (x:a) (input:set f): 
    Lemma 
        (requires is_avl input) 

        (ensures (
            let out = remove x input in 
            is_avl out /\ height out <= height input /\ 
            height out >= height input - 1 /\ 

            (forall y. member y out <==> (
                member y input /\ ~(EQ? (f x y))
            ))
        ))
        
        (decreases input)


    = match input with 
    | Leaf -> ()
    | Node l k _ r -> match f x k with 
        | LT -> 
        begin 
            remove_lemma x l; 
            let l' = remove x l in
            if Leaf? r then make_lemma l' k r else all_balanceR_lemma l' k r
        end 
        | GT -> 
        begin
            remove_lemma x r; 
            let r' = remove x r in 
            if Leaf? l then make_lemma l k r' else all_balanceL_lemma l k r'
        end 
        | EQ -> 
            if Leaf? l then () else 
            if Leaf? r then () else begin
            
            find_min_lemma r; 
            let k' = find_min r in 
            let r' = remove k' r in
            remove_lemma k' r;

            lemma_EQ r; lemma_EQ r';
            
            if Leaf? l then make_lemma l k' r' else all_balanceL_lemma l k' r' 
            
        end


#pop-options

