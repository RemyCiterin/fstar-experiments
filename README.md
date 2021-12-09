# fstar-experiments
several experiments on F * for the generation of (almost) automatic proofs

## todo : 
1. AVL tree (done)
2. Set and Map module (done)
3. Binary Decision Diagram (typed in this case for more efficient memoization) : apply + restrict + simplify + the eval_node equivalence :

        (
            MapAVL.member b1.node b1 table.map /\
            MapAVL.member b2.node b2 table.map
        )
        ==>
        (
            (forall f. eval_node f b1 == eval_node f b2) <==> b1 == b2  
        )
4. eventualy a SAT solver