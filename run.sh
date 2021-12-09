#!/bin/bash 

# AVL.fst BinTree.fst BDD.fst MapAVL.fst SetAVL.fst Compare.fst
fstar.exe --record_hints --use_hints --odir fstar_out --codegen OCaml BDD2.fst # --query_stats 
cd fstar_out 
ocamlbuild BDD2.native -package fstarlib,batteries
cd ..