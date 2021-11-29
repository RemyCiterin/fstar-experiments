#!/bin/bash 
fstar.exe --record_hints --use_hints --odir fstar_out --codegen OCaml Set.fst Compare.fst --query_stats #Set.fst AVL.fst BinTree.fst BDD.fst BDD2.fst Set.fst
cd fstar_out 
ocamlbuild BDD.native -package fstarlib,batteries
cd ..