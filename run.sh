#!/bin/bash 
fstar.exe --record_hints --use_hints --odir fstar_out --codegen OCaml BDD2.fst --query_stats #AVL.fst BinTree.fst BDD.fst Map.fst Set.fst
cd fstar_out 
ocamlbuild BDD.native -package fstarlib,batteries
cd ..