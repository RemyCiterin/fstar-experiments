#!/bin/bash 
fstar.exe --record_hints --use_hints --odir fstar_out --codegen OCaml AVL.fst BinTree.fst BDD.fst BDD2.fst  --query_stats #
cd fstar_out 
ocamlbuild BDD.native -package fstarlib,batteries
cd ..