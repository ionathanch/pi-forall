# Stratified Type Theory

This repository contains the supplementary material for
Stratified Type Theory (StraTT),
consisting of three parts:

* `coq/`: A Coq development of the syntactic metatheory of StraTT.
  Compilation instructions can be found in `coq/README.md`,
  or run `make coq`.
* `agda/`: An Agda mechanization of the consistency of subStraTT.
* `impl/`: A Haskell implementation of a type checker for StraTT
  augmented with datatypes, based on pi-forall.
  Compilation instructions can be found in `impl/README.md`,
  or run `make impl`.