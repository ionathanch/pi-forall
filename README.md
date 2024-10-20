# Stratified Type Theory

[This repository](https://github.com/plclub/StraTT)
contains the supplementary material for
Stratified Type Theory (StraTT), described in the paper:

> Chan, Jonathan and Weirich, Stephanie:
  Stratified Type Theory.
  In: Programming Languages and Systems:
  34th European Symposium on Programming, ESOP 2024,
  Held as Part of the International Joint Conferences on Theory and Practice of Software,
  ETAPS 2025, Hamilton, Canada, May 3–8, 2025, Proceedings.
  [https://doi.org/10.1007/978-3-031-XXXXX-X](https://doi.org/10.1007/978-3-031-XXXXX-X).

The material consists of three parts:

* `coq/`: A Coq development of the syntactic metatheory of StraTT.
* `agda/`: An Agda mechanization of the consistency of subStraTT.
* `impl/`: A Haskell implementation of a type checker for StraTT augmented with datatypes,
  based on [pi-forall](https://github.com/sweirich/pi-forall).

They have also been packaged in a paper artifact at [TODO].
Detailed descriptions of their contents and of local build instructions
are found in the `README.md`s of their respective directories.
Instructions for running the artifact is found in `INSTALL.md`,
and its requirements are found in `REQUIREMENTS.md`.