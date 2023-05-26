pi-forall
=========

A demo implementation of a simple dependently-typed language for OPLSS
(used in 2022, 2014 and 2013). Notes for the lectures are included in the
distribution: [oplss.pdf](doc/oplss.pdf).

The goal of this project is to bring up the design issues that occur in the
implementation of the type checkers of languages like Agda, Coq, Epigram, Idris, etc.
Of course, it can't cover everything, but this code is a starting point for discussion.

As its main purpose is didactic, the code itself has been written for
clarity, not for speed. The point of this implementation is an introduction to
practical issues of language design and how specific features interact with
each other.

Installation
------------

Compiling pi-forall requires GHC and stack. Recommended tools (see links for instructions):

1. [ghcup](https://www.haskell.org/ghcup/)

   The ghcup tool is an installer for general purpose Haskell tools, including GHC, Cabal, Stack and the Haskell language server (HLS). You'll want to install the recommended versions of all of these tools.

2. [VSCode](https://code.visualstudio.com/) and [Haskell language extension](https://marketplace.visualstudio.com/items?itemName=haskell.haskell)


Contents
--------

The implementation has the following structure:

```
pi/*.pi            example pi-forall files
src/*.hs           source code
app/Main.hs        entry point
test/Main.hs
README.md (this file)
LICENSE
pi-forall.cabal
stack.yaml

```

To build each version, go to that directory and type:

```sh
stack build
```

and to type check a source file:

```sh
stack exec -- pi-forall <sourcefile>
```


Acknowledgements
----------------

Some of this code was adapted from the 'zombie-trellys' implementation by the
Trellys team. The Trellys team includes Aaron Stump, Tim Sheard, Stephanie
Weirich, Garrin Kimmell, Harley D. Eades III, Peng Fu, Chris Casinghino,
Vilhelm Sjöberg, Nathan Collins, and Ki Yung Ahn.

This material is based upon work supported by the National Science Foundation
under Grant Number 0910786. Any opinions, findings, and conclusions or
recommendations expressed in this material are those of the author(s) and do
not necessarily reflect the views of the National Science Foundation.