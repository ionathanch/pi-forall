pi-forall Language
------------------

A demo implementation of a simple dependently-typed language for OPLSS
(used in 2022, 2014 and 2013). Notes for the lectures are included in the
distribution: [oplss.pdf](oplss.pdf).

The goal of this project is to bring up the design issues that occur in the
implementation of the type checkers of languages like Agda, Coq, Epigram, Idris, etc.
Of course, it can't cover everything, but this code is a starting point for discussion.

As its main purpose is didactic, the code itself has been written for
clarity, not for speed. The point of this implementation is an introduction to
practical issues of language design and how specific features interact with
each other.

This language implementation is designed to accompany four lectures at
OPLSS during Summer 2022.
These lecture notes correspond to an increasingly expressive demo
implementation of dependently-typed lambda calculus.

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

History
-------

This is a revised version of lecture notes originally presented at OPLSS
during 2014 and 2013.

Videos from the 2014 lectures are also available from the
[OPLSS website](https://www.cs.uoregon.edu/research/summerschool/summer14/curriculum.html).
If you want to watch these videos, you should look at the
2014 branch of this repository.

An abridged version of these lectures was also given at the Compose
Conference, January 2015. Notes from this version are also available.

- [compose.md](old/compose.md): Overview of pi-forall implementation


Source files for Lecture Notes
------------------------------

To typeset these notes, you will need to have installed LaTeX and the Ott tool. The easiest way to install Ott is through [opam](https://opam.ocaml.org/).

The Ott tool assists with typesetting mathematical specifications of type systems. All typing rules that appear in the lecture notes are specified within the following source files.

[Ott](https://www.cl.cam.ac.uk/~pes20/ott/top2.html) specifications:
+ [pi.ott](pi.ott) - Core system
+ [bool.ott](bool.ott) - Booleans
+ [sigma.ott](sigma.ott) - Sigma types
+ [tyeq.ott](tyeq.ott) - Propositional equality
+ [epsilon.ott](epsilon.ott) - Irrelevance
+ [data.ott](data.ott) - Data types

LaTeX source files
+ [oplss.mng](oplss.mng) - Main text of the document
+ [lstpi.sty](lstpi.sty) - [Listings](https://ctan.mirrors.hoobly.com/macros/latex/contrib/listings/listings.pdf) specification for  typesetting `pi-forall` source code
+ [ottalt.sty](ottalt.sty) - [Auxiliary style file](https://users.cs.northwestern.edu/~jesse/code/latex/ottalt/ottalt.pdf) for working with Ott produced LaTeX macros
+ [weirich.bib](weirich.bib) - BibTeX data
+ Makefile - how to put everything together

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