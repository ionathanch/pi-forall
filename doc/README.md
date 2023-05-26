pi-forall Language
------------------

This language implementation is designed to accompany four lectures at
OPLSS during Summer 2022.
These lecture notes correspond to an increasingly expressive demo
implementation of dependently-typed lambda calculus.
The implementation [README.md](../src/README.md) includes instructions about
how to compile and work with these implementations.

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