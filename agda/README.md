# Mechanization of consistency of subStraTT

This mechanization has been checked with
[Agda](https://wiki.portal.chalmers.se/agda/Main/HomePage) 2.7.0.1,
compiled using GHC 9.6.6,
and using [agda-stdlib](https://github.com/agda/agda-stdlib) 2.1.1.
Instructions for the standard library can be found in their repository,
but Agda can be installed using Cabal and Stack,
which are recommended to be installed using [GHCup](https://www.haskell.org/ghcup/).

```sh
cabal get Agda-2.7.0.1
cd Agda-2.7.0.1
stack --stack-yaml stack-9.6.6.yaml install
```

## Expected output

The top-level file can be checked by `agda consistency.agda`,
with the following expected output when run in the VM.

```
Checking consistency (/root/StraTT/agda/consistency.agda).
 Checking common (/root/StraTT/agda/common.agda).
 Checking accessibility (/root/StraTT/agda/accessibility.agda).
 Checking syntactics (/root/StraTT/agda/syntactics.agda).
 Checking reduction (/root/StraTT/agda/reduction.agda).
 Checking typing (/root/StraTT/agda/typing.agda).
 Checking semantics (/root/StraTT/agda/semantics.agda).
 Checking soundness (/root/StraTT/agda/soundness.agda).
```

## Axioms

The only axiom used is function extensionality,
which is located in the `accext` module of `accessibility.agda`
as private postulates (one for an implicit and one for an explicit domain).
Function extensionality is only used to prove
mere propositionality of the accessibility predicate,
which in turn is only used to prove `accU` in `semantics.agda`.

## Contents

The modules below are in approximate dependency order,
with the corresponding lemmas and theorems from the paper
that they contain in parentheses.
Most of the modules are parametrized over an abstract `Level`
and its strict transitive order,
only to be instantiated at the very end by the naturals.

* `common.agda`: Reëxports all the necessary agda-stdlib modules,
  and defines common definitions.
* `accessibility.agda`: The accessibility predicate and its mere propositionality.
* `syntactics.agda`: Syntax, substitution, contexts, and context membership.
* `reduction.agda`: Parallel reduction, substitution lemmas, confluence, and conversion.
* `typing.agda`: Definitional equality (Lemma 3), context well-formedness, and well-typedness.
* `semantics.agda`: Logical relations stating semantic typing and semantic context formation (Figure 7, Figure 8),
  along with important properties such as cumulativity (Lemma 4), conversion (Lemma 5), and backward preservation (Lemma 6).
* `soundness.agda`: The fundamental theorem of soundness of typing —
  syntactic well-typedness implies semantic well-typedness (Theorem 1).
* `consistency.agda`: Strict order on the naturals, well-foundedness of the naturals
  with respect to its strict order, and logical consistency using the naturals as levels (Corollary 1).

## Statistics

```
github.com/AlDanial/cloc v 1.98  T=0.01 s (654.7 files/s, 88706.0 lines/s)
--------------------------------------------------------------------------------
File                              blank        comment           code
--------------------------------------------------------------------------------
reduction.agda                       46             11            223
syntactics.agda                      42             21            181
semantics.agda                       38             20            178
typing.agda                          14             20            117
soundness.agda                        3              0             78
consistency.agda                     12              2             44
accessibility.agda                    4              0             18
common.agda                           1              0             11
--------------------------------------------------------------------------------
SUM:                                160             74            850
--------------------------------------------------------------------------------
```