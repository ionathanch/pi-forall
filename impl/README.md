# Stratified Type Theory

This is an implementation of a Haskell type checker for Stratified Type Theory (StraTT),
extended with datatypes, recursive global functions, and level inference.

## Installation

This project requires Stack and Cabal, and has been tested with GHC 9.6.6.
These can be installed using [GHCup](https://www.haskell.org/ghcup/).
It also uses [Z3](https://github.com/Z3Prover/z3) to solve level constraints,
and has been tested with version 4.13.0.
To compile the type checker, run `stack build`.
To check a file `<file>`, run `stack exec -- stratt <file>`.
If successful, the definitions in that file will be printed out
explicitly annotated with levels and displacements.

## Grammar

The grammar for the implemented language is given below,
with a description for each construct and
its corresponding StraTT syntax from the paper where they differ.
In addition to datatypes, there is also a primitive equality type.
Note that parentheses `()` and brackets `[]` are concrete syntax,
while braces `{}` aren't and are only used for grouping,
in particular for use with ellipses `...` to denote sequences.

```ebnf
x, y, z ::= <name>     (* variable/constant names *)
D ::= <name>           (* datatype names *)
C ::= <name>           (* constructor names *)
M ::= <name>           (* module names *)
i, j, k ::= <natural>  (* levels *)

(* terms *)
a, b, A, B ::= x                   (*             variable or constant with implicit displacement *)
             | x ^ i               (* [xⁱ]        constant with explicit displacement *)
             | Type                (* [⋆]         type universe *)
             | \x. b               (* [λx. b]     function *)
             | b a                 (*             application *)
             | (x : A @ k) -> B    (* [Πx:ᵏA.B]   dependent function type with explicit domain level *)
             | (x : A) -> B        (*                                 and with implicit domain level *)
             | A -> B              (* [A → B]     nondependent function type *)
             | Void                (* [⊥]         empty type *)
             | absurd b            (* [absurd(b)] ex falso quodlibet *)
(* the following are features not found in StraTT *)
             | a = b               (*             equality type *)
             | Refl                (*             reflexivity proof *)
             | subst a by b        (*             substitute in the type of a the equality b *)
             | contra b            (*             eliminate propositional equality of definitionally inequal terms *)
             | (a : A)             (*             explicit type annotation *)
             | let x = a in b      (*             let-bound expressions *)
             | TRUSTME             (*             typed hole *)
             | PRINTME             (*             typed hole printing context, constraints, and goal *)
(* the following are relevant to datatypes *)
             | D a...              (*             fully applied datatype *)
             | C a...              (*             fully applied constructor *)
             | case a of           (*             case expression *)
                 {C x... => b}...

(* signatures *)
Δ ::= x : A      (* [x : A ≔ a] global definition *)
      x = a
    | <datatype> (* see further below *)

(* file structure *)
file ::= module M where
         {import M}...
         Δ...
```

Datatype definitions are of the form:

```
data D E... : Type @ k where
  C of E... @ j
  ...
  C of E... @ j
```

```ebnf
E ::= (x : A @ i)  (* dependent parameter/argument *)
      (x : A)      (* nondependent parameter/dependent argument with implicit level *)
      (A)          (* nondependent parameter/argument *)
      [x = a]      (* assignment of variable to value *)
```

where `k` is a level annotation for datatype D,
`j` is a level annotation for constructor C,
we have the constraint `j <= k`,
and both annotations can be omitted to be inferred.

The syntax for parameters and arguments are a little nonuniform
to accommodate both dependency/nondependency and explicit/implicit levels.
Named parameters with no level annotations indicate nondependent parameters,
while named constructor arguments with no level annotations indicate dependent arguments whose level is inferred.
For instance, below is how `DPair` would be declared
along with its corresponding paper StraTT definition.

```
data DPair (A : Type @ 0) (B : (_ : A @ 0) -> Type) : Type @ 1 where
  MkPair of (x : A @ 0) (B x) @ 1
```

```
data DPair (A :⁰ ⋆) (B : Π _ :⁰ A . ⋆) :¹ ⋆ where
  MkPair :¹ Π x :⁰ A . B x → DPair A B
```

Rather than having indices, parameters can be equated to values.
For instance, the following implements the naturals and the finite sets.
The corresponding paper StraTT definition for the finite set is also given.

```
data Nat : Type @ 0 where
  Zero @ 0
  Succ of (Nat) @ 0

data Fin (n : Nat) : Type @ 1 where
  Zero of (m : Nat @ 0) [n = Succ m] @ 1
  Succ of (m : Nat @ 0) [n = Succ m] (Fin m) @ 1
```

```
data Fin (n : Nat) :¹ Type where
  Zero :¹ Π m :⁰ Nat . Fin (Succ m)
  Succ :¹ Π m :⁰ Nat . Fin m → Fin (Succ m)

```

## Examples

All the example files are found in the `pi/` directory.
The `pi/README.pi` file imports each file with a short description.
The `pi/StraTT.pi` file contains all of the specific examples mentioned in the paper.