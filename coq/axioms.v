(* This file lists all axioms in the development.
   These are related to the definition of equivalence and are needed
   in the proof of type soundness. *)

Require Export StraTT.StraTT_ott.
Require Export Metalib.Metatheory.

Set Implicit Arguments.

(* Axiom 2 (function type injectivity) in the paper,
   needed for preservation lemma.
   These results require long proofs,
   but the system is extremely similar to existing definitions of βη-equivalence,
   and have been mechanized in the Agda development,
   so there is nothing to be learned from mechanizing them here.
*)

Axiom DEquiv_Arrow_inj1 : forall S A1 B1 A2 B2,
    DEquiv S (a_Arrow A1 B1) (a_Arrow A2 B2) -> DEquiv S A1 A2.
Axiom DEquiv_Arrow_inj2 : forall S A1 B1 A2 B2,
    DEquiv S (a_Arrow A1 B1) (a_Arrow A2 B2) -> DEquiv S B1 B2.
Axiom DEquiv_Pi_inj1 : forall S A1 B1 j1 j2 A2 B2,
    DEquiv S (a_Pi A1 j1 B1) (a_Pi A2 j2 B2) -> DEquiv S A1 A2.
Axiom DEquiv_Pi_inj2 : forall S A1 B1 j1 j2 A2 B2,
    DEquiv S (a_Pi A1 j1 B1) (a_Pi A2 j2 B2) -> j1 = j2.
Axiom DEquiv_Pi_inj3 : forall S A1 B1 j1 j2 A2 B2 a,
    lc_tm a
    -> DEquiv S (a_Pi A1 j1 B1) (a_Pi A2 j2 B2)
    -> DEquiv S (open_tm_wrt_tm B1 a) (open_tm_wrt_tm B2 a).

(* Axiom 3 (consistency of definitional equality) in the paper,
   needed for progress lemma.
*)

Axiom ineq_Arrow_Pi : forall S A1 B1 A2 j B2,
    DEquiv S (a_Arrow A1 A2) (a_Pi B1 j B2) -> False.

Axiom ineq_Arrow_Type :
  forall S (A1 A2 : tm),
  DEquiv S (a_Arrow A1 A2) a_Type -> False.

Axiom ineq_Pi_Type:
  forall S B1 j B2,
  DEquiv S (a_Pi B1 j B2) a_Type -> False.

Axiom ineq_Type_Bottom : forall S,
  DEquiv S a_Type a_Bottom -> False.

Axiom ineq_Arrow_Bottom :
  forall S (A1 A2 : tm),
  DEquiv S (a_Arrow A1 A2) a_Bottom -> False.

Axiom ineq_Pi_Bottom:
  forall S B1 j B2,
  DEquiv S (a_Pi B1 j B2) a_Bottom -> False.


