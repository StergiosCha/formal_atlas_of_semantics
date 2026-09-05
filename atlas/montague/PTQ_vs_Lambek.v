(* ========================================================================== *)
(*  PTQ_vs_Lambek.v — lineage edge: Montague 1973 <- Lambek/categorial        *)
(*  FORMAL-ATLAS / atlas/montague                                             *)
(* ========================================================================== *)
(*
   The claim graded here (edges/ptq__lambek.json): the Curry-Howard reading
   of Lambek-calculus derivations (atlas/type_logical/Lambek.v, Part 6, after
   Moot & Retore 2012 ch. 3) COMPUTES the PTQ meanings of the shared fragment
   — same generalized quantifiers, same first-order truth conditions, and
   type raising is literally Montague's star.  The divergence is in the
   engine, not the output: PTQ derives meanings by analysis trees +
   quantifying-in, the categorial route by sequent derivations + the
   homomorphism; on the shared fragment the outputs coincide definitionally
   (all theorems below close by rewrite + reflexivity).

   SOURCES: M73 (via atlas/montague/PTQ.v); Moot & Retore 2012 ch. 3 and
   Lambek 1958 (via atlas/type_logical/Lambek.v).
*)

Require Import List.
Import ListNotations.
Require type_logical.Lambek.
Require montague.PTQ.

Import Lambek (denote).

Section Edge.

Variables (Entity : Type) (man walk : Entity -> Prop) (john : Entity).

(* E1.  "john walks": the Lambek derivation denotes the PTQ meaning. *)
Theorem lambek_computes_ptq_john :
  denote (Lambek.Fragment.interp Entity)
         Lambek.Fragment.d_john_walks (john, (walk, tt))
  = PTQ.john_walks Entity walk john.
Proof.
  rewrite (Lambek.Fragment.john_walks_sem Entity john walk); reflexivity.
Qed.

(* E2.  "every man walks": same generalized-quantifier meaning. *)
Theorem lambek_computes_ptq_every :
  denote (Lambek.Fragment.interp Entity)
         Lambek.Fragment.d_every_man_walks
         (Lambek.Fragment.every_sem Entity, (man, (walk, tt)))
  = PTQ.every_man_walks Entity man walk.
Proof.
  rewrite (Lambek.Fragment.every_man_walks_sem Entity man walk); reflexivity.
Qed.

(* E3.  "some/a man walks": Lambek's some_sem is PTQ's indefinite. *)
Theorem lambek_computes_ptq_some :
  denote (Lambek.Fragment.interp Entity)
         Lambek.Fragment.d_some_man_walks
         (Lambek.Fragment.some_sem Entity, (man, (walk, tt)))
  = PTQ.a_man_walks Entity man walk.
Proof.
  rewrite (Lambek.Fragment.some_man_walks_sem Entity man walk); reflexivity.
Qed.

(* E4.  Type raising IS Montague's star (T2): the Lambek derivation of
   np |- s/(np\s) denotes fun P => P john. *)
Theorem lambek_typeraise_is_star :
  denote (Lambek.Fragment.interp Entity)
         Lambek.Fragment.d_type_raise (john, tt)
  = PTQ.star Entity john.
Proof.
  rewrite (Lambek.Fragment.type_raise_sem Entity john); reflexivity.
Qed.

End Edge.

(* Assumption audit: all edge theorems inherit Lambek.v's axiom-free
   fragment; expected "Closed under the global context". *)
Print Assumptions lambek_computes_ptq_john.
Print Assumptions lambek_computes_ptq_every.
Print Assumptions lambek_computes_ptq_some.
Print Assumptions lambek_typeraise_is_star.
