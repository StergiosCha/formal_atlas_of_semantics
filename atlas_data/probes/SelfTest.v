(* Self-test for VacuityProbe (A3 L2). Three deliberately shaped lemmas:

     st_vacuous   n < 0 -> 1 = 2      hypotheses unsatisfiable  => vacuity VACUOUS
                                       stripped goal 1 = 2 unprovable => triviality ok
     st_normal    n <= m -> n <= S m  honest lemma              => both ok
     st_trivial   n > 5 -> hidden_true (:= True)                => triviality TRIVIAL
                                       (exact I through conversion), vacuity ok

   run_probes.py --selftest compiles this file and checks the six PROBE lines
   exactly; a mismatch aborts the whole probe run. *)

Require Import Lia.

Lemma st_vacuous : forall n : nat, n < 0 -> 1 = 2.
Proof. intros n H. exfalso. lia. Qed.

Lemma st_normal : forall n m : nat, n <= m -> n <= S m.
Proof. intros. lia. Qed.

Definition hidden_true : Prop := True.

Lemma st_trivial : forall n : nat, n > 5 -> hidden_true.
Proof. intros. exact I. Qed.

From Ltac2 Require Import Ltac2.
Require VacuityProbe.

Goal True.
Proof.
  VacuityProbe.probe_theorem "SelfTest.st_vacuous" reference:(st_vacuous).
  VacuityProbe.probe_theorem "SelfTest.st_normal" reference:(st_normal).
  VacuityProbe.probe_theorem "SelfTest.st_trivial" reference:(st_trivial).
Abort.
