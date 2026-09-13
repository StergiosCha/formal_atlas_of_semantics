(* Prospective P1 pilot, paper 66. Grice 1975 pp.49-51,57-58.
   Inventory/protocol: atlas_data/campaigns/pilot_2026_09_13_*.
   A constraint representation of the three stated conditions, not an
   algorithm deriving relevance or beliefs from an utterance. Compatibility
   and recognizability remain explicit inputs. The garage test's relevance
   constraint is an ENCODING ASSUMPTION, not a prediction independently
   derived from the maxims. No complete mechanization of implicature. *)

Section Conditions.
Variable BeliefState : Type.
Variable presumed_cooperative : Prop.
Variable compatible : BeliefState -> Prop.
Variable recognizable : Prop.
Definition calculable (q : BeliefState -> Prop) :=
  presumed_cooperative /\ (forall b, compatible b -> q b) /\ recognizable.

Theorem licensed_belief : forall q b,
  calculable q -> compatible b -> q b.
Proof. intros q b [_ [H _]] Hb; apply H; exact Hb. Qed.

(* P.57: opting out removes a presumption needed for this derivation.
   Does NOT claim that arbitrary negation of q is a cooperative utterance. *)
Theorem opting_out_blocks_this_derivation : forall q,
  ~ presumed_cooperative -> ~ calculable q.
Proof. intros q H [Hc _]; exact (H Hc). Qed.
End Conditions.

Module Garage.
(* P.51: the speaker thinks the garage is, or may be, open and selling
   petrol. Our bool abstracts that belief; it is not world truth. *)
Definition believes_usable (b : bool) := b = true.
Definition compatible (b : bool) := believes_usable b.
Definition inferred := calculable bool True compatible True believes_usable.

Theorem garage_belief_with_explicit_relevance_premise : inferred.
Proof. repeat split; auto. Qed.

(* P.58(4): what is said can be true while what is implicated is false.
   A concrete separation of world fact from the speaker's belief. *)
Theorem literal_and_inferred_do_not_entail_fact :
  exists (garage_exists garage_usable : bool),
    garage_exists = true /\ inferred /\ garage_usable <> true.
Proof. exists true, false; repeat split; try discriminate; auto. Qed.

Theorem literal_content_survives_opt_out :
  exists garage_exists : bool,
    garage_exists = true /\
    ~ calculable bool False compatible True believes_usable.
Proof. exists true; split; [reflexivity | intros [H _]; exact H]. Qed.
End Garage.
