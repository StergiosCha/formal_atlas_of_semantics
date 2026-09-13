(* MTT and DTS: explicit translations, not identical noun ontologies.
   BM17 section 1.4 pp. 17-19 uses Entity -> Type noun predicates;
   CL20 section 3.2 uses CN types and section 3.2.3 propositional forms
   of judgements.  BM17 p. 19 acknowledges the C&L treatment of negated
   and conditional predication.  Neither framework is shown incapable
   of those constructions by comparing raw typing judgements alone.

   The shared donkey reading below is restricted to Prop-valued
   predicates; it first builds noun types as Sigma packages of entities
   and noun evidence.  It does not remove proof relevance from arbitrary
   Type-valued DTS predicates, or identify proof search with MTT typing. *)
Require mtt_ranta.MTT mtt_ranta.Ranta mtt_ranta.DTS mtt_ranta.MTT_vs_Ranta.

Section Predication.
Variables (A Entity : Type) (c : A -> Entity).

(* CL20 propositional form: an arbitrary Entity need not already be A.
   DTS can use this image as one particular noun predicate. *)
Definition image_predicate : Entity -> Prop := MTT.in_prop A Entity c.

Theorem existential_image : forall Q : Entity -> Prop,
  MTT.some A (fun a => Q (c a)) <->
  exists e, image_predicate e /\ Q e.
Proof.
  intros Q; split.
  - intros [a Ha]; exists (c a); split; [exists a; reflexivity | exact Ha].
  - intros [e [[a Ha] HQ]]; exists a; rewrite Ha; exact HQ.
Qed.

Theorem universal_image : forall Q : Entity -> Prop,
  MTT.every A (fun a => Q (c a)) <->
  forall e, image_predicate e -> Q e.
Proof.
  intros Q; split.
  - intros H e [a <-]; apply H.
  - intros H a; apply H; exists a; reflexivity.
Qed.

(* Negative predication is an ordinary proposition in this comparison.
   Forming it does not require exhibiting an inhabitant of A over e. *)
Theorem negative_predication : forall e,
  ~ image_predicate e <-> forall a, c a <> e.
Proof.
  intros e; split.
  - intros H a E; apply H; exists a; exact E.
  - intros H [a E]; exact (H a E).
Qed.
End Predication.

Theorem negative_predication_without_positive_typing :
  ~ MTT.in_prop unit bool (fun _ => false) true.
Proof. intros [a E]; discriminate E. Qed.

Section Donkey.
Variable Entity : Type.
Variables farmer donkey : Entity -> Prop.
Variables own beat : Entity -> Entity -> Prop.

(* CN types are INDUCED from the DTS predicates, not assumed identical
   to the unrestricted Entity domain.  The source noun proofs remain
   in the context even though the final sentence is Prop-valued. *)
Theorem donkey_after_noun_translation :
  Ranta.tequiv (DTS.PredicateDTS.canonical Entity farmer donkey own beat)
    (MTT_vs_Ranta.mtt_donkey
      (DTS.PredicateDTS.farmer_type Entity farmer)
      (DTS.PredicateDTS.donkey_type Entity donkey)
      (fun x y => own (projT1 x) (projT1 y))
      (fun x y => beat (projT1 x) (projT1 y))).
Proof.
  exact (DTS.PredicateDTS.canonical_ranta_translation Entity farmer donkey own beat).
Qed.
End Donkey.

Print Assumptions existential_image.
Print Assumptions universal_image.
Print Assumptions negative_predication.
Print Assumptions negative_predication_without_positive_typing.
Print Assumptions donkey_after_noun_translation.
