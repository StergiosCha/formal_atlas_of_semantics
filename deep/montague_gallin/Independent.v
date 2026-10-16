(* Independent standard Ty2 models, Gallin pp. 59-62.
   General entity/index carriers are separate from PTQ. For the full
   tensed source, correspondence is proved for models on a declared
   world-time frame whose temporal symbols satisfy the two explicit laws.
   Full internal function spaces, not Henkin subdomains. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation.
Import ListNotations.
Set Implicit Arguments.

Record standard_model (S : gty -> Type) := {
  standard_entities : Type;
  standard_indices : Type;
  entities_inhabited : inhabited standard_entities;
  indices_inhabited : inhabited standard_indices;
  standard_truth : BooleanTruth;
  standard_extensionality : FunExt;
  standard_lex : forall a, S a -> value_domain standard_entities standard_indices a
}.
Definition standard_assignment {S} (N : standard_model S) P :=
  forall a, P a -> value_domain (standard_entities N) (standard_indices N) a.
Definition standard_eval {S P} (N : standard_model S) (theta : standard_assignment N P)
  {G a} (p : gtm S P G a) rho := geval (standard_truth N) (standard_lex N) theta p rho.
Arguments standard_eval {S P} N theta {G a} p rho.

(* This is an independent target interpretation on a specified PTQ frame.
   No source model, source constant valuation, or preservation theorem is
   a field of this record. Temporal coherence is a semantic restriction. *)
Record coherent_model (F : frame) := {
  coherent_truth : BooleanTruth;
  coherent_extensionality : FunExt;
  coherent_lex : forall a, source_symbol a -> gdomain F a;
  future_coherence : forall i j,
    coherent_lex FutureRelation i j = true <-> index_future i j;
  past_coherence : forall i j,
    coherent_lex PastRelation i j = true <-> index_past i j
}.
Definition coherent_assignment F := forall a, source_parameter a -> gdomain F a.
Definition coherent_eval {F} (N : coherent_model F) (theta : coherent_assignment F)
  {G a} (p : target_term G a) rho := geval (coherent_truth N) (coherent_lex N) theta p rho.

Lemma index_inhabited F : inhabited (index F).
Proof.
  destruct (world_nonempty F) as [w], (time_nonempty F) as [t].
  exact (inhabits (w,t)).
Qed.
Definition as_standard F (N : coherent_model F) : standard_model source_symbol :=
  {| standard_entities := entity F; standard_indices := index F;
     entities_inhabited := entity_nonempty F; indices_inhabited := index_inhabited F;
     standard_truth := coherent_truth N; standard_extensionality := coherent_extensionality N;
     standard_lex := coherent_lex N |}.

Definition embed_model (M : model) : coherent_model (carrier M).
Proof.
  refine {| coherent_truth := boolean_truth M;
    coherent_extensionality := function_extensionality M;
    coherent_lex := target_lex M |}; intros; apply truth_spec.
Defined.
Definition reconstruct_model F (N : coherent_model F) : model :=
  {| carrier := F; boolean_truth := coherent_truth N;
     function_extensionality := coherent_extensionality N;
     constants := fun a n i => lower_value F a (coherent_lex N (IndexedConstant a n) i) |}.
Definition reconstruct_assignment F (N : coherent_model F) (theta : coherent_assignment F)
  : free_env (reconstruct_model N) :=
  fun a n => lower_value F a (theta _ (SourceFree a n)).

Lemma truth_from_spec B P b : (b = true <-> P) -> truth B P = b.
Proof.
  intro H; destruct b; destruct (truth B P) eqn:HB; auto.
  - assert (HP : P) by (apply H; reflexivity).
    apply (proj2 (truth_spec B P)) in HP; congruence.
  - apply (proj1 (truth_spec B P)) in HB.
    apply H in HB; discriminate.
Qed.

Theorem target_symbols_recovered F (N : coherent_model F) a (c : source_symbol a) :
  target_lex (reconstruct_model N) c = coherent_lex N c.
Proof.
  destruct c; cbn [target_lex reconstruct_model].
  - apply (coherent_extensionality N); intro i; apply lift_lower.
  - apply (coherent_extensionality N); intro i.
    apply (coherent_extensionality N); intro j.
    apply truth_from_spec; apply future_coherence.
  - apply (coherent_extensionality N); intro i.
    apply (coherent_extensionality N); intro j.
    apply truth_from_spec; apply past_coherence.
Qed.
Theorem target_free_values_recovered F (N : coherent_model F)
  (theta : coherent_assignment F) a (v : source_parameter a) :
  target_free (reconstruct_assignment N theta) v = theta a v.
Proof. destruct v; apply lift_lower. Qed.
Theorem source_constant_values_recovered M a n i :
  constants (reconstruct_model (embed_model M)) a n i = constants M a n i.
Proof. apply lower_lift. Qed.
Theorem source_free_values_recovered M (sigma : free_env M) a n :
  reconstruct_assignment (embed_model M) (target_free sigma) a n = sigma a n.
Proof. apply lower_lift. Qed.

(* The round trip preserves every target expression in this signature,
   including expressions outside the translation's syntactic image. *)
Theorem target_roundtrip_interpretation F (N : coherent_model F)
  (theta : coherent_assignment F) G a (p : target_term G a) rho :
  coherent_eval N theta p rho =
  target_eval (reconstruct_model N) (reconstruct_assignment N theta) p rho.
Proof.
  unfold coherent_eval, target_eval.
  apply geval_extensional; [exact (coherent_extensionality N) | |].
  - intros; symmetry; apply target_symbols_recovered.
  - intros; symmetry; apply target_free_values_recovered.
Qed.

Theorem backward_preservation F (N : coherent_model F) (theta : coherent_assignment F)
  a (p : tm [] a) i :
  coherent_eval N theta (translate_intension p) (gempty F) i =
  lift_value F a (eval (reconstruct_model N) p (empty_env _)
    (reconstruct_assignment N theta) i).
Proof. rewrite target_roundtrip_interpretation, closed_preservation; reflexivity. Qed.
Theorem forward_preservation M sigma a (p : tm [] a) i :
  coherent_eval (embed_model M) (target_free sigma) (translate_intension p)
    (gempty (carrier M)) i =
  lift_value (carrier M) a (eval M p (empty_env M) sigma i).
Proof. exact (@closed_preservation M a p sigma i). Qed.

Theorem embedded_arbitrary_assignment M (theta : coherent_assignment (carrier M))
  G a (p : target_term G a) rho :
  coherent_eval (embed_model M) theta p rho =
  target_eval M (reconstruct_assignment (embed_model M) theta) p rho.
Proof.
  unfold coherent_eval, target_eval; apply geval_extensional.
  - exact (function_extensionality M).
  - intros; reflexivity.
  - intros; symmetry; apply target_free_values_recovered.
Qed.

Definition reference_assignment F (N : coherent_model F) (i : index F)
  : coherent_assignment F :=
  fun a v => match v in source_parameter a return gdomain F a with
  | SourceFree b n => coherent_lex N (IndexedConstant b n) i
  end.

(* Formula truth, not equality of records containing proof fields. *)
Theorem coherent_standard_interpretation F (N : coherent_model F)
  theta G a (p : target_term G a) rho :
  standard_eval (as_standard N) theta p rho = coherent_eval N theta p rho.
Proof. reflexivity. Qed.
