(* PTQ p. 31: quantifier order, actual source reductions, and a separating
   model satisfying every lexical postulate. *)
From Coq Require Import List Bool Arith.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning
  Postulates Examples Catalogue Reductions.
Import ListNotations.
Set Implicit Arguments.

Lemma love_every_man_reduction M (A : admissible M) x i :
  word_value M (ltv love) i
    (fun j => dvalue M every (word_value M (lcn man) j) j) x = true <->
  forall v, cn_star M man i v = true -> tv_star M love i (x i) v = true.
Proof.
  rewrite (@tv_extensional_reduction M A love I).
  apply (universal_reduction A man I).
Qed.

Theorem surface_scope_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed woman_loves_every_man) (empty_env M) sigma i = true <->
  exists u, cn_star M woman i u = true /\
    forall v, cn_star M man i v = true -> tv_star M love i u v = true.
Proof.
  rewrite closed_translation_interpretation.
  change (dvalue M a_or_an (word_value M (lcn woman) i) i
    (fun j x => word_value M (ltv love) j
      (fun k => dvalue M every (word_value M (lcn man) k) k) x) = true <->
    exists u, cn_star M woman i u = true /\
      forall v, cn_star M man i v = true -> tv_star M love i u v = true).
  rewrite (indefinite_reduction A woman I).
  setoid_rewrite (love_every_man_reduction A); reflexivity.
Qed.

Lemma woman_loves_concept_reduction M (A : admissible M) x i :
  dvalue M a_or_an (word_value M (lcn woman) i) i
    (fun j y => word_value M (ltv love) j (fun k P => P k x) y) = true <->
  exists u, cn_star M woman i u = true /\ tv_star M love i u (x i) = true.
Proof.
  rewrite (indefinite_reduction A woman I).
  setoid_rewrite (@tv_extensional_reduction M A love I); reflexivity.
Qed.

Theorem inverse_scope_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed every_man_loved_by_a_woman) (empty_env M) sigma i = true <->
  forall v, cn_star M man i v = true ->
    exists u, cn_star M woman i u = true /\ tv_star M love i u v = true.
Proof.
  rewrite closed_translation_interpretation.
  change (dvalue M every (word_value M (lcn man) i) i
    (fun j x => dvalue M a_or_an (word_value M (lcn woman) j) j
      (fun k y => word_value M (ltv love) k (fun l P => P l x) y)) = true <->
    forall v, cn_star M man i v = true ->
      exists u, cn_star M woman i u = true /\ tv_star M love i u v = true).
  rewrite (universal_reduction A man I).
  setoid_rewrite (woman_loves_concept_reduction A); reflexivity.
Qed.

Definition scope_constants B a n i : domain two_times a :=
  match ty_eq_dec ivty a with
  | left H => carry H (fun x =>
      if (Nat.eqb n 5 || Nat.eqb n 6)%bool
      then truth B (exists u, x = (fun _ => u)) else false)
  | right _ => match ty_eq_dec (category_type TV) a with
    | left H => carry H (fun Q x =>
        if Nat.eqb n 16 then Q i (fun j y => truth B (x j = y j))
        else if (Nat.leb 13 n && Nat.leb n 17)%bool then Q i (fun _ _ => false)
        else true)
    | right _ => sample_constants B a n i
    end
  end.
Definition scope_model B FE : model :=
  {| carrier := two_times; boolean_truth := B; function_extensionality := FE;
     constants := scope_constants B |}.
Definition scope_assignment B FE : free_env (scope_model B FE) := fun a _ => zero_value a.

Theorem scope_model_admissible B FE : admissible (scope_model B FE).
Proof.
  constructor.
  - intro n; exists false; destruct n; reflexivity.
  - intros c O i x H; destruct c; cbn in O; try contradiction;
      try discriminate; apply truth_spec in H; exact H.
  - intros v O; exists (fun _ _ => false); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v O; destruct v; cbn in O; try contradiction.
    + exists (fun _ _ _ => false); reflexivity.
    + exists (fun _ _ _ => false); reflexivity.
    + exists (fun _ _ _ => false); reflexivity.
    + exists (fun _ x y => truth B (x = y)); reflexivity.
    + exists (fun _ _ _ => false); reflexivity.
  - intros v O Q; exists (fun _ _ => true); destruct v; cbn in O; try contradiction; reflexivity.
  - intros v p; exists (fun _ _ => true); destruct v; reflexivity.
  - intros v Q; exists (fun _ _ => true); destruct v; reflexivity.
  - exists (fun _ _ _ _ => false); reflexivity.
  - unfold mp9; intros; reflexivity.
Qed.

Lemma scope_nouns B FE c i u : c = man \/ c = woman ->
  cn_star (scope_model B FE) c i u = true.
Proof.
  intros [E|E]; subst c; apply truth_spec; exists u; reflexivity.
Qed.
Lemma scope_love B FE i u v :
  tv_star (scope_model B FE) love i u v = true <-> u = v.
Proof. apply truth_spec. Qed.

Theorem quantifier_readings_separated B FE :
  let M := scope_model B FE in
  admissible M /\
  eval M (translate_closed woman_loves_every_man) (empty_env M) (scope_assignment B FE) (tt,false) = false /\
  eval M (translate_closed every_man_loved_by_a_woman) (empty_env M) (scope_assignment B FE) (tt,false) = true.
Proof.
  cbn zeta; split; [apply scope_model_admissible |]; split.
  - destruct (eval (scope_model B FE) (translate_closed woman_loves_every_man)
      (empty_env _) (scope_assignment B FE) (tt,false)) eqn:E; auto.
    apply (proj1 (surface_scope_source_reduction (scope_model_admissible B FE) _ _)) in E.
    destruct E as [u [W H]].
    assert (H0 : u = false).
    { apply (proj1 (@scope_love B FE (tt,false) u false)); apply H; apply scope_nouns; auto. }
    assert (H1 : u = true).
    { apply (proj1 (@scope_love B FE (tt,false) u true)); apply H; apply scope_nouns; auto. }
    congruence.
  - apply (proj2 (inverse_scope_source_reduction (scope_model_admissible B FE) _ _)).
    intros v V; exists v; split; [apply scope_nouns; auto | apply scope_love; reflexivity].
Qed.
