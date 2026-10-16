(* Gallin p. 61, clauses (i)-(vii), applied to the actual source-first PTQ
   datatype. Source constants become functions of the explicit index.
   Box quantifies over all indices. Tense uses named relations on indices,
   an extension for PTQ (Gallin p. 10 footnote 1), not a clause of section 8. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target.
Import ListNotations.
Set Implicit Arguments.

Inductive source_symbol : gty -> Type :=
| IndexedConstant : forall a, nat -> source_symbol (garr gs (translate_type a))
| FutureRelation : source_symbol (garr gs (garr gs gt))
| PastRelation : source_symbol (garr gs (garr gs gt)).
Inductive source_parameter : gty -> Type :=
| SourceFree : forall a, nat -> source_parameter (translate_type a).
Definition target_term := gtm source_symbol source_parameter.

Definition index_future F (i j : index F) :=
  fst i = fst j /\ before F (snd i) (snd j).
Definition index_past F (i j : index F) :=
  fst i = fst j /\ before F (snd j) (snd i).
Definition target_lex (M : model) a (c : source_symbol a) : gdomain (carrier M) a :=
  match c in source_symbol a return gdomain (carrier M) a with
  | IndexedConstant a n => fun i => lift_value (carrier M) a (constants M a n i)
  | FutureRelation => fun i j => truth (boolean_truth M) (index_future i j)
  | PastRelation => fun i j => truth (boolean_truth M) (index_past i j)
  end.
Definition target_free (M : model) (sigma : free_env M) a (v : source_parameter a)
  : gdomain (carrier M) a :=
  match v in source_parameter a return gdomain (carrier M) a with
  | SourceFree a n => lift_value (carrier M) a (sigma a n)
  end.
Definition target_eval M sigma {G a} (p : target_term G a) rho :=
  geval (boolean_truth M) (target_lex M) (target_free sigma) p rho.
Arguments target_eval M sigma {G a} p rho.

Definition variable_map G D := forall a, var G a -> gvar D (translate_type a).
Definition shift_map {G D a} (r : variable_map G D) : variable_map G (a :: D) :=
  fun b v => gvs (r b v).
Definition lift_map {G D a} (r : variable_map G D)
  : variable_map (a :: G) (translate_type a :: D) :=
  fun b v => match v in var G' b' return
    match G' with [] => unit
    | c :: G0 => variable_map G0 D -> gvar (translate_type c :: D) (translate_type b')
    end with
  | @vz _ _ => fun _ => gz
  | @vs _ _ _ w => fun r0 => gvs (r0 _ w)
  end r.
Fixpoint canonical_map {G a} (v : var G a) : gvar (map translate_type G) (translate_type a) :=
  match v with vz => gz | vs w => gvs (canonical_map w) end.

Fixpoint compile {G a} (u : tm G a) : forall D,
  variable_map G D -> target_term D gs -> target_term D (translate_type a) :=
  match u in tm G' a' return forall D,
    variable_map G' D -> target_term D gs -> target_term D (translate_type a') with
  | Var v => fun D r _ => GVar (r _ v)
  | Free n => fun D _ _ => GFree (SourceFree _ n)
  | Con n => fun D _ i => GApp (GCon (IndexedConstant _ n)) i
  | Lam p => fun D r i => GLam (compile p (lift_map r) (gweaken i))
  | App p q => fun D r i => GApp (compile p r i) (compile q r i)
  | Eq p q => fun D r i => GEq (compile p r i) (compile q r i)
  | Neg p => fun D r i => GNeg (compile p r i)
  | And p q => fun D r i => GAnd (compile p r i) (compile q r i)
  | Or p q => fun D r i => GOr (compile p r i) (compile q r i)
  | Imp p q => fun D r i => GImp (compile p r i) (compile q r i)
  | Iff p q => fun D r i => GIff (compile p r i) (compile q r i)
  | All p => fun D r i => GAll (compile p (lift_map r) (gweaken i))
  | Ex p => fun D r i => GEx (compile p (lift_map r) (gweaken i))
  | Box p => fun D r _ => GAll (compile p (shift_map r) (GVar gz))
  | Will p => fun D r i => GEx (GAnd
      (GApp (GApp (GCon FutureRelation) (gweaken i)) (GVar gz))
      (compile p (shift_map r) (GVar gz)))
  | Has p => fun D r i => GEx (GAnd
      (GApp (GApp (GCon PastRelation) (gweaken i)) (GVar gz))
      (compile p (shift_map r) (GVar gz)))
  | Up p => fun D r _ => GLam (compile p (shift_map r) (GVar gz))
  | Down p => fun D r i => GApp (compile p r i) i
  end.

Definition environments_match M G D (r : variable_map G D)
  (rho : genv (carrier M) D) (tau : env M G) :=
  forall a v, rho _ (r a v) = lift_value (carrier M) a (tau a v).
Lemma shifted_environments (M : model) G D a (r : variable_map G D) rho (tau : env M G) x :
  environments_match r rho tau ->
  environments_match (@shift_map G D a r) (gextend rho x) tau.
Proof. intros H b v; apply H. Qed.
Lemma lifted_environments (M : model) G D a (r : variable_map G D) rho (tau : env M G) x :
  environments_match r rho tau ->
  environments_match (@lift_map G D a r) (gextend rho x)
    (extend tau (lower_value (carrier M) a x)).
Proof.
  intros H; unfold environments_match; apply var_cases; cbn.
  - symmetry; apply lift_lower.
  - intros; apply H.
Qed.

Section Preservation.
Variable M : model.
Variable sigma : free_env M.
Local Notation F := (carrier M).
Local Notation B := (boolean_truth M).
Local Notation FE := (function_extensionality M).
Local Notation E := (target_eval M sigma).

Lemma target_weaken G a b (p : target_term G b) rho x :
  E (@gweaken _ _ G a b p) (gextend rho x) = E p rho.
Proof. apply geval_weaken; exact FE. Qed.

(* Source eval and target geval are independently defined recursors.
   This induction covers every constructor, not only closed examples. *)
Theorem interpretation_preservation G a (p : tm G a) : forall D
  (r : variable_map G D) (i : target_term D gs) rho tau,
  environments_match r rho tau ->
  E (compile p r i) rho = lift_value F a (eval M p tau sigma (E i rho)).
Proof.
  induction p; intros D r i rho tau H; cbn [compile].
  - apply H.
  - reflexivity.
  - reflexivity.
  - match goal with |- _ = ?rhs => change ((fun x => E (compile p (lift_map r) (gweaken i)) (gextend rho x)) = rhs) end.
    rewrite lift_lambda; apply FE; intro x.
    rewrite IHp with (tau := extend tau (lower_value F a x));
      [rewrite target_weaken; reflexivity | apply lifted_environments; exact H].
  - match goal with |- _ = ?rhs => change (E (compile p1 r i) rho (E (compile p2 r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
    apply lift_application.
  - match goal with |- _ = ?rhs => change (truth B (E (compile p1 r i) rho = E (compile p2 r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
    apply truth_congr; split; intro K.
    + apply (f_equal (lower_value F a)) in K; rewrite !lower_lift in K; exact K.
    + exact (f_equal (lift_value F a) K).
  - match goal with |- _ = ?rhs => change (negb (E (compile p r i) rho) = rhs) end.
    rewrite IHp with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (andb (E (compile p1 r i) rho) (E (compile p2 r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (orb (E (compile p1 r i) rho) (E (compile p2 r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (orb (negb (E (compile p1 r i) rho)) (E (compile p2 r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (Bool.eqb (E (compile p1 r i) rho) (E (compile p2 r i) rho) = rhs) end.
    rewrite IHp1 with (tau := tau), IHp2 with (tau := tau); auto.
  - match goal with |- _ = ?rhs => change (truth B (forall x, E (compile p (lift_map r) (gweaken i)) (gextend rho x) = true) = rhs) end.
    assert (K : forall x, E (compile p (lift_map r) (gweaken i)) (gextend rho x) =
      eval M p (extend tau (lower_value F a x)) sigma (E i rho)).
    { intro x; rewrite IHp with (tau := extend tau (lower_value F a x));
        [rewrite target_weaken; reflexivity | apply lifted_environments; exact H]. }
    apply truth_congr; setoid_rewrite K.
    split; intros Q x.
    + specialize (Q (lift_value F a x)); rewrite lower_lift in Q; exact Q.
    + apply Q.
  - match goal with |- _ = ?rhs => change (truth B (exists x, E (compile p (lift_map r) (gweaken i)) (gextend rho x) = true) = rhs) end.
    assert (K : forall x, E (compile p (lift_map r) (gweaken i)) (gextend rho x) =
      eval M p (extend tau (lower_value F a x)) sigma (E i rho)).
    { intro x; rewrite IHp with (tau := extend tau (lower_value F a x));
        [rewrite target_weaken; reflexivity | apply lifted_environments; exact H]. }
    apply truth_congr; setoid_rewrite K.
    split; intros [x Q].
    + exists (lower_value F a x); exact Q.
    + exists (lift_value F a x); rewrite lower_lift; exact Q.
  - match goal with |- _ = ?rhs => change (truth B (forall j, E (compile p (shift_map r) (GVar gz)) (gextend rho j) = true) = rhs) end.
    apply truth_congr.
    assert (K : forall j, E (compile p (shift_map r) (GVar gz)) (gextend rho j) =
      eval M p tau sigma j).
    { intro j; apply IHp; apply shifted_environments; exact H. }
    cbn [eval]; setoid_rewrite K; reflexivity.
  - match goal with |- _ = ?rhs => change (truth B (exists j : index F, andb (truth B (index_future (E (@gweaken _ _ D gs gs i) (@gextend F D gs rho j)) j)) (E (compile p (shift_map r) (GVar gz)) (@gextend F D gs rho j)) = true) = rhs) end.
    apply truth_congr; cbn [eval].
    assert (K : forall j, E (compile p (shift_map r) (GVar gz)) (gextend rho j) = eval M p tau sigma j).
    { intro j; apply IHp; apply shifted_environments; exact H. }
    setoid_rewrite target_weaken; setoid_rewrite K.
    setoid_rewrite Bool.andb_true_iff; setoid_rewrite truth_spec.
    unfold index_future; destruct (E i rho) as [w now]; cbn.
    split.
    + intros [[w' later] [[Hw Hb] Hp]]; cbn in *; subst w'; exists later; auto.
    + intros [later [Hb Hp]]; exists (w,later); cbn; auto.
  - match goal with |- _ = ?rhs => change (truth B (exists j : index F, andb (truth B (index_past (E (@gweaken _ _ D gs gs i) (@gextend F D gs rho j)) j)) (E (compile p (shift_map r) (GVar gz)) (@gextend F D gs rho j)) = true) = rhs) end.
    apply truth_congr; cbn [eval].
    assert (K : forall j, E (compile p (shift_map r) (GVar gz)) (gextend rho j) = eval M p tau sigma j).
    { intro j; apply IHp; apply shifted_environments; exact H. }
    setoid_rewrite target_weaken; setoid_rewrite K.
    setoid_rewrite Bool.andb_true_iff; setoid_rewrite truth_spec.
    unfold index_past; destruct (E i rho) as [w now]; cbn.
    split.
    + intros [[w' earlier] [[Hw Hb] Hp]]; cbn in *; subst w'; exists earlier; auto.
    + intros [earlier [Hb Hp]]; exists (w,earlier); cbn; auto.
  - match goal with |- _ = ?rhs => change ((fun j => E (compile p (shift_map r) (GVar gz)) (gextend rho j)) = rhs) end.
    rewrite lift_intension; apply FE; intro j; apply IHp.
    apply shifted_environments; exact H.
  - match goal with |- _ = ?rhs => change (E (compile p r i) rho (E i rho) = rhs) end.
    rewrite IHp with (tau := tau); auto.
    rewrite lift_intension; reflexivity.
Qed.
End Preservation.

Fixpoint canonical_env (M : model) G : env M G -> genv (carrier M) (map translate_type G) :=
  match G return env M G -> genv (carrier M) (map translate_type G) with
  | [] => fun _ => gempty (carrier M)
  | a :: G => fun rho => gextend
      (@canonical_env M G (fun b v => rho b (vs v)))
      (lift_value (carrier M) a (rho a vz))
  end.
Lemma canonical_environments_match M G (rho : env M G) :
  environments_match (@canonical_map G) (canonical_env rho) rho.
Proof.
  induction G as [|a G IH].
  - intros b v; inversion v.
  - unfold environments_match; apply var_cases; cbn.
    + reflexivity.
    + intros; apply IH.
Qed.
Definition translate_intension {G a} (p : tm G a)
  : target_term (map translate_type G) (garr gs (translate_type a)) :=
  GLam (compile p (shift_map (@canonical_map G)) (GVar gz)).

Theorem open_preservation M G a (p : tm G a) rho sigma i :
  target_eval M sigma (translate_intension p) (canonical_env rho) i =
  lift_value (carrier M) a (eval M p rho sigma i).
Proof.
  match goal with |- _ = ?rhs =>
    change (target_eval M sigma (compile p (shift_map (@canonical_map G)) (GVar gz))
      (@gextend (carrier M) (map translate_type G) gs (canonical_env rho) i) = rhs)
  end.
  apply interpretation_preservation; apply shifted_environments.
  apply canonical_environments_match.
Qed.
Corollary closed_preservation M a (p : tm [] a) sigma i :
  target_eval M sigma (translate_intension p) (gempty (carrier M)) i =
  lift_value (carrier M) a (eval M p (empty_env M) sigma i).
Proof. exact (@open_preservation M [] a p (empty_env M) sigma i). Qed.
Corollary translated_truth_iff M G (p : tm G t) rho sigma i :
  target_eval M sigma (translate_intension p) (canonical_env rho) i = true <->
  eval M p rho sigma i = true.
Proof. rewrite open_preservation; reflexivity. Qed.
Corollary translated_counterexample_iff M G (p q : tm G t) rho sigma i :
  (target_eval M sigma (translate_intension p) (canonical_env rho) i = true /\
   target_eval M sigma (translate_intension q) (canonical_env rho) i = false) <->
  (eval M p rho sigma i = true /\ eval M q rho sigma i = false).
Proof. rewrite !open_preservation; reflexivity. Qed.
