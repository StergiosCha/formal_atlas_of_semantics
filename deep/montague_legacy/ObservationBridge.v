(* A guarded comparison of the EXISTING Boolean Ty2 evaluator with the
   EXISTING Prop-valued explicit-index evaluator. It neither imports the
   legacy parameters nor identifies arbitrary Prop and Boolean domains. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Models Calculus BooleanModels BooleanFinite Ty2Syntax Ty2Models Ty2Calculus.
From MontagueLegacy Require Import IndexSyntax IndexModels.
Import ListNotations.
Set Implicit Arguments.

Fixpoint observation_type (a : wty) : pty :=
  match a with
  | we => pe | wt => pt | ws => pw
  | warr a b => parr (observation_type a) (observation_type b)
  end.
Fixpoint observation_var {G a} (v : wvar G a) : pvar (map observation_type G) (observation_type a) :=
  match v with wz => pz | wvs v => pvs (observation_var v) end.

Section Translation.
Context {symbol : wty -> Type} {target : pty -> Type}.
Variable constants : forall a, symbol a -> target (observation_type a).
Fixpoint observation_term {G a} (t : wtm symbol G a) :
  ptm target (map observation_type G) (observation_type a) :=
  match t in wtm _ G' a' return ptm target (map observation_type G') (observation_type a') with
  | WVar v => PVar (observation_var v)
  | WConst c => PConst (@constants _ c)
  | WLam t => PLam (observation_term t)
  | WApp f x => PApp (observation_term f) (observation_term x)
  | WImp p q => PImp (observation_term p) (observation_term q)
  | WAll p => PAll (observation_term p)
  end.
End Translation.

(* A certificate on actual Ty2 terms. Higher-order lambda/application are
   allowed under related values, but general quantification is only e or s.
   Encoded falsity is separately justified; not arbitrary quantification at t. *)
Inductive observation_sort : wty -> Prop :=
| observe_entities : observation_sort we
| observe_worlds : observation_sort ws.

Inductive observable {symbol} : forall G a, wtm symbol G a -> Prop :=
| observe_var : forall G a (v : wvar G a), observable (WVar v)
| observe_const : forall G a (c : symbol a), observable (@WConst symbol G a c)
| observe_lam : forall G a b (t : wtm symbol (a :: G) b), observable t -> observable (WLam t)
| observe_app : forall G a b (f : wtm symbol G (warr a b)) x,
    observable f -> observable x -> observable (WApp f x)
| observe_imp : forall G (p q : wtm symbol G wt),
    observable p -> observable q -> observable (WImp p q)
| observe_all : forall G a (p : wtm symbol (a :: G) wt),
    observation_sort a -> observable p -> observable (WAll p)
| observe_false : forall G, observable (@wfalsity symbol G).

Lemma observable_renaming : forall symbol G a (t : wtm symbol G a), observable t ->
  forall D (r : wren G D), observable (wrename t r).
Proof.
  intros symbol G a t H; induction H; intros D r; cbn;
    eauto using observe_var, observe_const, observe_lam, observe_app, observe_imp, observe_all, observe_false.
Qed.

Lemma observable_weakening : forall symbol G a b (t : wtm symbol G b), observable t ->
  observable (@wweaken symbol G a b t).
Proof. intros; apply observable_renaming; assumption. Qed.

Lemma observable_negation : forall symbol G (p : wtm symbol G wt), observable p -> observable (wneg p).
Proof. intros; apply observe_imp; [assumption | apply observe_false]. Qed.

Lemma observable_necessity : forall symbol G (p : wtm symbol G (warr ws wt)),
  observable p -> observable (necessarily p).
Proof.
  intros; apply observe_all; [apply observe_worlds |].
  apply observe_app; [apply observable_weakening; assumption | apply observe_var].
Qed.

Section Relation.
Context {E W T : Type}.
Fixpoint observation_relation (a : wty) :
  pdomain E W T (observation_type a) -> wdomain E W a -> Prop :=
  match a with
  | we => fun p b => p = b
  | ws => fun p b => p = b
  | wt => fun p b => p <-> b = true
  | warr a b => fun p q => forall x y, observation_relation a x y ->
      observation_relation b (p x) (q y)
  end.
End Relation.

Section Preservation.
Context {symbol : wty -> Type} {target : pty -> Type} (M : wmodel symbol).
Context {T : Type}.
Variable constants : forall a, symbol a -> target (observation_type a).
Variable lex : forall a, target a -> pdomain (windividuals M) (worlds M) T a.
Variable before : T -> T -> Prop.
Hypothesis lexical_relation : forall a (c : symbol a),
  observation_relation a (@lex _ (@constants a c)) (wlexical M a c).

Definition observation_envs {G}
  (rho : @penv (windividuals M) (worlds M) T (map observation_type G)) (sigma : wenv M G) :=
  forall a (v : wvar G a), observation_relation a (rho _ (observation_var v)) (sigma _ v).

Lemma observation_envs_extend : forall G a rho sigma x y,
  @observation_envs G rho sigma -> observation_relation a x y ->
  @observation_envs (a :: G) (pextend rho x) (wextend sigma y).
Proof.
  intros G a rho sigma x y H R; unfold observation_envs;
    apply (@wvar_cons_cases G a);
    cbn; [exact R | intros; apply H].
Qed.

Theorem observation_preservation : forall G a (t : wtm symbol G a), observable t ->
  forall rho sigma, observation_envs rho sigma ->
  observation_relation a (peval lex before (observation_term constants t) rho) (weval M t sigma).
Proof.
  intros G a t H; induction H; intros rho sigma R; cbn -[observation_relation] in *.
  - apply R.
  - apply lexical_relation.
  - cbn; intros x y XY; apply IHobservable; apply observation_envs_extend; assumption.
  - exact (IHobservable1 rho sigma R _ _ (IHobservable2 rho sigma R)).
  - change ((peval lex before (observation_term constants p) rho ->
      peval lex before (observation_term constants q) rho) <->
      bimp (weval M p sigma) (weval M q sigma) = true).
    pose proof (IHobservable1 rho sigma R) as P.
    pose proof (IHobservable2 rho sigma R) as Q.
    cbn [observation_relation] in P, Q; rewrite bimp_spec; tauto.
  - destruct H; cbn; rewrite wforall_spec; split; intros A x.
    + apply (proj1 (IHobservable _ _ (@observation_envs_extend G we rho sigma x x R eq_refl))); apply A.
    + apply (proj2 (IHobservable _ _ (@observation_envs_extend G we rho sigma x x R eq_refl))); apply A.
    + apply (proj1 (IHobservable _ _ (@observation_envs_extend G ws rho sigma x x R eq_refl))); apply A.
    + apply (proj2 (IHobservable _ _ (@observation_envs_extend G ws rho sigma x x R eq_refl))); apply A.
  - change ((forall P : Prop, P) <-> weval M (@wfalsity symbol G) sigma = true).
    rewrite wfalsity_value; split; [intro A; exact (False_rect _ (A False)) | discriminate].
Qed.

Corollary observation_truth : forall G (p : wtm symbol G wt), observable p ->
  forall rho sigma, observation_envs rho sigma ->
  peval lex before (observation_term constants p) rho <-> weval M p sigma = true.
Proof. intros; exact (observation_preservation H H0). Qed.

Corollary observation_refutation : forall G (p : wtm symbol G wt), observable p ->
  forall rho sigma, observation_envs rho sigma ->
  ~ peval lex before (observation_term constants p) rho <-> weval M p sigma = false.
Proof.
  intros G p H rho sigma R; rewrite (observation_truth H R).
  destruct (weval M p sigma); intuition discriminate.
Qed.

Theorem certified_observation_is_decidable : forall G (p : wtm symbol G wt), observable p ->
  forall rho sigma, observation_envs rho sigma ->
  peval lex before (observation_term constants p) rho \/
  ~ peval lex before (observation_term constants p) rho.
Proof.
  intros G p H rho sigma R; pose proof (observation_truth H R) as I.
  destruct (weval M p sigma); intuition discriminate.
Qed.

Theorem observation_inference_agreement : forall G (premises : list (wtm symbol G wt)) (q : wtm symbol G wt),
  Forall (@observable symbol G wt) premises -> observable q -> forall rho sigma, observation_envs rho sigma ->
  ((forall p, In p premises -> peval lex before (observation_term constants p) rho) ->
    peval lex before (observation_term constants q) rho) <->
  ((forall p, In p premises -> weval M p sigma = true) -> weval M q sigma = true).
Proof.
  intros G premises q Ps Q rho sigma R.
  assert (P : (forall p, In p premises -> peval lex before (observation_term constants p) rho) <->
      (forall p, In p premises -> weval M p sigma = true)).
  { split; intros A p Hin;
      pose proof (proj1 (Forall_forall (@observable symbol G wt) premises) Ps p Hin) as H;
      [apply (proj1 (observation_truth H R)) | apply (proj2 (observation_truth H R))]; apply A; exact Hin. }
  pose proof (observation_truth Q R) as QR; tauto.
Qed.

Theorem observation_counterexample_agreement : forall G (p q : wtm symbol G wt),
  observable p -> observable q -> forall rho sigma, observation_envs rho sigma ->
  (peval lex before (observation_term constants p) rho /\
   ~ peval lex before (observation_term constants q) rho) <->
  (weval M p sigma = true /\ weval M q sigma = false).
Proof. intros; rewrite (observation_truth H H1), (observation_refutation H0 H1); reflexivity. Qed.

Theorem observable_derivation_prop_sound (FE : FunExt) : forall L G
  (premises : list (wtm symbol G wt)) q,
  Forall (@observable symbol G wt) premises -> observable q -> wderives L premises q ->
  forall rho sigma, observation_envs rho sigma ->
  (forall p, In p premises -> peval lex before (observation_term constants p) rho) ->
  peval lex before (observation_term constants q) rho.
Proof.
  intros L G premises q Ps Q D rho sigma R.
  apply (proj2 (observation_inference_agreement Ps Q R)).
  exact (world_derivation_sound FE D (M:=M) (rho:=sigma)).
Qed.

(* Witnesshood is an observation on an e-predicate, not a newly added
   object-language existential constructor or a covert double negation. *)
Theorem observation_entity_witnesses : forall G (p : wtm symbol (we :: G) wt), observable p ->
  forall rho sigma, observation_envs rho sigma ->
  (exists x, peval lex before (observation_term constants p) (pextend rho x)) <->
  (exists x, weval M p (wextend sigma x) = true).
Proof.
  intros G p H rho sigma R; split; intros [x A]; exists x;
    [apply (proj1 (observation_truth H (@observation_envs_extend G we rho sigma x x R eq_refl))) |
     apply (proj2 (observation_truth H (@observation_envs_extend G we rho sigma x x R eq_refl)))]; exact A.
Qed.

Theorem observation_finite_witnesses : forall (F : finite (windividuals M))
  G (p : wtm symbol (we :: G) wt), observable p ->
  forall rho sigma, observation_envs rho sigma ->
  (exists x, peval lex before (observation_term constants p) (pextend rho x)) <->
  existsb (fun x => weval M p (wextend sigma x)) (values F) = true.
Proof.
  intros F G p H rho sigma R; rewrite (observation_entity_witnesses H R), existsb_exists.
  split; intros [x A]; exists x; [split; [apply values_complete | exact A] | apply A].
Qed.
End Preservation.

(* Boundary results: a truth-reflection witness decides THAT proposition.
   Requiring such witnesses for every Prop implies excluded middle. *)
Lemma reflected_proposition_is_decidable (P : Prop) b :
  (P <-> b = true) -> P \/ ~ P.
Proof. destruct b; cbn; intuition discriminate. Qed.

Theorem total_truth_reflection_implies_classical_truth :
  (forall P : Prop, exists b : bool, P <-> b = true) -> ClassicalTruth.
Proof. intros R P; destruct (R P) as [b H]; exact (reflected_proposition_is_decidable H). Qed.

Lemma common_truth_value_gives_equivalence (P Q : Prop) b :
  (P <-> b = true) -> (Q <-> b = true) -> (P <-> Q).
Proof. intros P' Q'; rewrite P', Q'; reflexivity. Qed.

Theorem truth_equality_bridge_requires_propositional_extensionality :
  (forall P : Prop, exists b : bool, P <-> b = true) ->
  (forall (P Q : Prop) b c, (P <-> b = true) -> (Q <-> c = true) ->
    ((P = Q) <-> (b = c))) ->
  (forall P Q : Prop, (P <-> Q) -> P = Q).
Proof.
  intros Reflect Equal P Q I; destruct (Reflect P) as [b B], (Reflect Q) as [c C].
  apply (proj2 (Equal P Q b c B C)); destruct b, c; try reflexivity;
    exfalso; firstorder discriminate.
Qed.
