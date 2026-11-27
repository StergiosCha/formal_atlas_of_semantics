(** TTR_Stratified.v

    A model of the core of TTR: existence of a stratified system of types
    satisfying the witness conditions of

      Cooper, R. (2023). From Perception to Communication. OUP. Appendix A,
      pp. 398-410 (A2 basic types, A3 ptypes, A4 function types, A6 singleton
      types, A7 join types, A8 meet types, A10 Type^n and dependent function
      types, A11.1-A11.2 records, record types, dependent record types and
      manifest fields).

    Cooper states each construct as a condition on a given system ("a system
    has function types if ...").  The question answered here is whether one
    system satisfies all of these conditions at once.  The types and their
    witness sets are defined together: [ty c P] says that the object [c] is a
    type whose witnesses are exactly the objects satisfying [P].  Orders are
    built by recursion on [n], each order seeing the one below as [low].

    Recorded differences from the source (none silently repaired):
    D1  A11.1 requires every value in a record to be "of some type".  This is
        not imposed: a record is a finite labelled set with distinct labels.
    D2  Partial function types (A4), set and plurality types (A5), generalized
        joins and meets (A7, A8), modal systems (A9), merges and the rest of
        A11.3-A11.8, list and string types (A12, A13) are not modelled.
    D3  Functions are abstract names [Fn] with an application map [app].  A
        function type contains the functions of the right domain and range
        that exist in [Fn], not all set-theoretic functions.
    D4  Types are built with constructors, not as the labelled sets with
        reserved labels that the appendix specifies; records and record types
        are lists, so two orderings of the same fields are distinct objects
        (Theorem [order_independent] shows they have the same witnesses).
    D5  [A] and [Fp] do not vary with the order, and are not required to be
        disjoint from the types.
    D6  [Rec] is represented by the record type with no fields.

    No axioms, no [Admitted].  Standard library only. *)

From Coq Require Import List Arith Lia Permutation Setoid Morphisms.
Import ListNotations.

Definition Label := nat.
Definition Path := list Label.

Fixpoint lookup {X : Type} (fs : list (Label * X)) (l : Label) : option X :=
  match fs with
  | [] => None
  | (l', v) :: rest => if Nat.eqb l l' then Some v else lookup rest l
  end.

Section Model.

(** * Objects *)

Variable Fn : Type.

Inductive Val : Type :=
| VInd (i : nat)                       (* an object that is not a type *)
| VFn (f : Fn)                         (* a function *)
| VRec (fs : list (Label * Val))       (* a record, A11.1 *)
| TBasic (b : nat)                     (* A2 *)
| TPred (p : nat) (args : list Val)    (* A3: P(a1,...,an) *)
| TFun (T1 T2 : Val)                   (* A4: (T1 -> T2) *)
| TPi (T F : Val)                      (* A10: ((a : T) -> F(a)) *)
| TSing (T a : Val)                    (* A6: T_a *)
| TJoin (T1 T2 : Val)                  (* A7 *)
| TMeet (T1 T2 : Val)                  (* A8 *)
| TUniv (k : nat)                      (* A10: Type^k *)
| TRecUniv (k : nat)                   (* A11.2: RecType^k *)
| TERec                                (* A11.2: ERec *)
| TRecT (fs : list (Label * Fld))      (* A11.2: record types; [] is Rec *)
with Fld : Type :=
| FPlain (T : Val)                     (* <l, T> *)
| FDep (F : Val) (ps : list Path).     (* <l, <F, <pi1,...,pim>>> *)

(** * The model: A2, A3 *)

Variable app : Fn -> Val -> option Val.
Variable A : nat -> Val -> Prop.            (* witnesses of basic types *)
Variable arity : nat -> list Val -> Prop.   (* polymorphic arities, A3.1 *)
Variable Fp : nat -> list Val -> Val -> Prop. (* witnesses of ptypes *)

(** * Records, paths, application *)

Definition is_fn (g : Val) : Prop := exists f, g = VFn f.

Definition is_record (r : Val) : Prop :=
  exists fs, r = VRec fs /\ NoDup (map fst fs).

Definition field (r : Val) (l : Label) : option Val :=
  match r with VRec fs => lookup fs l | _ => None end.

Fixpoint resolve (r : Val) (p : Path) : option Val :=
  match p with
  | [] => None
  | l :: q =>
      match field r l with
      | Some v => match q with [] => Some v | _ => resolve v q end
      | None => None
      end
  end.

Definition vapp (g a : Val) : option Val :=
  match g with VFn f => app f a | _ => None end.

Fixpoint apps (g : Val) (args : list Val) : option Val :=
  match args with
  | [] => Some g
  | a :: rest => match vapp g a with Some h => apps h rest | None => None end
  end.

Definition eqv (P Q : Val -> Prop) : Prop := forall v, P v <-> Q v.

(** "g is a function whose domain is P" (A4, clause 2). *)
Definition dom_is (P : Val -> Prop) (g : Val) : Prop :=
  is_fn g /\ forall a, P a <-> vapp g a <> None.

Definition functional (R : Val -> (Val -> Prop) -> Prop) : Prop :=
  forall c P Q, R c P -> R c Q -> eqv P Q.

Definition fresh (l : Label) (R : list (Label * Fld)) : Prop :=
  ~ In l (map fst R).

Definition is_rectype (c : Val) : Prop := c = TERec \/ exists R, c = TRecT R.

Definition arrows (Ts : list Val) (U : Val) : Val := fold_right TFun U Ts.

Lemma eqv_refl : forall P, eqv P P.
Proof. intros P v; tauto. Qed.

Lemma dom_is_eqv : forall P Q g, eqv P Q -> (dom_is P g <-> dom_is Q g).
Proof.
  intros P Q g E. unfold dom_is. unfold eqv in E. setoid_rewrite E. tauto.
Qed.

Lemma Forall2_eqv_args : forall Ps' Ps (args : list Val),
  Forall2 eqv Ps' Ps -> Forall2 (fun (P : Val -> Prop) a => P a) Ps args ->
  Forall2 (fun (P : Val -> Prop) a => P a) Ps' args.
Proof.
  intros Ps' Ps args H. revert args.
  induction H as [| P' P Ps' Ps E _ IH]; intros args Ha; inversion Ha; subst.
  - constructor.
  - constructor; [apply E; assumption | apply IH; assumption].
Qed.

Ltac rw E := unfold eqv in E; repeat setoid_rewrite E.

(** * One order of the system, given the order below *)

Section Order.

Variable n : nat.
Variable low : Val -> (Val -> Prop) -> Prop.

(** [famok [P1;...;Pm] F]: F is a function of type (T1 -> ... -> (Tm -> Type^n)),
    where Pi is the witness set of Ti: its values are types of the order below. *)
Fixpoint famok (Ps : list (Val -> Prop)) (g : Val) : Prop :=
  match Ps with
  | [] => exists Q, low g Q
  | P :: Ps' => dom_is P g /\ forall a b, vapp g a = Some b -> famok Ps' b
  end.

Inductive ty : Val -> (Val -> Prop) -> Prop :=
(* A2.1 clause 4 *)
| ty_basic : forall b, ty (TBasic b) (A b)
(* A3.2 clauses 5, 8 *)
| ty_pred : forall p Ts Ps args,
    arity p Ts -> tyl Ts Ps ->
    Forall2 (fun (P : Val -> Prop) a => P a) Ps args ->
    ty (TPred p args) (Fp p args)
(* A4 clauses 1, 2 *)
| ty_fun : forall T1 T2 P1 P2,
    ty T1 P1 -> ty T2 P2 ->
    ty (TFun T1 T2)
       (fun g => dom_is P1 g /\ forall a b, vapp g a = Some b -> P2 b)
(* A10, dependent function types, clauses 1, 2 *)
| ty_pi : forall T P F,
    0 < n -> ty T P -> famok [P] F ->
    ty (TPi T F)
       (fun g => dom_is P g /\
                 forall a b, vapp g a = Some b ->
                   exists c Q, vapp F a = Some c /\ low c Q /\ Q b)
(* A6 clauses 1, 2 *)
| ty_sing : forall T P T' P' a,
    ty T P -> ty T' P' -> P' a ->
    ty (TSing T a) (fun b => P b /\ a = b)
(* A7 clauses 1, 2 *)
| ty_join : forall T1 T2 P1 P2,
    ty T1 P1 -> ty T2 P2 -> ty (TJoin T1 T2) (fun a => P1 a \/ P2 a)
(* A8 clauses 1, 2 *)
| ty_meet : forall T1 T2 P1 P2,
    ty T1 P1 -> ty T2 P2 -> ty (TMeet T1 T2) (fun a => P1 a /\ P2 a)
(* A10 clauses 4, 5 *)
| ty_univ_top : 0 < n -> ty (TUniv n) (fun c => exists P, low c P)
(* A10 clause 2, for the lower universes *)
| ty_univ_low : forall k P, k < n -> low (TUniv k) P -> ty (TUniv k) P
(* A11.2, intensional clauses 2, 3 *)
| ty_recuniv_top :
    0 < n -> ty (TRecUniv n) (fun c => is_rectype c /\ exists P, low c P)
| ty_recuniv_low : forall k P, k < n -> low (TRecUniv k) P -> ty (TRecUniv k) P
(* A11.2 clauses 3, 4 *)
| ty_erec : ty TERec (fun r => r = VRec [])
(* A11.2 clauses 1, 2 (without the typedness condition of A11.1: D1) *)
| ty_rec : ty (TRecT []) is_record
(* A11.2 clauses 5-8 *)
| ty_field_plain : forall l T PT R PR,
    fresh l R -> ty (TRecT R) PR -> ty T PT ->
    ty (TRecT ((l, FPlain T) :: R))
       (fun r => PR r /\ exists a, field r l = Some a /\ PT a)
(* A11.2, dependent record types, clauses 1, 2 *)
| ty_field_dep : forall l F ps Ts Ps R PR,
    0 < n -> fresh l R -> ty (TRecT R) PR ->
    tyl Ts Ps -> length ps = length Ts -> famok Ps F ->
    (forall r p, PR r -> In p ps -> resolve r p <> None) ->
    ty (TRecT ((l, FDep F ps) :: R))
       (fun r => PR r /\ exists a, field r l = Some a /\
          exists args c Q,
            Forall2 (fun p v => resolve r p = Some v) ps args /\
            apps F args = Some c /\ low c Q /\ Q a)
with tyl : list Val -> list (Val -> Prop) -> Prop :=
| tyl_nil : tyl [] []
| tyl_cons : forall T P Ts Ps, ty T P -> tyl Ts Ps -> tyl (T :: Ts) (P :: Ps).

Scheme ty_mut := Minimality for ty Sort Prop
  with tyl_mut := Minimality for tyl Sort Prop.
Combined Scheme ty_tyl_mutind from ty_mut, tyl_mut.

Lemma tyl_length : forall Ts Ps, tyl Ts Ps -> length Ts = length Ps.
Proof. induction 1; simpl; congruence. Qed.

Lemma famok_apps : forall Ps F args c,
  famok Ps F -> length args = length Ps -> apps F args = Some c ->
  Forall2 (fun (P : Val -> Prop) a => P a) Ps args /\ exists Q, low c Q.
Proof.
  induction Ps as [| P Ps IH]; intros F args c HF Hlen Happ;
    destruct args as [| a args]; simpl in *; try discriminate.
  - inversion Happ; subst. split; [constructor | exact HF].
  - destruct HF as [Hd Hr]. destruct (vapp F a) as [h |] eqn:E; try discriminate.
    destruct (IH h args c (Hr _ _ E)) as [Hall HQ]; [lia | exact Happ |].
    split; [| exact HQ]. constructor; [| exact Hall].
    apply (proj2 Hd). rewrite E. discriminate.
Qed.

Ltac use_IH :=
  repeat match goal with
  | IH : forall Q, ty ?T Q -> eqv ?P Q, H : ty ?T ?Q' |- _ =>
      lazymatch Q' with
      | P => fail
      | _ => lazymatch goal with
             | _ : eqv P Q' |- _ => fail
             | _ => pose proof (IH _ H)
             end
      end
  end.

Ltac rew_eqv :=
  unfold dom_is;
  repeat match goal with
  | E : eqv _ _ |- _ => unfold eqv in E; repeat setoid_rewrite E; clear E
  end.

(** Each type of this order has one witness set, if that holds below. *)
Lemma ty_functional : functional low -> functional ty.
Proof.
  intros Hlow c P Q H. revert Q.
  induction H; intros Q0 HQ; inversion HQ; subst; clear HQ;
    try (exfalso; lia); use_IH; try (eapply Hlow; eassumption);
    intro v; rew_eqv; reflexivity.
Qed.

End Order.

(** * From one order to the next *)

Section Step.

Variable n : nat.
Variable low : Val -> (Val -> Prop) -> Prop.
Local Notation L := (ty n low).
Hypothesis Hfun : functional L.
Hypothesis Hincl : forall c P, low c P -> exists P', L c P' /\ eqv P' P.

Lemma lift_wit : forall c b, (exists Q, low c Q) ->
  ((exists Q, L c Q /\ Q b) <-> (exists Q, low c Q /\ Q b)).
Proof.
  intros c b [Q0 H0]. destruct (Hincl _ _ H0) as [Q0' [H0' E0]]. split.
  - intros [Q [HQ Hb]]. exists Q0. split; [exact H0 |].
    apply E0. apply (Hfun _ _ _ HQ H0'). exact Hb.
  - intros [Q [HQ Hb]]. destruct (Hincl _ _ HQ) as [Q' [HQ' E]].
    exists Q'. split; [exact HQ' | apply E; exact Hb].
Qed.

Lemma famok_lift : forall Ps' Ps, Forall2 eqv Ps' Ps ->
  forall F, famok low Ps F -> famok L Ps' F.
Proof.
  induction 1 as [| P' P Ps' Ps E _ IH]; intros F HF; simpl in *.
  - destruct HF as [Q HQ]. destruct (Hincl _ _ HQ) as [Q' [HQ' _]].
    exists Q'; exact HQ'.
  - destruct HF as [Hd Hr]. split.
    + apply (dom_is_eqv P' P F E). exact Hd.
    + intros a b Hab. apply IH. eapply Hr; eauto.
Qed.

Lemma ty_step_mut :
  (forall c P, ty n low c P -> exists P', ty (S n) L c P' /\ eqv P' P) /\
  (forall Ts Ps, tyl n low Ts Ps ->
     exists Ps', tyl (S n) L Ts Ps' /\ Forall2 eqv Ps' Ps).
Proof.
  apply (ty_tyl_mutind n low
    (fun c P => exists P', ty (S n) L c P' /\ eqv P' P)
    (fun Ts Ps => exists Ps', tyl (S n) L Ts Ps' /\ Forall2 eqv Ps' Ps)).
  - (* basic *)
    intros b. exists (A b). split; [constructor | apply eqv_refl].
  - (* pred *)
    intros p Ts Ps args Har _ [Ps' [Htyl' EPs]] Hargs.
    exists (Fp p args). split; [| apply eqv_refl].
    eapply ty_pred; eauto. eapply Forall2_eqv_args; eauto.
  - (* fun *)
    intros T1 T2 P1 P2 _ [P1' [H1 E1]] _ [P2' [H2 E2]].
    exists (fun g => dom_is P1' g /\ forall a b, vapp g a = Some b -> P2' b).
    split; [constructor; assumption |].
    intro v. unfold dom_is. rw E1. rw E2. reflexivity.
  - (* pi *)
    intros T P F Hn _ [P' [HT E]] Hfam. simpl in Hfam. destruct Hfam as [Hd Hr].
    exists (fun g => dom_is P' g /\
              forall a b, vapp g a = Some b ->
                exists c Q, vapp F a = Some c /\ L c Q /\ Q b).
    split.
    + apply ty_pi; [lia | exact HT |]. simpl. split.
      * apply (dom_is_eqv P' P F E). exact Hd.
      * intros a b Hab. destruct (Hr a b Hab) as [Q HQ].
        destruct (Hincl _ _ HQ) as [Q' [HQ' _]]. exists Q'; exact HQ'.
    + intro v. split; intros [Hdv Hrv]; (split; [apply (dom_is_eqv P' P v E); exact Hdv |]);
        intros a b Hab; destruct (Hrv a b Hab) as (c & Q & Hc & HQ & Hb).
      * destruct (proj1 (lift_wit c b (Hr a c Hc)) (ex_intro _ Q (conj HQ Hb)))
          as [Q1 [HQ1 Hb1]]. exists c, Q1; auto.
      * destruct (proj2 (lift_wit c b (Hr a c Hc)) (ex_intro _ Q (conj HQ Hb)))
          as [Q1 [HQ1 Hb1]]. exists c, Q1; auto.
  - (* sing *)
    intros T P T' P' a _ [Q [HT E]] _ [Q' [HT' E']] Ha.
    exists (fun b => Q b /\ a = b). split.
    + eapply ty_sing; eauto. apply E'; exact Ha.
    + intro v. rw E. reflexivity.
  - (* join *)
    intros T1 T2 P1 P2 _ [P1' [H1 E1]] _ [P2' [H2 E2]].
    exists (fun a => P1' a \/ P2' a). split; [constructor; assumption |].
    intro v. rw E1. rw E2. reflexivity.
  - (* meet *)
    intros T1 T2 P1 P2 _ [P1' [H1 E1]] _ [P2' [H2 E2]].
    exists (fun a => P1' a /\ P2' a). split; [constructor; assumption |].
    intro v. rw E1. rw E2. reflexivity.
  - (* univ_top *)
    intros Hn. exists (fun c => exists P, low c P). split; [| apply eqv_refl].
    apply ty_univ_low; [lia |]. apply ty_univ_top; exact Hn.
  - (* univ_low *)
    intros k P Hk Hl. exists P. split; [| apply eqv_refl].
    apply ty_univ_low; [lia |]. apply ty_univ_low; assumption.
  - (* recuniv_top *)
    intros Hn. exists (fun c => is_rectype c /\ exists P, low c P).
    split; [| apply eqv_refl].
    apply ty_recuniv_low; [lia |]. apply ty_recuniv_top; exact Hn.
  - (* recuniv_low *)
    intros k P Hk Hl. exists P. split; [| apply eqv_refl].
    apply ty_recuniv_low; [lia |]. apply ty_recuniv_low; assumption.
  - (* erec *)
    eexists. split; [apply ty_erec | apply eqv_refl].
  - (* rec *)
    eexists. split; [apply ty_rec | apply eqv_refl].
  - (* field_plain *)
    intros l T PT R PR Hfr _ [PR' [HR ER]] _ [PT' [HT ET]].
    exists (fun r => PR' r /\ exists a, field r l = Some a /\ PT' a).
    split; [constructor; assumption |].
    intro v. rw ER. rw ET. reflexivity.
  - (* field_dep *)
    intros l F ps Ts Ps R PR Hn Hfr _ [PR' [HR ER]] Htyl [Ps' [Htyl' EPs]]
           Hlen Hfam Hpaths.
    exists (fun r => PR' r /\ exists a, field r l = Some a /\
              exists args c Q,
                Forall2 (fun p v => resolve r p = Some v) ps args /\
                apps F args = Some c /\ L c Q /\ Q a).
    split.
    + eapply ty_field_dep with (Ts := Ts) (Ps := Ps'); eauto;
        try lia; try (eapply famok_lift; eassumption);
        try (intros r p Hr; apply Hpaths; apply ER; exact Hr).
    + intro v.
      assert (Hex : forall args c,
                Forall2 (fun p w => resolve v p = Some w) ps args ->
                apps F args = Some c -> exists Q, low c Q).
      { intros args c Hres Happ.
        apply (famok_apps low Ps F args c Hfam); [| exact Happ].
        rewrite <- (Forall2_length Hres), Hlen. apply (tyl_length _ _ _ _ Htyl). }
      split; intros [HPR (a & Hf & args & c & Q & Hres & Happ & HQ & Ha)];
        (split; [apply ER; exact HPR |]); exists a; (split; [exact Hf |]).
      * destruct (proj1 (lift_wit c a (Hex args c Hres Happ))
                    (ex_intro _ Q (conj HQ Ha))) as [Q1 [HQ1 Ha1]].
        exists args, c, Q1; auto.
      * destruct (proj2 (lift_wit c a (Hex args c Hres Happ))
                    (ex_intro _ Q (conj HQ Ha))) as [Q1 [HQ1 Ha1]].
        exists args, c, Q1; auto.
  - (* tyl_nil *)
    exists []. split; constructor.
  - (* tyl_cons *)
    intros T P Ts Ps _ [P' [HT E]] _ [Ps' [HTs EPs]].
    exists (P' :: Ps'). split; constructor; assumption.
Qed.

End Step.

(** * The stratified system (A10) *)

Definition Empty : Val -> (Val -> Prop) -> Prop := fun _ _ => False.

Fixpoint TY (n : nat) : Val -> (Val -> Prop) -> Prop :=
  match n with
  | 0 => ty 0 Empty
  | S m => ty (S m) (TY m)
  end.

Definition lowof (n : nat) : Val -> (Val -> Prop) -> Prop :=
  match n with 0 => Empty | S m => TY m end.

Lemma TY_unfold : forall n, TY n = ty n (lowof n).
Proof. destruct n; reflexivity. Qed.

(** a :_n T, and T in Type^n. *)
Definition wit (n : nat) (T a : Val) : Prop := exists P, TY n T P /\ P a.
Definition istype (n : nat) (T : Val) : Prop := exists P, TY n T P.

(** ** Statement 1.  Every type of every order has exactly one witness set. *)
Theorem one_witness_set : forall n, functional (TY n).
Proof.
  induction n; simpl; apply ty_functional.
  - intros c P Q [].
  - exact IHn.
Qed.

Lemma TY_step : forall n c P, TY n c P -> exists P', TY (S n) c P' /\ eqv P' P.
Proof.
  induction n; intros c P H.
  - apply (proj1 (ty_step_mut 0 Empty (one_witness_set 0)
                    (fun c P (H : Empty c P) => match H with end))).
    exact H.
  - apply (proj1 (ty_step_mut (S n) (TY n) (one_witness_set (S n)) IHn)).
    exact H.
Qed.

Lemma wit_ext : forall n T P, TY n T P -> forall a, wit n T a <-> P a.
Proof.
  intros n T P H a. split.
  - intros [Q [HQ Ha]]. apply (one_witness_set n _ _ _ H HQ). exact Ha.
  - intro Ha. exists P; auto.
Qed.

Lemma wit_up : forall n T a, wit n T a -> wit (S n) T a.
Proof.
  intros n T a [P [H Ha]]. destruct (TY_step n T P H) as [P' [H' E]].
  exists P'. split; [exact H' | apply E; exact Ha].
Qed.

Lemma istype_up : forall n T, istype n T -> istype (S n) T.
Proof.
  intros n T [P H]. destruct (TY_step n T P H) as [P' [H' _]]. exists P'; exact H'.
Qed.

Lemma wit_down : forall n T a, istype n T -> wit (S n) T a -> wit n T a.
Proof.
  intros n T a [P H] Hw. destruct (TY_step n T P H) as [P' [H' E]].
  exists P. split; [exact H |]. apply E. apply (wit_ext _ _ _ H'). exact Hw.
Qed.

Lemma tyl_of_wits : forall n Ts args, Forall2 (wit n) Ts args ->
  exists Ps, tyl n (lowof n) Ts Ps /\ Forall2 (fun (P : Val -> Prop) a => P a) Ps args.
Proof.
  induction 1 as [| T a Ts args [P [H Ha]] _ [Ps [Ht Hall]]].
  - exists []. split; constructor.
  - exists (P :: Ps). split; constructor; auto. rewrite <- TY_unfold. exact H.
Qed.

Lemma wits_of_tyl : forall n Ts Ps, tyl n (lowof n) Ts Ps ->
  forall args, Forall2 (fun (P : Val -> Prop) a => P a) Ps args -> Forall2 (wit n) Ts args.
Proof.
  induction 1 as [| T P Ts Ps H _ IH]; intros args Ha; inversion Ha; subst.
  - constructor.
  - constructor; [| apply IH; assumption].
    exists P. split; [rewrite TY_unfold; exact H | assumption].
Qed.

Lemma tyl_of_types : forall n Ts, Forall (istype n) Ts -> exists Ps, tyl n (lowof n) Ts Ps.
Proof.
  induction 1 as [| T Ts [P H] _ [Ps Ht]].
  - exists []. constructor.
  - exists (P :: Ps). constructor; [rewrite <- TY_unfold; exact H | exact Ht].
Qed.

(** ** Statement 2.  The clauses of A2, A3, A4, A6, A7 and A8 hold. *)

Lemma A2_basic_types : forall n b,
  istype n (TBasic b) /\ forall a, wit n (TBasic b) a <-> A b a.
Proof.
  intros n b.
  assert (H : TY n (TBasic b) (A b)) by (rewrite TY_unfold; constructor).
  split; [eexists; exact H | exact (wit_ext _ _ _ H)].
Qed.

Lemma A3_ptypes : forall n p args,
  (istype n (TPred p args) <->
     exists Ts, arity p Ts /\ Forall2 (wit n) Ts args) /\
  (istype n (TPred p args) -> forall a, wit n (TPred p args) a <-> Fp p args a).
Proof.
  intros n p args. split; [split |].
  - intros [P H]. rewrite TY_unfold in H. inversion H; subst.
    exists Ts. split; [assumption |]. eapply wits_of_tyl; eauto.
  - intros [Ts [Har Hw]]. destruct (tyl_of_wits n Ts args Hw) as [Ps [Ht Ha]].
    exists (Fp p args). rewrite TY_unfold. eapply ty_pred; eauto.
  - intros [P H] a. rewrite (wit_ext _ _ _ H).
    rewrite TY_unfold in H. inversion H; subst. reflexivity.
Qed.

Lemma A4_function_types : forall n T1 T2, istype n T1 -> istype n T2 ->
  istype n (TFun T1 T2) /\
  forall g, wit n (TFun T1 T2) g <->
    (is_fn g /\ (forall a, wit n T1 a <-> vapp g a <> None) /\
     (forall a b, vapp g a = Some b -> wit n T2 b)).
Proof.
  intros n T1 T2 [P1 H1] [P2 H2].
  assert (H : TY n (TFun T1 T2)
                (fun g => dom_is P1 g /\ forall a b, vapp g a = Some b -> P2 b)).
  { rewrite TY_unfold in *. constructor; assumption. }
  split; [eexists; exact H |]. intro g. rewrite (wit_ext _ _ _ H). unfold dom_is.
  setoid_rewrite (wit_ext _ _ _ H1). setoid_rewrite (wit_ext _ _ _ H2). tauto.
Qed.

Lemma A6_singleton_types : forall n T T' a, istype n T -> wit n T' a ->
  istype n (TSing T a) /\
  forall b, wit n (TSing T a) b <-> (wit n T b /\ a = b).
Proof.
  intros n T T' a [P H] [P' [H' Ha]].
  assert (HS : TY n (TSing T a) (fun b => P b /\ a = b)).
  { rewrite TY_unfold in *. eapply ty_sing; eauto. }
  split; [eexists; exact HS |]. intro b. rewrite (wit_ext _ _ _ HS).
  rewrite (wit_ext _ _ _ H). reflexivity.
Qed.

Lemma A7_A8_join_meet_types : forall n T1 T2, istype n T1 -> istype n T2 ->
  (istype n (TJoin T1 T2) /\
   forall a, wit n (TJoin T1 T2) a <-> (wit n T1 a \/ wit n T2 a)) /\
  (istype n (TMeet T1 T2) /\
   forall a, wit n (TMeet T1 T2) a <-> (wit n T1 a /\ wit n T2 a)).
Proof.
  intros n T1 T2 [P1 H1] [P2 H2].
  assert (HJ : TY n (TJoin T1 T2) (fun a => P1 a \/ P2 a))
    by (rewrite TY_unfold in *; constructor; assumption).
  assert (HM : TY n (TMeet T1 T2) (fun a => P1 a /\ P2 a))
    by (rewrite TY_unfold in *; constructor; assumption).
  split; (split; [eexists; eassumption |]); intro a.
  - rewrite (wit_ext _ _ _ HJ), (wit_ext _ _ _ H1), (wit_ext _ _ _ H2). reflexivity.
  - rewrite (wit_ext _ _ _ HM), (wit_ext _ _ _ H1), (wit_ext _ _ _ H2). reflexivity.
Qed.

(** ** Statement 3.  Stratification (A10): cumulativity, Type^n in Type^n,
       its witnesses are the types of the order below, and no Type^k is a
       witness of itself. *)

Lemma univ_level : forall m k, istype m (TUniv k) -> 0 < k <= m.
Proof.
  induction m; intros k [P H]; simpl in H; inversion H; subst; try lia.
  assert (0 < k <= m) by (apply IHm; eexists; eassumption). lia.
Qed.

Lemma univ_clause : forall n,
  TY (S n) (TUniv (S n)) (fun c => exists P, TY n c P).
Proof. intro n. simpl. apply ty_univ_top. lia. Qed.

Theorem A10_stratification : forall n,
  (forall T, istype n T -> istype (S n) T) /\
  (forall T a, wit n T a -> wit (S n) T a) /\
  (forall T a, istype n T -> wit (S n) T a -> wit n T a) /\
  istype (S n) (TUniv (S n)) /\
  (forall T, wit (S n) (TUniv (S n)) T <-> istype n T) /\
  ~ wit n (TUniv n) (TUniv n).
Proof.
  intro n. repeat split.
  - apply istype_up.
  - apply wit_up.
  - apply wit_down.
  - eexists; apply univ_clause.
  - apply (wit_ext _ _ _ (univ_clause n)).
  - apply (wit_ext _ _ _ (univ_clause n)).
  - destruct n as [| m]; intros Hw.
    + destruct Hw as [P [H _]].
      assert (0 < 0 <= 0) by (apply univ_level; eexists; exact H). lia.
    + apply (wit_ext _ _ _ (univ_clause m)) in Hw.
      assert (0 < S m <= m) by (apply univ_level; exact Hw). lia.
Qed.

(** ** Statement 4.  Dependent function types (A10). *)
Theorem A10_dependent_function_types : forall n T F,
  istype (S n) T -> wit (S n) (TFun T (TUniv (S n))) F ->
  istype (S n) (TPi T F) /\
  forall g, wit (S n) (TPi T F) g <->
    (is_fn g /\ (forall a, wit (S n) T a <-> vapp g a <> None) /\
     forall a b, vapp g a = Some b ->
       exists c, vapp F a = Some c /\ wit (S n) c b).
Proof.
  intros n T F [P HT] HF.
  assert (HFT : TY (S n) (TFun T (TUniv (S n)))
                  (fun g => dom_is P g /\
                            forall a b, vapp g a = Some b -> exists Q, TY n b Q)).
  { simpl. apply ty_fun; [exact HT | apply (univ_clause n)]. }
  apply (wit_ext _ _ _ HFT) in HF. destruct HF as [HFd HFr].
  assert (H : TY (S n) (TPi T F)
                (fun g => dom_is P g /\
                          forall a b, vapp g a = Some b ->
                            exists c Q, vapp F a = Some c /\ TY n c Q /\ Q b)).
  { simpl. apply ty_pi; [lia | exact HT |]. simpl. split; assumption. }
  split; [eexists; exact H |]. intro g. rewrite (wit_ext _ _ _ H). unfold dom_is.
  setoid_rewrite (wit_ext _ _ _ HT). split.
  - intros [[Hfn Hd] Hr]. split; [exact Hfn |]. split; [exact Hd |].
    intros a b Hab. destruct (Hr a b Hab) as (c & Q & Hc & HQ & Hb).
    exists c. split; [exact Hc |]. apply wit_up. exists Q; auto.
  - intros (Hfn & Hd & Hr). split; [split; assumption |].
    intros a b Hab. destruct (Hr a b Hab) as (c & Hc & Hw).
    destruct (HFr a c Hc) as [Q0 HQ0].
    apply wit_down in Hw; [| exists Q0; exact HQ0].
    destruct Hw as (Q & HQ & Hb). exists c, Q; auto.
Qed.

(** ** Statement 5.  Records and record types (A11.2). *)
Theorem A11_record_types : forall n,
  (istype n (TRecT []) /\ forall r, wit n (TRecT []) r <-> is_record r) /\
  (istype n TERec /\ forall r, wit n TERec r <-> r = VRec []) /\
  (forall l T R, fresh l R -> istype n (TRecT R) -> istype n T ->
     istype n (TRecT ((l, FPlain T) :: R)) /\
     forall r, wit n (TRecT ((l, FPlain T) :: R)) r <->
       (wit n (TRecT R) r /\ exists a, field r l = Some a /\ wit n T a)) /\
  (istype (S n) (TRecUniv (S n)) /\
   forall T, wit (S n) (TRecUniv (S n)) T <-> (is_rectype T /\ istype n T)).
Proof.
  intro n. split; [| split; [| split]].
  - assert (H : TY n (TRecT []) is_record) by (rewrite TY_unfold; constructor).
    split; [eexists; exact H | exact (wit_ext _ _ _ H)].
  - assert (H : TY n TERec (fun r => r = VRec [])) by (rewrite TY_unfold; constructor).
    split; [eexists; exact H | exact (wit_ext _ _ _ H)].
  - intros l T R Hfr [PR HR] [PT HT].
    assert (H : TY n (TRecT ((l, FPlain T) :: R))
                  (fun r => PR r /\ exists a, field r l = Some a /\ PT a)).
    { rewrite TY_unfold in *. constructor; assumption. }
    split; [eexists; exact H |]. intro r. rewrite (wit_ext _ _ _ H).
    rewrite (wit_ext _ _ _ HR). setoid_rewrite (wit_ext _ _ _ HT). reflexivity.
  - assert (H : TY (S n) (TRecUniv (S n))
                  (fun c => is_rectype c /\ exists P, TY n c P)).
    { simpl. apply ty_recuniv_top. lia. }
    split; [eexists; exact H | exact (wit_ext _ _ _ H)].
Qed.

Lemma ty_arrows : forall n Ts Ps, tyl (S n) (TY n) Ts Ps ->
  ty (S n) (TY n) (arrows Ts (TUniv (S n))) (famok (TY n) Ps).
Proof.
  induction 1 as [| T P Ts Ps HT _ IH]; simpl.
  - apply ty_univ_top. lia.
  - apply ty_fun; assumption.
Qed.

Lemma dep_ext : forall n F ps Ts Ps r,
  tyl (S n) (TY n) Ts Ps -> length ps = length Ts -> famok (TY n) Ps F ->
  forall a,
  (exists args c Q, Forall2 (fun p v => resolve r p = Some v) ps args /\
                    apps F args = Some c /\ TY n c Q /\ Q a) <->
  (exists args c, Forall2 (fun p v => resolve r p = Some v) ps args /\
                  Forall2 (wit (S n)) Ts args /\
                  apps F args = Some c /\ wit (S n) c a).
Proof.
  intros n F ps Ts Ps r Htyl Hlen HF a.
  assert (Hex : forall args c,
            Forall2 (fun p w => resolve r p = Some w) ps args ->
            apps F args = Some c ->
            Forall2 (fun (P : Val -> Prop) a => P a) Ps args /\ exists Q, TY n c Q).
  { intros args c Hres Happ. apply (famok_apps (TY n) Ps F args c HF); [| exact Happ].
    rewrite <- (Forall2_length Hres), Hlen. apply (tyl_length _ _ _ _ Htyl). }
  split.
  - intros (args & c & Q & Hres & Happ & HQ & Ha).
    destruct (Hex args c Hres Happ) as [Hall _].
    exists args, c. repeat split; auto.
    + apply (wits_of_tyl (S n) Ts Ps Htyl). exact Hall.
    + apply wit_up. exists Q; auto.
  - intros (args & c & Hres & _ & Happ & Hw).
    destruct (Hex args c Hres Happ) as [_ [Q0 HQ0]].
    apply wit_down in Hw; [| exists Q0; exact HQ0].
    destruct Hw as (Q & HQ & Ha). exists args, c, Q; auto.
Qed.

(** ** Statement 6.  Dependent record types (A11.2, clauses 1 and 2 of the
       dependent case): a field whose type is F applied to the values on the
       paths pi1,...,pim of the same record. *)
Theorem A11_dependent_record_types : forall n l F ps Ts R,
  fresh l R -> istype (S n) (TRecT R) ->
  Forall (istype (S n)) Ts -> length ps = length Ts ->
  (forall r p, wit (S n) (TRecT R) r -> In p ps -> resolve r p <> None) ->
  wit (S n) (arrows Ts (TUniv (S n))) F ->
  istype (S n) (TRecT ((l, FDep F ps) :: R)) /\
  forall r, wit (S n) (TRecT ((l, FDep F ps) :: R)) r <->
    (wit (S n) (TRecT R) r /\
     exists a, field r l = Some a /\
       exists args c,
         Forall2 (fun p v => resolve r p = Some v) ps args /\
         Forall2 (wit (S n)) Ts args /\
         apps F args = Some c /\ wit (S n) c a).
Proof.
  intros n l F ps Ts R Hfr [PR HR] HTs Hlen Hpaths HF.
  destruct (tyl_of_types (S n) Ts HTs) as [Ps Htyl]. simpl in Htyl.
  apply (wit_ext (S n) _ _ (ty_arrows n Ts Ps Htyl)) in HF.
  assert (H : TY (S n) (TRecT ((l, FDep F ps) :: R))
                (fun r => PR r /\ exists a, field r l = Some a /\
                   exists args c Q,
                     Forall2 (fun p v => resolve r p = Some v) ps args /\
                     apps F args = Some c /\ TY n c Q /\ Q a)).
  { simpl. eapply ty_field_dep with (Ts := Ts) (Ps := Ps); eauto.
    - lia.
    - intros r p Hr. apply Hpaths. exists PR; auto. }
  split; [eexists; exact H |]. intro r. rewrite (wit_ext _ _ _ H).
  rewrite (wit_ext _ _ _ HR).
  setoid_rewrite (dep_ext n F ps Ts Ps r Htyl Hlen HF). reflexivity.
Qed.

(** ** Statement 7.  Field-wise witness condition, and independence of the
       order in which the fields of a record type were added. *)

Definition field_ok (n : nat) (r : Val) (lf : Label * Fld) : Prop :=
  match lf with
  | (l, FPlain T) => exists a, field r l = Some a /\ wit n T a
  | (l, FDep F ps) =>
      exists a, field r l = Some a /\
        exists args c, Forall2 (fun p v => resolve r p = Some v) ps args /\
                       apps F args = Some c /\ wit n c a
  end.

Theorem record_type_witness : forall n R, istype n (TRecT R) ->
  forall r, wit n (TRecT R) r <-> (is_record r /\ Forall (field_ok n r) R).
Proof.
  intros n R. induction R as [| [l fld] R IH]; intros [P H] r;
    rewrite (wit_ext _ _ _ H); rewrite TY_unfold in H; inversion H; subst.
  - split; [intro Hr; split; [exact Hr | constructor] | tauto].
  - (* plain field *)
    match goal with
    | HR : ty n (lowof n) (TRecT R) ?PR, HT : ty n (lowof n) ?T ?PT |- _ =>
        rewrite <- TY_unfold in HR, HT;
        rewrite <- (wit_ext _ _ _ HR);
        rewrite (IH (ex_intro _ _ HR) r);
        setoid_rewrite <- (wit_ext _ _ _ HT)
    end.
    split.
    + intros [[Hrec Hall] Hf]. split; [exact Hrec |]. constructor; assumption.
    + intros [Hrec Hall]. inversion Hall; subst. split; [split |]; assumption.
  - (* dependent field *)
    destruct n as [| m]; [lia |]. simpl lowof in *.
    match goal with
    | HR : ty (S m) (TY m) (TRecT R) ?PR, Htyl : tyl (S m) (TY m) ?Ts ?Ps,
      Hlen : length ?ps = length ?Ts, HF : famok (TY m) ?Ps ?F |- _ =>
        change (TY (S m) (TRecT R) PR) in HR;
        rewrite <- (wit_ext _ _ _ HR);
        rewrite (IH (ex_intro _ _ HR) r);
        setoid_rewrite (dep_ext m F ps Ts Ps r Htyl Hlen HF)
    end.
    split.
    + intros [[Hrec Hall] (a & Hf & args & c & Hres & _ & Happ & Hw)].
      split; [exact Hrec |]. constructor; [| exact Hall].
      simpl. exists a. split; [exact Hf |]. exists args, c; auto.
    + intros [Hrec Hall]. inversion Hall as [| x xs Hx Hxs]; subst.
      split; [split; assumption |].
      simpl in Hx. destruct Hx as (a & Hf & args & c & Hres & Happ & Hw).
      exists a. split; [exact Hf |]. exists args, c. repeat split; auto.
      match goal with
      | Htyl : tyl (S m) (TY m) ?Ts ?Ps, Hlen : length ?ps = length ?Ts,
        HF : famok (TY m) ?Ps ?F |- _ =>
          apply (wits_of_tyl (S m) Ts Ps Htyl);
          apply (famok_apps (TY m) Ps F args c HF); [| exact Happ];
          rewrite <- (Forall2_length Hres), Hlen; apply (tyl_length _ _ _ _ Htyl)
      end.
Qed.

Corollary order_independent : forall n R R',
  Permutation R R' -> istype n (TRecT R) -> istype n (TRecT R') ->
  forall r, wit n (TRecT R) r <-> wit n (TRecT R') r.
Proof.
  intros n R R' Hp H H' r.
  rewrite (record_type_witness n R H r), (record_type_witness n R' H' r).
  split; intros [Hrec Hall]; (split; [exact Hrec |]).
  - eapply Permutation_Forall; eauto.
  - eapply Permutation_Forall; [apply Permutation_sym |]; eauto.
Qed.

(** ** Statement 8.  Manifest fields (A11.2: [l=a : T] is the field <l, T_a>),
       and consistency: an empty type exists at every order, and a function
       type from an inhabited type into it has no witness. *)

Theorem manifest_field : forall n l T a R,
  fresh l R -> istype n (TRecT R) -> wit n T a ->
  istype n (TRecT ((l, FPlain (TSing T a)) :: R)) /\
  forall r, wit n (TRecT ((l, FPlain (TSing T a)) :: R)) r <->
    (wit n (TRecT R) r /\ field r l = Some a).
Proof.
  intros n l T a R Hfr HR Ha.
  assert (HT : istype n T) by (destruct Ha as [P [H _]]; exists P; exact H).
  destruct (A6_singleton_types n T T a HT Ha) as [HS HSw].
  destruct (A11_record_types n) as (_ & _ & Hplain & _).
  destruct (Hplain l (TSing T a) R Hfr HR HS) as [Hty Hw].
  split; [exact Hty |]. intro r. rewrite Hw. split; intros [HRr X]; (split; [exact HRr |]).
  - destruct X as (b & Hf & Hb). apply HSw in Hb. destruct Hb as [_ <-]. exact Hf.
  - exists a. split; [exact X |]. apply HSw. split; [exact Ha | reflexivity].
Qed.

Theorem consistency : forall n e, (forall v, ~ A e v) ->
  (istype n (TBasic e) /\ forall v, ~ wit n (TBasic e) v) /\
  (forall T a, wit n T a -> forall g, ~ wit n (TFun T (TBasic e)) g) /\
  (forall T f, istype n T -> (forall a, ~ wit n T a) ->
     (forall a, app f a = None) -> wit n (TFun T (TBasic e)) (VFn f)).
Proof.
  intros n e He. destruct (A2_basic_types n e) as [HE HEw].
  assert (Hempty : forall v, ~ wit n (TBasic e) v).
  { intros v Hv. apply (He v). apply HEw. exact Hv. }
  split; [split; assumption |]. split.
  - intros T a Ha g Hg.
    assert (HT : istype n T) by (destruct Ha as [P [H _]]; exists P; exact H).
    apply (proj2 (A4_function_types n T (TBasic e) HT HE)) in Hg.
    destruct Hg as (_ & Hd & Hr). apply Hd in Ha.
    destruct (vapp g a) as [b |] eqn:E; [| congruence].
    exact (Hempty b (Hr a b E)).
  - intros T f HT Hno Hf.
    apply (proj2 (A4_function_types n T (TBasic e) HT HE)). split; [| split].
    + exists f; reflexivity.
    + intro a. simpl. rewrite Hf. split; [intro Ha; destruct (Hno a Ha) | congruence].
    + intros a b. simpl. rewrite Hf. discriminate.
Qed.

End Model.

Print Assumptions one_witness_set.
Print Assumptions A2_basic_types.
Print Assumptions A3_ptypes.
Print Assumptions A4_function_types.
Print Assumptions A6_singleton_types.
Print Assumptions A7_A8_join_meet_types.
Print Assumptions A10_stratification.
Print Assumptions A10_dependent_function_types.
Print Assumptions A11_record_types.
Print Assumptions A11_dependent_record_types.
Print Assumptions record_type_witness.
Print Assumptions order_independent.
Print Assumptions manifest_field.
Print Assumptions consistency.

(** * Non-vacuity check.  A concrete system, to show that the conditions above
      can be met: the record type [x : Ind, c : dog(x)], a manifest field, a
      function type with a witness, and a function type with none. *)

Arguments VInd {Fn} i.
Arguments VFn {Fn} f.
Arguments VRec {Fn} fs.
Arguments TBasic {Fn} b.
Arguments TPred {Fn} p args.
Arguments TFun {Fn} T1 T2.
Arguments TSing {Fn} T a.
Arguments TUniv {Fn} k.
Arguments TRecT {Fn} fs.
Arguments FPlain {Fn} T.
Arguments FDep {Fn} F ps.
Arguments is_record {Fn} r.
Arguments field {Fn} r l.

Module Example.

Inductive fn := f_dog | f_id.   (* \v:Ind. dog(v)  and  \v:Ind. v *)
Definition V := Val fn.
Definition Ind : V := TBasic 0.
Definition Nothing : V := TBasic 1.

Definition app (f : fn) (a : V) : option V :=
  match a with
  | VInd i => match f with
              | f_dog => Some (TPred 0 [VInd i])
              | f_id => Some (VInd i)
              end
  | _ => None
  end.
Definition A (b : nat) (v : V) : Prop := b = 0 /\ exists i, v = VInd i.
Definition arity (p : nat) (Ts : list V) : Prop := p = 0 /\ Ts = [Ind].
(* The only dog is individual 0; situation 100 shows it. *)
Definition Fp (p : nat) (args : list V) (v : V) : Prop :=
  p = 0 /\ args = [VInd 0] /\ v = VInd 100.

Local Notation witE := (wit fn app A arity Fp).
Local Notation istypeE := (istype fn app A arity Fp).

Lemma ind_type : forall n, istypeE n Ind.
Proof. intro n. apply (A2_basic_types fn app A arity Fp n 0). Qed.

Lemma ind_wit : forall n a, witE n Ind a <-> exists i, a = VInd i.
Proof.
  intros n a. rewrite (proj2 (A2_basic_types fn app A arity Fp n 0) a).
  unfold A. tauto.
Qed.

Lemma dog_type : forall n i, istypeE n (TPred 0 [VInd i]).
Proof.
  intros n i. apply (proj1 (A3_ptypes fn app A arity Fp n 0 [VInd i])).
  exists [Ind]. split; [split; reflexivity |].
  constructor; [apply ind_wit; eauto | constructor].
Qed.

Lemma dog_wit : forall n i a, witE n (TPred 0 [VInd i]) a <-> (i = 0 /\ a = VInd 100).
Proof.
  intros n i a.
  rewrite (proj2 (A3_ptypes fn app A arity Fp n 0 [VInd i]) (dog_type n i) a).
  unfold Fp. split.
  - intros (_ & E & Ha). injection E as E. auto.
  - intros [-> ->]. auto.
Qed.

Lemma dog_family : witE 1 (TFun Ind (TUniv 1)) (VFn f_dog).
Proof.
  destruct (A10_stratification fn app A arity Fp 0) as (_ & _ & _ & HU & HUw & _).
  apply (proj2 (A4_function_types fn app A arity Fp 1 Ind (TUniv 1) (ind_type 1) HU)).
  split; [exists f_dog; reflexivity |]. split.
  - intro a. rewrite ind_wit. destruct a; simpl; split;
      try (intros [i E]; discriminate E); try congruence; eauto;
      try (intro H; exfalso; apply H; reflexivity).
  - intros a b. destruct a; simpl; try discriminate.
    intros E. injection E as <-. apply HUw. apply dog_type.
Qed.

Definition R0 : list (Label * Fld fn) := [(0, FPlain Ind)].
(* [x : Ind, c : dog(x)], with labels x = 0 and c = 1 *)
Definition DogT : V := TRecT ((1, FDep (VFn f_dog) [[0]]) :: R0).
Definition r_good : V := VRec [(0, VInd 0); (1, VInd 100)].
Definition r_bad : V := VRec [(0, VInd 1); (1, VInd 100)].

Lemma R0_clause :
  istypeE 1 (TRecT R0) /\
  forall r, witE 1 (TRecT R0) r <->
    (is_record r /\ exists a, field r 0 = Some a /\ witE 1 Ind a).
Proof.
  destruct (A11_record_types fn app A arity Fp 1) as ([HRec HRecw] & _ & Hplain & _).
  destruct (Hplain 0 Ind [] (fun H => H) HRec (ind_type 1)) as [Hty Hw].
  split; [exact Hty |]. intro r. rewrite (Hw r), (HRecw r). reflexivity.
Qed.

Theorem example_dependent_record_type :
  istypeE 1 DogT /\ witE 1 DogT r_good /\ ~ witE 1 DogT r_bad.
Proof.
  destruct R0_clause as [HR0 HR0w].
  destruct (A11_dependent_record_types fn app A arity Fp 0 1 (VFn f_dog) [[0]] [Ind] R0)
    as [Hty Hw].
  - unfold fresh. simpl. intros [H | []]. discriminate H.
  - exact HR0.
  - constructor; [apply ind_type | constructor].
  - reflexivity.
  - intros r p Hr [<- | []]. apply HR0w in Hr. destruct Hr as [_ (a & Hf & _)].
    simpl. rewrite Hf. discriminate.
  - exact dog_family.
  - split; [exact Hty |]. split.
    + apply Hw. split.
      * apply HR0w. split.
        -- exists [(0, VInd 0); (1, VInd 100)]. split; [reflexivity |].
           simpl. repeat constructor; simpl; intuition discriminate.
        -- exists (VInd 0). split; [reflexivity | apply ind_wit; eauto].
      * exists (VInd 100). split; [reflexivity |].
        exists [VInd 0], (TPred 0 [VInd 0]). split; [| split; [| split]].
        -- constructor; [reflexivity | constructor].
        -- constructor; [apply ind_wit; eauto | constructor].
        -- reflexivity.
        -- apply dog_wit. auto.
    + intro Hbad. apply Hw in Hbad.
      destruct Hbad as [_ (a & Hf & args & c & Hres & _ & Happ & Hwa)].
      inversion Hres as [| p v ps' args' Hr0 Hrest]; subst.
      inversion Hrest; subst. simpl in Hr0. injection Hr0 as <-.
      simpl in Happ. injection Happ as <-.
      apply dog_wit in Hwa. destruct Hwa as [E _]. discriminate E.
Qed.

Theorem example_function_types :
  witE 1 (TFun Ind Ind) (VFn f_id) /\ forall g, ~ witE 1 (TFun Ind Nothing) g.
Proof.
  split.
  - apply (proj2 (A4_function_types fn app A arity Fp 1 Ind Ind (ind_type 1) (ind_type 1))).
    split; [exists f_id; reflexivity |]. split.
    + intro a. rewrite ind_wit. destruct a; simpl; split;
        try (intros [i E]; discriminate E); try congruence; eauto;
      try (intro H; exfalso; apply H; reflexivity).
    + intros a b. destruct a; simpl; try discriminate.
      intros E. injection E as <-. apply ind_wit; eauto.
  - assert (He : forall v : V, ~ A 1 v) by (intros v [E _]; discriminate E).
    destruct (consistency fn app A arity Fp 1 1 He) as (_ & Hneg & _).
    apply (Hneg Ind (VInd 0)). apply ind_wit; eauto.
Qed.

Theorem example_manifest_field : forall r,
  witE 1 (TRecT [(0, FPlain (TSing Ind (VInd 7)))]) r <->
  (is_record r /\ field r 0 = Some (VInd 7)).
Proof.
  intro r.
  destruct (A11_record_types fn app A arity Fp 1) as ([HRec HRecw] & _).
  destruct (manifest_field fn app A arity Fp 1 0 Ind (VInd 7) [] (fun H => H) HRec)
    as [_ Hw].
  - apply ind_wit; eauto.
  - rewrite (Hw r), (HRecw r). reflexivity.
Qed.

End Example.

Print Assumptions Example.example_dependent_record_type.
Print Assumptions Example.example_function_types.
Print Assumptions Example.example_manifest_field.
