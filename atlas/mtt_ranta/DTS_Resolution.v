(* BM17 sections 3.4-3.6, pp. 28-30, especially Definition 5.
   A BOUNDED typed @ calculus: pronoun slots target entity, and candidates
   are projections from a finite dependent telescope. ref n abbreviates
   n second projections followed by a first projection; @ i denotes an
   explicitly declared hole. Resolving it chooses ONE typed projection,
   consistently for all occurrences of i. No unrestricted DTT search,
   CCG, accommodation, or automatic salience ranking is claimed.

   The telescope retains arbitrary dependent proof fields. Its shape is
   used only to find entity binders, not to identify proof types. Thus
   search completeness below is ONLY for entity projection candidates,
   not for all proofs/terms of DTS. Empty search is not global infelicity:
   background constants and accommodation are outside this fragment.
   No axioms, no admitted proofs, no claim of framework equivalence. *)
Require Import List Arith.
Require mtt_ranta.DTS.
Import ListNotations.

Inductive sort := entity | evidence.
Inductive term := ref (index : nat) | hole (slot : nat).

Inductive typed (G : list sort) (holes : list nat) : term -> Prop :=
| t_ref : forall n, nth_error G n = Some entity -> typed G holes (ref n)
| t_at : forall i, In i holes -> typed G holes (hole i).

Definition substitution := nat -> option nat.
Definition sound_substitution (G : list sort) (s : substitution) :=
  forall i n, s i = Some n -> nth_error G n = Some entity.
Definition covers (holes : list nat) (s : substitution) :=
  forall i, In i holes -> exists n, s i = Some n.
Definition instantiate (s : substitution) (t : term) : option term :=
  match t with ref n => Some (ref n)
             | hole i => option_map ref (s i) end.

(* A typed instance of BM17's equation @i = M : A, with A = entity
   at the local context and M a context projection. Abstracting over
   the local context gives the function type in their formula (40). *)
Definition resolution_equation G holes i n :=
  typed G holes (hole i) /\ typed G [] (ref n).

Theorem substitution_preserves_typing : forall G holes s t u,
  sound_substitution G s -> typed G holes t ->
  instantiate s t = Some u -> typed G [] u.
Proof.
  intros G holes s t u Hs Ht; destruct Ht; simpl.
  - intros Eq; inversion Eq; subst; constructor; assumption.
  - destruct (s i) eqn:E; simpl; try discriminate.
    intros Eq; inversion Eq; subst; constructor; eapply Hs; eauto.
Qed.

Theorem covered_terms_resolve : forall G holes s t,
  covers holes s -> typed G holes t -> exists u, instantiate s t = Some u.
Proof.
  intros G holes s t Hs Ht; destruct Ht; simpl.
  - eexists; reflexivity.
  - destruct (Hs i H) as [n E]; rewrite E; eexists; reflexivity.
Qed.

Theorem repeated_slot_consistent : forall s i u v,
  instantiate s (hole i) = Some u -> instantiate s (hole i) = Some v -> u = v.
Proof. intros; congruence. Qed.

Fixpoint search (G : list sort) : list nat :=
  match G with
  | [] => []
  | entity :: rest => 0 :: map S (search rest)
  | evidence :: rest => map S (search rest)
  end.

Theorem search_exact : forall G n,
  In n (search G) <-> nth_error G n = Some entity.
Proof.
  induction G as [|a G IH]; intros n.
  - destruct n; simpl; split; contradiction || discriminate.
  - destruct a; destruct n; simpl.
    + tauto.
    + rewrite in_map_iff, <- IH; split.
      * intros [H | [m [E H]]]; [discriminate | injection E as E; subst; exact H].
      * intros H; right; exists n; auto.
    + rewrite in_map_iff; split.
      * intros [m [E _]]; discriminate.
      * discriminate.
    + rewrite in_map_iff, <- IH; split.
      * intros [m [E H]]; injection E as E; subst; exact H.
      * intros H; exists n; auto.
Qed.

Theorem search_builds_equation : forall G holes i n,
  In i holes -> In n (search G) -> resolution_equation G holes i n.
Proof.
  intros; split; constructor; [assumption | apply search_exact; assumption].
Qed.

(* Executable policy: take the first projection for each declared hole.
   This is a deterministic demonstration policy, NOT a salience theory;
   search still exposes every candidate, including ambiguous alternatives. *)
Definition choose G holes : substitution := fun i =>
  if in_dec Nat.eq_dec i holes then hd_error (search G) else None.
Definition resolve G holes t := instantiate (choose G holes) t.

Theorem choose_sound : forall G holes, sound_substitution G (choose G holes).
Proof.
  intros G holes i n; unfold choose.
  destruct (in_dec Nat.eq_dec i holes); [|discriminate].
  destruct (search G) as [|a rest] eqn:E; simpl; [discriminate |].
  intros H; inversion H; subst.
  apply search_exact; rewrite E; simpl; auto.
Qed.

Theorem choose_covers : forall G holes,
  search G <> [] -> covers holes (choose G holes).
Proof.
  intros G holes H i Hi; unfold choose.
  destruct (in_dec Nat.eq_dec i holes); [|contradiction].
  destruct (search G) as [|a rest]; [contradiction |].
  exists a; reflexivity.
Qed.

Theorem automatic_resolution_sound : forall G holes t u,
  typed G holes t -> resolve G holes t = Some u -> typed G [] u.
Proof.
  intros; eapply substitution_preserves_typing; eauto using choose_sound.
Qed.

Theorem automatic_resolution_total_on_projection_contexts : forall G holes t,
  search G <> [] -> typed G holes t -> exists u, resolve G holes t = Some u.
Proof.
  intros; eapply covered_terms_resolve; eauto using choose_covers.
Qed.

Theorem automatic_resolution_examples :
  resolve [evidence; entity; evidence; evidence] [0] (hole 0) = Some (ref 1) /\
  resolve [] [0] (hole 0) = None /\
  resolve [entity] [] (hole 0) = None.
Proof. repeat split; reflexivity. Qed.

(* A tiny sentence interface makes the formation/verification distinction
   explicit: negation changes truth conditions, not hole obligations.
   Conditional LOCAL contexts are supplied as G, never exported by search. *)
Inductive sentence := atom (predicate : nat) (arg : term)
                    | neg (body : sentence) | conj (a b : sentence).
Fixpoint well_formed G holes s : Prop :=
  match s with
  | atom _ t => typed G holes t
  | neg a => well_formed G holes a
  | conj a b => well_formed G holes a /\ well_formed G holes b
  end.

Theorem negation_same_obligations : forall G holes a,
  well_formed G holes (neg a) <-> well_formed G holes a.
Proof. reflexivity. Qed.

Section DependentInterpretation.
Variable Entity : Type.

(* Unlike the finite shape, proof types may depend on earlier entities
   and proofs. This is a telescope, not a list of untyped individuals. *)
Inductive telescope : list sort -> Type :=
| done : telescope []
| bind_entity : forall ss, (Entity -> telescope ss) -> telescope (entity :: ss)
| bind_evidence : forall ss (A : Type), (A -> telescope ss) ->
    telescope (evidence :: ss).

Fixpoint environment {ss} (G : telescope ss) : Type :=
  match G with
  | done => unit
  | bind_entity _ rest => {x : Entity & environment (rest x)}
  | bind_evidence _ A rest => {p : A & environment (rest p)}
  end.

Fixpoint erase {ss} (G : telescope ss) : environment G -> list (option Entity) :=
  match G as g return environment g -> list (option Entity) with
  | done => fun _ => []
  | bind_entity _ rest => fun c =>
      Some (projT1 c) :: erase (rest (projT1 c)) (projT2 c)
  | bind_evidence _ _ rest => fun c =>
      None :: erase (rest (projT1 c)) (projT2 c)
  end.

Theorem projection_interpretation : forall ss (G : telescope ss) c n,
  nth_error ss n = Some entity ->
  exists e, nth_error (erase G c) n = Some (Some e).
Proof.
  intros ss G; induction G as [|ss rest IH|ss A rest IH]; intros c n H.
  - destruct n; discriminate H.
  - destruct c as [x c]; destruct n; simpl in *.
    + exists x; reflexivity.
    + exact (IH x c n H).
  - destruct c as [p c]; destruct n; simpl in *.
    + discriminate H.
    + exact (IH p c n H).
Qed.

Theorem resolved_term_has_entity : forall ss (G : telescope ss) c holes s t u,
  sound_substitution ss s -> typed ss holes t ->
  instantiate s t = Some u ->
  exists n e, u = ref n /\ nth_error (erase G c) n = Some (Some e).
Proof.
  intros ss G c holes s t u Hs Ht H.
  pose proof (substitution_preserves_typing ss holes s t u Hs Ht H) as Hu.
  inversion Hu; subst.
  - destruct (projection_interpretation ss G c n H0) as [e He].
    exists n, e; auto.
  - contradiction.
Qed.

Section MiniDiscourse.
Variable Prior : Type.
Variables man enter : Entity -> Type.
Definition discourse_telescope : telescope [evidence; entity; evidence; evidence] :=
  bind_evidence _ Prior (fun _ => bind_entity _ (fun x =>
    bind_evidence _ (man x) (fun _ =>
      bind_evidence _ (enter x) (fun _ => done)))).

Definition source_context := (Prior * DTS.PredicateDTS.first Entity man enter)%type.
Definition flatten (c : source_context) : environment discourse_telescope :=
  let '(prior, existT _ x (m, e)) := c in
  existT _ prior (existT _ x (existT _ m (existT _ e tt))).
Definition unflatten (c : environment discourse_telescope) : source_context :=
  let 'existT _ prior (existT _ x (existT _ m (existT _ e _))) := c in
  (prior, existT _ x (m, e)).

Theorem flatten_roundtrip : forall c, unflatten (flatten c) = c.
Proof. intros [prior [x [m e]]]; reflexivity. Qed.

Theorem unflatten_roundtrip : forall c, flatten (unflatten c) = c.
Proof. intros [prior [x [m [e []]]]]; reflexivity. Qed.

Theorem source_projection_adequate : forall c,
  nth_error (erase discourse_telescope (flatten c)) 1 =
    Some (Some (projT1 (snd c))).
Proof. intros [prior [x [m e]]]; reflexivity. Qed.

(* BM17 (41)-(42), after explicit reassociation into a flat telescope:
   the sole entity projection is the man introduced by the first clause. *)
Theorem mini_discourse_search : search [evidence; entity; evidence; evidence] = [1].
Proof. reflexivity. Qed.

Theorem mini_discourse_antecedent : forall c : environment discourse_telescope,
  nth_error (erase discourse_telescope c) 1 =
    Some (Some (projT1 (projT2 c))).
Proof. intros [prior [x [m [e u]]]]; reflexivity. Qed.
End MiniDiscourse.
End DependentInterpretation.

Theorem no_local_antecedent : search [] = [] /\ ~ typed [] [] (ref 0).
Proof. split; [reflexivity | intros H; inversion H; discriminate]. Qed.

Theorem two_antecedents : search [entity; entity] = [0; 1] /\
  resolution_equation [entity; entity] [7] 7 0 /\
  resolution_equation [entity; entity] [7] 7 1.
Proof.
  split; [reflexivity | split; apply search_builds_equation; simpl; auto].
Qed.

Theorem local_context_not_exported :
  In 0 (search [entity; evidence]) /\ ~ In 0 (search [evidence]).
Proof. simpl; tauto. Qed.

(* Search ambiguity is semantically real, not merely two proofs of typing. *)
Theorem ambiguity_changes_referent :
  nth_error [Some true; Some false] 0 <> nth_error [Some true; Some false] 1.
Proof. discriminate. Qed.
