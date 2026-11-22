(* Statement checkpoint. Sources and edition locators in CMM_SOURCES.md.
   Finite diagnostics are ours. Only Donkey_Sums and the semantic types
   explicitly imported here are borrowed implementations. *)
From Coq Require Import List Bool Arith Lia.
Require mtt_ranta.Donkey_Sums mtt_ranta.MTT_vs_DTS montague.PTQ ttr.TTR ttr.TTR_Model.
From MontaguePTQ Require Syntax Models.
Import ListNotations.

(* Cooper 2011 (34)-(35), Chatzikyriakidis and Luo 2020 (5.47)-(5.48).
   The list contains precisely the eligible facet pairs at one index.
   First argument of each pair is a copy, second a work. *)
Definition facet := (nat * nat)%type.
Definition label_count (label : facet -> nat) (books : list facet) : nat :=
  length (nodup Nat.eq_dec (map label books)).
Definition three_apart (apart : facet -> facet -> bool) (books : list facet) :=
  existsb (fun x => existsb (fun y => existsb (fun z =>
    apart x y && apart x z && apart y z) books) books) books.
Definition different_at (label : facet -> nat) x y :=
  negb (Nat.eqb (label x) (label y)).
Definition apart_both x y :=
  different_at fst x y && different_at snd x y.
Definition facet_counts (books : list facet) :=
  (label_count fst books, label_count snd books, three_apart apart_both books).

(* Arbitrary carriers, equivalence tests and lexical qualifications. A
   pointwise match of physical and informational distinctness also permits
   different choices of carrier. An inverse on eligible witnesses supplies
   the converse direction without introducing a choice axiom. *)
Definition joint {A : Type} (physical text : A -> A -> Prop) (eligible : A -> Prop) :=
  exists x y z : A, eligible x /\ eligible y /\ eligible z /\
    ~ physical x y /\ ~ physical x z /\ ~ physical y z /\
    ~ text x y /\ ~ text x z /\ ~ text y z.
Definition preservation_statement : Prop :=
  forall (A B : Type) (f : A -> B) (p i : A -> A -> Prop)
    (p' i' : B -> B -> Prop) (E : A -> Prop) (E' : B -> Prop),
    (forall x, E x -> E' (f x)) ->
    (forall x y, p' (f x) (f y) -> p x y) ->
    (forall x y, i' (f x) (f y) -> i x y) ->
    joint p i E -> joint p' i' E'.
Definition shelf : list facet :=
  [(0,0);(1,0);(2,1);(3,1);(4,2);(5,2);(6,2);(7,2);(8,2);(9,2)].
Example cooper_shelf : facet_counts shelf = (10,3,true).
Proof. reflexivity. Qed.
Example separate_copies : facet_counts [(0,0);(1,0);(2,0)] = (3,1,false).
Proof. reflexivity. Qed.
Example one_anthology : facet_counts [(0,0);(0,1);(0,2)] = (1,3,false).
Proof. reflexivity. Qed.
Definition crossed : list facet := [(0,0);(0,1);(0,2);(1,0);(2,0)].
Example two_marginals_overcount : facet_counts crossed = (3,3,false).
Proof. reflexivity. Qed.
Example same_marginals_true : facet_counts [(0,0);(1,1);(2,2)] = (3,3,true).
Proof. reflexivity. Qed.
Definition shares_facet (x y : facet) :=
  Nat.eqb (fst x) (fst y) || Nat.eqb (snd x) (snd y).
Example not_transitive_on_crossed :
  (shares_facet (0,1) (0,0), shares_facet (0,0) (1,0),
   shares_facet (0,1) (1,0)) = (true,true,false).
Proof. reflexivity. Qed.
(* Cooper 2023 (131)-(137). These three observations are reports, not
   journeys. We assign the same passenger to two different journeys. *)
Example passenger_counts :
  let reports : list facet := [(0,10);(0,10);(0,11)] in
  (length reports, label_count fst reports, label_count snd reports) = (3,1,2).
Proof. reflexivity. Qed.

(* Cooper 2023 section 8.3, five farmers and 54 donkeys. One farmer likes
   all 50 of hers. Each of the four others owns one and does not like it.
   Use the existing counting interpretations of Luo 2021 verbatim.
   The finite universes here are exactly the two enumerations. *)
Definition farmers := seq 0 5.
Definition donkeys := seq 0 54.
Definition owns (f d : nat) :=
  if Nat.eqb f 0 then Nat.ltb d 50 else Nat.eqb d (49 + f).
Definition likes (f d : nat) := Nat.eqb f 0 && Nat.ltb d 50.
Definition ownerships := Donkey_Sums.pairs_of owns farmers donkeys.
Example cooper_proportions :
  (length (filter (fun fd => likes (fst fd) (snd fd)) ownerships),
   length ownerships,
   length (filter (Donkey_Sums.strongb_of owns likes donkeys)
             (Donkey_Sums.owners_of owns farmers donkeys)),
   length (Donkey_Sums.owners_of owns farmers donkeys)) = (50,54,1,5).
Proof. vm_compute. reflexivity. Qed.
Example cooper_on_luo_readings :
  Donkey_Sums.pair_reading_c owns likes farmers donkeys /\
  ~ Donkey_Sums.strong_reading_c owns likes farmers donkeys /\
  ~ Donkey_Sums.weak_reading_c owns likes farmers donkeys.
Proof. vm_compute; lia. Qed.
Definition split_likes (f d : nat) := Nat.eqb d (2*f).
Example divided_households :
  Donkey_Sums.weak_reading_c Donkey_Sums.ownb3 split_likes (seq 0 3) (seq 0 6) /\
  ~ Donkey_Sums.strong_reading_c Donkey_Sums.ownb3 split_likes (seq 0 3) (seq 0 6).
Proof. vm_compute; lia. Qed.

(* Cooper 2023 (10), PTQ determiner T2 at one index, CL 2020 sect. 3.2.
   Cooper's rich proposition is observed through inhabitation. We use
   the atlas's ordinary extensional determiner, not its full IL grammar. *)
Definition noun_quantification_statement : Prop :=
  forall (A I D Base Pred : Type) (c : A -> I) (noun : I -> Prop) (vp : I -> Prop)
    (M : TTR_Model.model D Base Pred) (T : I -> TTR.ty Base Pred),
  (forall x, MTT_vs_DTS.image_predicate A I c x <-> noun x) ->
  (forall x, TTR_Model.inhabited_at M (T x) <-> noun x) ->
  (MTT.every A (fun a => vp (c a)) <-> PTQ.d_every I noun vp) /\
  ((forall x, TTR_Model.inhabited_at M (T x) -> vp x) <-> PTQ.d_every I noun vp).
Definition noun_assignment : TTR_Model.model unit unit bool :=
  {| TTR_Model.basic_extension := fun _ _ => True;
     TTR_Model.ptype_extension := fun p args v =>
       p = true /\ args = [] /\ v = TTR.VBase tt |}.
Definition noun_ptype (e : bool) : TTR.ty unit bool := TTR.TPty e [].
Example nontrivial_noun_assignment :
  (forall e, MTT_vs_DTS.image_predicate unit bool (fun _ => true) e <-> e = true) /\
  (forall e, TTR_Model.inhabited_at noun_assignment (noun_ptype e) <-> e = true).
Proof.
  split.
  - intros e; split; [intros [[] <-]; reflexivity | intros ->; exists tt; reflexivity].
  - intros e; split; [intros [v [H _]]; exact H | intros ->; exists (TTR.VBase tt);
      repeat split; reflexivity].
Qed.

(* Going from world-time truth values to attitude reports.
   PTQ sections 2-4, Cooper 2023 (35)-(40),(58), CL 2020 (4.79)-(4.80).
   The constant co-denotation here is a model stipulation. The two
   descriptions themselves are intentionally different constructors. *)
Inductive description := purchase | sale.
Definition two_times : Models.frame.
Proof.
  refine {| Models.entity := bool; Models.world := unit; Models.time := bool;
            Models.entity_nonempty := inhabits false;
            Models.world_nonempty := inhabits tt; Models.time_nonempty := inhabits false;
            Models.time_le := fun t u => t = false \/ u = true |}.
  - intros []; cbv; auto.
  - intros [] [] []; cbv; intuition congruence.
  - intros [] []; cbv; intuition congruence.
  - intros [] []; cbv; auto.
Defined.
Definition denotation (_ : description) : Models.domain two_times (Syntax.intens Syntax.t) :=
  fun it => snd it.
Definition pleased (d : description) := match d with purchase => true | sale => false end.
Example intensions_coincide : denotation purchase = denotation sale.
Proof. reflexivity. Qed.
Example report_cannot_factor :
  ~ exists F : Models.domain two_times (Syntax.intens Syntax.t) -> bool,
    forall d, F (denotation d) = pleased d.
Proof.
  intros [F H]. pose proof (H purchase) as Hb. pose proof (H sale) as Hs.
  change (F (denotation purchase) = true) in Hb.
  change (F (denotation purchase) = false) in Hs.
  congruence.
Qed.
(* Cooper 2023 (13): truth-level version 1 with inhabited local base.
   It does not implement the final topos-based (23). *)
Definition indices : list (Models.index two_times) := [(tt,false);(tt,true)].
Definition all_indices (P : Models.index two_times -> bool) := forallb P indices.
Definition prelim_necessity (here : Models.index two_times)
  (base ideal P : Models.index two_times -> bool) :=
  base here && all_indices (fun i => implb (base i && ideal i) (P i)).
Example unrestricted_modal_agreement :
  prelim_necessity (tt,true) (fun _ => true) (fun _ => true) (denotation purchase)
  = all_indices (denotation purchase).
Proof. reflexivity. Qed.
Example restricted_modal_difference :
  (prelim_necessity (tt,true) (fun _ => true) snd (denotation purchase),
   all_indices (denotation purchase)) = (true,false).
Proof. reflexivity. Qed.

(* A precise relation between PTQ Box and Atlas family-level necessity.
   Primary sources: PTQ section 2, Cooper 2023 Appendix A9. Realization
   supplies truth equivalence per index. The family is exactly the image. *)
Definition modal_bridge_statement : Prop :=
  forall (D Base Pred : Type) (M : Models.model)
    (u : Syntax.tm [] Syntax.t) rho sigma i
    (assignment : Models.index (Models.carrier M) -> TTR_Model.model D Base Pred)
    (T : TTR.ty Base Pred),
  (forall j, Models.eval M u rho sigma j = true <->
             TTR_Model.inhabited_at (assignment j) T) ->
  (Models.eval M (Syntax.Box u) rho sigma i = true <->
   TTR_Model.necessary D Base Pred (fun m => exists j, assignment j = m) T).

(* Modification. In the finite example the assertion that someone allegedly
   wrote can be true without a writing event. CL 2020 (4.58),(4.80).
   The ability test illustrates sensitivity to the profession chosen. *)
Inductive profession := surgeon | violinist.
Definition skilled (p : profession) (_ : unit) :=
  match p with surgeon => true | violinist => false end.
Example skill_varies_by_profession : (skilled surgeon tt, skilled violinist tt) = (true,false).
Proof. reflexivity. Qed.
Record occurrence := { actor : bool; patient : bool; writing : bool; illegible : bool }.
Definition wrote (a : bool) (ds : list occurrence) :=
  existsb (fun e => Bool.eqb (actor e) a && writing e) ds.
Definition wrote_illegibly (a : bool) (ds : list occurrence) :=
  existsb (fun e => Bool.eqb (actor e) a && writing e && illegible e) ds.
Example manner_requires_same_event :
  let w := Build_occurrence true false true false in
  let i := Build_occurrence true false false true in
  (wrote true [w;i], wrote_illegibly true [w;i],
   wrote_illegibly true [Build_occurrence true false true true]) = (true,false,true).
Proof. reflexivity. Qed.
(* Toy report catalogue. A person can allege a writing that did not occur. *)
Definition allegedly_wrote (subject : bool) (claims : list (bool * bool)) :=
  existsb (fun report => Bool.eqb (snd report) subject) claims.
Example unfulfilled_allegation :
  (allegedly_wrote true [(false,true)], wrote true []) = (true,false).
Proof. reflexivity. Qed.

(* Luo and Soloviev 2017 sections 2-3,5. Our representation of their
   lexical example using an event record with two functional roles. *)
Definition agent_event a := {v : occurrence | actor v = a}.
Definition patient_event p := {v : occurrence | patient v = p}.
Definition two_role_event a p := {v : occurrence | actor v = a /\ patient v = p}.
Definition forget_patient a p (v : two_role_event a p) : agent_event a :=
  exist _ (proj1_sig v) (proj1 (proj2_sig v)).
Definition forget_agent a p (v : two_role_event a p) : patient_event p :=
  exist _ (proj1_sig v) (proj2 (proj2_sig v)).
Definition role_diamond_statement : Prop := forall a p (v : two_role_event a p),
  proj1_sig (forget_patient a p v) = proj1_sig (forget_agent a p v).
Example one_occurrence_both_roles :
  let v := Build_occurrence true false true true in
  let both := exist (fun z => actor z = true /\ patient z = false) v (conj eq_refl eq_refl) in
  proj1_sig (forget_patient true false both) = proj1_sig (forget_agent true false both).
Proof. reflexivity. Qed.
(* Scope fragment for the event quantification problem. The only free
   names checked here are agent names appearing in binder domains.
   A bare event binder has no such dependency. *)
Inductive bind := person (name : nat) | event_of (name : nat) | bare_event.
Fixpoint domains_in_scope (people : list nat) (binders : list bind) : bool :=
  match binders with
  | [] => true
  | person x :: bs => domains_in_scope (x :: people) bs
  | event_of x :: bs => existsb (Nat.eqb x) people && domains_in_scope people bs
  | bare_event :: bs => domains_in_scope people bs
  end.
Example binder_order_in_empty_context :
  (domains_in_scope [] [person 0;event_of 0],
   domains_in_scope [] [event_of 0;person 0],
   domains_in_scope [] [bare_event;person 0]) = (true,false,true).
Proof. reflexivity. Qed.

(* A role-indexed kiss, its Cooper-style witnesses, and its extension at a
   PTQ index. Our two assignments realize the same kiss predication in two
   different ways. Luo and Soloviev 2017 (1)-(4), Cooper 2023 sect. 1.4.3.
   We use the same finite lexical table for all three interpretations. *)
Module Kiss.
Inductive token := passionate | ordinary | reversed.
Inductive atom := individual (a : bool) | situation (k : token).
Definition roles (k : token) : bool * bool :=
  match k with reversed => (false,true) | _ => (true,false) end.
Definition available (version : bool) (k : token) : bool :=
  match k with passionate => version | ordinary => negb version | reversed => false end.
Definition evt_ap (a p : bool) := {k : token | roles k = (a,p)}.
Definition occurs (version : bool) (a p : bool) :=
  exists v : evt_ap a p, available version (proj1_sig v) = true.
Definition assignment (version : bool) : TTR_Model.model atom unit unit :=
  {| TTR_Model.basic_extension := fun _ _ => True;
     TTR_Model.ptype_extension := fun _ args v =>
       match v with
       | TTR.VBase (situation k) =>
           args = [individual (fst (roles k)); individual (snd (roles k))] /\
           available version k = true
       | _ => False
       end |}.
Definition record_witness (version a p : bool) (k : token) :=
  TTR_Model.typing (assignment version)
    [(0,TTR.VBase (individual a));(1,TTR.VBase (individual p))]
    (TTR.VBase (situation k)) (TTR.TPty tt [[0];[1]]).
Definition relation (ver : bool) : Models.domain two_times
    (Syntax.arr Syntax.e (Syntax.arr Syntax.e Syntax.t)) :=
  fun a p => existsb (fun k => Bool.eqb (fst (roles k)) a &&
                              Bool.eqb (snd (roles k)) p && available ver k)
                     [passionate;ordinary;reversed].
Example assignment_respects_arity : forall ver,
  TTR_Model.admissible atom unit unit (fun _ => [tt;tt]) (assignment ver).
Proof.
  intros ver; split.
  - intros d; exists tt; exact I.
  - intros [] args [[a|k]|r]; try contradiction. cbn.
    intros [-> _]; repeat constructor.
Qed.
Example three_observations_match :
  forall ver a p, (occurs ver a p <-> relation ver a p = true) /\
                  ((exists k, record_witness ver a p k) <-> relation ver a p = true).
Proof.
  intros ver a p. split.
  - split.
    + intros [[k match_roles] live]. destruct k, ver, a, p; cbv in *; congruence.
    + destruct ver, a, p; cbv; try discriminate; intro H.
      * exists (exist (fun k => roles k = (true,false)) passionate eq_refl); reflexivity.
      * exists (exist (fun k => roles k = (true,false)) ordinary eq_refl); reflexivity.
  - split.
    + intros [k H]; destruct k, ver, a, p; cbv in *; intuition congruence.
    + destruct ver, a, p; cbv; try discriminate; intro H.
      * exists passionate; split; reflexivity.
      * exists ordinary; split; reflexivity.
Qed.
Example same_pairs_different_manner :
  (forall a p, relation true a p = relation false a p) /\
  record_witness true true false passionate /\
  ~ record_witness false true false passionate.
Proof. split; [intros [] []; reflexivity|cbv; intuition congruence]. Qed.
End Kiss.

(* Consequence of treating every physical copy as carrying exactly one
   work at the chosen granularity. This premise is debated in CL 2020,
   section 5.1, p. 102, footnote 4. *)
Definition one_work_per_copy_statement : Prop :=
  forall books : list facet,
  (forall x y, In x books -> In y books -> fst x = fst y -> snd x = snd y) ->
  three_apart (different_at snd) books = three_apart apart_both books.

(* Sutton 2024 (4)-(5), (36)-(39). Two resolved counting bases for
   insightful/damaged books. This is our finite truth test downstream
   of context resolution. The question stack and lexical updates are
   discussed in the report. The ineligible fourth book remains on the shelf. *)
Module Display.
Record library_book := { facets : facet; insightful : bool; damaged : bool }.
Definition eligible (shelf : list library_book) :=
  map facets (filter (fun b => insightful b && damaged b) shelf).
Definition stock := [Build_library_book (0,0) true true;
                     Build_library_book (1,0) true true;
                     Build_library_book (2,0) true true;
                     Build_library_book (3,1) false true].
Example readings_after_context_resolution :
  let books := eligible stock in
  (three_apart apart_both books, three_apart (different_at fst) books) = (false,true).
Proof. reflexivity. Qed.
End Display.

(* Chatzikyriakidis, Cooper, Gregoromichelaki and Sutton 2025, sect. 2,
   p. 19. A fixed agent's collection of truth intensions need not be upward
   closed under entailment. This example uses the PTQ semantic domain. *)
Definition attributed (p : Models.domain two_times (Syntax.intens Syntax.t)) :=
  p (tt,true) && negb (p (tt,false)).
Example belief_relation_need_not_close_under_entailment :
  let p := denotation purchase in
  let q := fun _ : Models.index two_times => true in
  (forall i, p i = true -> q i = true) /\
    attributed p = true /\ attributed q = false.
Proof. repeat split; reflexivity. Qed.
