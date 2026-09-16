(* Heim (1982), final file change semantics, in the 2011 retypesetting.
   Source: III.1.4, III.2.1.1 (B), III.4.4 p.234 (I-IV), p.254 fn.28 (V),
   pp.202/236-238 (extended NFC), pp.214-220 (truth).
   Requirements/coverage: atlas_data/campaigns/heim_1982_design.md.

   Arbitrary worlds/individuals; infinite assignments; predicate-valued sets;
   independent file domain and satisfaction; statically finite-arity atoms.
   No finite-domain reduction, choice, extensionality, classical axiom or
   assumption that satisfaction/felicity is decidable. Equality of files is
   pointwise. The source's B is kept distinct from stronger domain support.
   Formula represents interpreted LF, NOT a complete English grammar.
   Mark records NP definiteness; Use records a non-formula definite occurrence.
   Felicity includes precisely the specified checks, not every pragmatic cause
   of infelicity. Accommodation is a separate extension, not hidden in update. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Set Implicit Arguments.

Fixpoint tuple (A : Type) (n : nat) : Type :=
  match n with 0 => unit | S k => (A * tuple A k)%type end.

Fixpoint slots (n : nat) : tuple nat n -> list nat :=
  match n return tuple nat n -> list nat with
  | 0 => fun _ => []
  | S k => fun xs => fst xs :: slots k (snd xs)
  end.

Section Semantics.
Context {W D : Type}.
Definition Assignment := nat -> D.
Definition Domain := nat -> Prop.
Definition agree (d : Domain) (g h : Assignment) :=
  forall i, d i -> g i = h i.
Definition differs (i : nat) (g h : Assignment) :=
  forall j, j <> i -> g j = h j.
Definition put (g : Assignment) (i : nat) (x : D) : Assignment :=
  fun j => if Nat.eq_dec j i then x else g j.

Lemma put_same : forall g i x, put g i x i = x.
Proof. intros; unfold put; destruct (Nat.eq_dec i i); congruence. Qed.
Lemma put_other : forall g i x j, j <> i -> put g i x j = g j.
Proof. intros; unfold put; destruct (Nat.eq_dec j i); congruence. Qed.
Lemma agree_refl : forall d g, agree d g g.
Proof. intros d g i Hi; reflexivity. Qed.
Lemma agree_sym : forall d g h, agree d g h -> agree d h g.
Proof. intros d g h H i Hi; symmetry; apply H; exact Hi. Qed.
Lemma agree_trans : forall d g h k,
  agree d g h -> agree d h k -> agree d g k.
Proof. intros d g h k H1 H2 i Hi; rewrite (H1 i Hi); apply H2; exact Hi. Qed.
Lemma differs_agree : forall d i g h,
  ~ d i -> differs i g h -> agree d g h.
Proof. intros d i g h Hn H j Hj; apply H; intro E; subst; contradiction. Qed.

Record File := { dom : Domain; sat : W -> Assignment -> Prop }.
Definition file_equiv (F G : File) :=
  (forall i, dom F i <-> dom G i) /\
  (forall w g, sat F w g <-> sat G w g).
Definition condition_B (F : File) := forall w i g h,
  ~ dom F i -> differs i g h -> (sat F w g <-> sat F w h).
Definition supported (F : File) := forall w g h,
  agree (dom F) g h -> (sat F w g <-> sat F w h).
Definition empty_file : File :=
  {| dom := fun _ => False; sat := fun _ _ => True |}.
Definition false_file (d : Domain) : File :=
  {| dom := d; sat := fun _ _ => False |}.
Definition world_content (F : File) (w : W) := exists g, sat F w g.

Lemma supported_implies_B : forall F, supported F -> condition_B F.
Proof. intros F H w i g h Hn Hd; apply H; eapply differs_agree; eauto. Qed.
Lemma empty_supported : supported empty_file.
Proof. intros w g h H; simpl; tauto. Qed.
Lemma false_supported : forall d, supported (false_file d).
Proof. intros d w g h H; simpl; tauto. Qed.
Theorem empty_file_truth_needs_inhabited_domain : forall w,
  world_content empty_file w <-> inhabited D.
Proof.
  intro w; split.
  - intros [g _]; exact (inhabits (g 0)).
  - intros [d]; exists (fun _ => d); exact I.
Qed.
Lemma fresh_put : forall F, condition_B F -> forall w g i x,
  ~ dom F i -> (sat F w (put g i x) <-> sat F w g).
Proof.
  intros F HB w g i x Hn; apply HB with i; [exact Hn |].
  intros j Hj; apply put_other; exact Hj.
Qed.

Fixpoint values (n : nat) (g : Assignment) : tuple nat n -> tuple D n :=
  match n return tuple nat n -> tuple D n with
  | 0 => fun _ => tt
  | S k => fun xs => (g (fst xs), values k g (snd xs))
  end.
Lemma values_agree : forall n xs g h,
  (forall i, In i (slots n xs) -> g i = h i) -> values n g xs = values n h xs.
Proof.
  induction n as [|n IH]; intros xs g h H; [reflexivity |].
  destruct xs as [i xs]; simpl in *.
  rewrite (H i (or_introl eq_refl)), (IH xs g h); [reflexivity |].
  intros j Hj; apply H; right; exact Hj.
Qed.

Inductive Formula : Type :=
| Atom : forall n, tuple nat n -> (W -> tuple D n -> Prop) -> Formula
| Seq : Formula -> Formula -> Formula
| Every : Formula -> Formula -> Formula
| Not : Formula -> Formula
| Or : Formula -> Formula -> Formula
| Mark : bool -> nat -> Formula -> Formula
| Use : nat -> Formula.

Definition atomic (n : nat) (xs : tuple nat n)
  (P : W -> tuple D n -> Prop) (F : File) : File :=
  {| dom := fun i => dom F i \/ In i (slots n xs);
     sat := fun w g => sat F w g /\ P w (values n g xs) |}.
Definition filter (F : File) (P : W -> Assignment -> Prop) : File :=
  {| dom := dom F; sat := fun w g => sat F w g /\ P w g |}.
Definition extension_at (d : Domain) (G : File) w g :=
  exists h, agree d g h /\ sat G w h.
Definition universal_result (F R S : File) : File :=
  filter F (fun w g => forall h,
    agree (dom F) g h -> sat R w h -> extension_at (dom R) S w h).
Definition negative_result (F G : File) : File :=
  filter F (fun w g => ~ extension_at (dom F) G w g).
Definition disjunctive_result (F G H : File) : File :=
  filter F (fun w g => extension_at (dom F) G w g \/ extension_at (dom F) H w g).

Theorem disjunction_single_witness : forall F G H w g,
  sat (disjunctive_result F G H) w g <->
  sat F w g /\ exists h, agree (dom F) g h /\ (sat G w h \/ sat H w h).
Proof.
  intros F G H w g; split.
  - intros [HF [[h [Ha HG]] | [h [Ha HH]]]]; split; auto; exists h; auto.
  - intros [HF [h [Ha [HG | HH]]]]; split; auto;
      [left | right]; exists h; auto.
Qed.

Fixpoint update (p : Formula) (F : File) : File :=
  match p with
  | Atom n xs P => atomic n xs P F
  | Seq p q => update q (update p F)
  | Every p q => let R := update p F in universal_result F R (update q R)
  | Not p => negative_result F (update p F)
  | Or p q => disjunctive_result F (update p F) (update q F)
  | Mark _ _ p => update p F
  | Use _ => F
  end.
Definition entails (F : File) (p : Formula) :=
  forall w g, sat F w g -> sat (update p F) w g.

(* Raw meanings are used to test descriptive entailment; definedness is
   checked separately, avoiding a circular definition of presupposition. *)
Fixpoint licensed (p : Formula) (F : File) : Prop :=
  match p with
  | Atom _ _ _ => True
  | Seq p q => licensed p F /\ licensed q (update p F)
  | Every p q => licensed p F /\ licensed q (update p F)
  | Not p => licensed p F
  | Or p q => licensed p F /\ licensed q F
  | Mark definite i p =>
      (if definite then dom F i /\ entails F p else ~ dom F i) /\ licensed p F
  | Use i => dom F i
  end.
Definition defined_update (p : Formula) (F G : File) :=
  licensed p F /\ file_equiv (update p F) G.
Definition utterance_true (p : Formula) F w :=
  licensed p F /\ world_content (update p F) w.
Definition utterance_false (p : Formula) F w :=
  licensed p F /\ world_content F w /\ ~ world_content (update p F) w.

Fixpoint exported (p : Formula) : list nat :=
  match p with
  | Atom n xs _ => slots n xs
  | Seq p q => exported p ++ exported q
  | Mark _ _ p => exported p
  | _ => []
  end.

Theorem domain_update : forall p F i,
  dom (update p F) i <-> dom F i \/ In i (exported p).
Proof.
  induction p; intros F i; simpl.
  - tauto.
  - rewrite IHp2, IHp1, in_app_iff; tauto.
  - tauto.
  - tauto.
  - tauto.
  - apply IHp.
  - tauto.
Qed.
Theorem update_contractive : forall p F w g,
  sat (update p F) w g -> sat F w g.
Proof.
  induction p; intros F w g H; simpl in H.
  - exact (proj1 H).
  - apply IHp1; apply IHp2; exact H.
  - exact (proj1 H).
  - exact (proj1 H).
  - exact (proj1 H).
  - eapply IHp; exact H.
  - exact H.
Qed.
Theorem file_truth_contracts : forall p F w,
  world_content (update p F) w -> world_content F w.
Proof. intros p F w [g H]; exists g; eapply update_contractive; exact H. Qed.
Theorem true_false_exclusive : forall p F w,
  utterance_true p F w -> ~ utterance_false p F w.
Proof. unfold utterance_true, utterance_false; firstorder. Qed.
Theorem false_input_has_no_C_truth_value : forall p F w,
  ~ world_content F w -> ~ utterance_true p F w /\ ~ utterance_false p F w.
Proof.
  intros p F w H; split.
  - intros [_ Hu]; apply H; eapply file_truth_contracts; exact Hu.
  - intros [_ [Hf _]]; contradiction.
Qed.
Theorem infelicity_is_neither_true_nor_false : forall p F w,
  ~ licensed p F -> ~ utterance_true p F w /\ ~ utterance_false p F w.
Proof. unfold utterance_true, utterance_false; firstorder. Qed.

Lemma extension_at_agree : forall d G w g h,
  agree d g h -> (extension_at d G w g <-> extension_at d G w h).
Proof.
  intros d G w g h H; split; intros [k [Hk Hs]]; exists k; split; auto.
  - eapply agree_trans; [apply agree_sym; exact H | exact Hk].
  - eapply agree_trans; eauto.
Qed.
Lemma universal_test_agree : forall F R S w g h,
  agree (dom F) g h ->
  ((forall k, agree (dom F) g k -> sat R w k -> extension_at (dom R) S w k) <->
   (forall k, agree (dom F) h k -> sat R w k -> extension_at (dom R) S w k)).
Proof.
  intros F R S w g h H; split; intros HH k Hk Hs; apply HH; auto.
  - eapply agree_trans; eauto.
  - eapply agree_trans; [apply agree_sym; exact H | exact Hk].
Qed.

Arguments extension_at_agree d G w g h _ : clear implicits.
Arguments universal_test_agree F R S w g h _ : clear implicits.
Arguments fresh_put F _ w g i x _ : clear implicits.

Theorem update_preserves_B : forall p F,
  condition_B F -> condition_B (update p F).
Proof.
  induction p; intros F HB.
  - intros w i g h Hn Hd; simpl in *.
    assert (Hf : ~ dom F i) by tauto.
    assert (Hv : values n g t = values n h t).
    { apply values_agree; intros j Hj; apply Hd.
      intro E; subst; apply Hn; right; exact Hj. }
    rewrite (HB w i g h Hf Hd), Hv; tauto.
  - apply IHp2, IHp1; exact HB.
  - intros w i g h Hn Hd; simpl in *.
    assert (Ha : agree (dom F) g h) by (eapply differs_agree; eauto).
    unfold universal_result, filter; simpl.
    rewrite (HB w i g h Hn Hd), (universal_test_agree F (update p1 F)
      (update p2 (update p1 F)) w g h Ha); tauto.
  - intros w i g h Hn Hd; simpl in *.
    assert (Ha : agree (dom F) g h) by (eapply differs_agree; eauto).
    unfold negative_result, filter; simpl.
    rewrite (HB w i g h Hn Hd), (extension_at_agree (dom F) (update p F) w g h Ha); tauto.
  - intros w i g h Hn Hd; simpl in *.
    assert (Ha : agree (dom F) g h) by (eapply differs_agree; eauto).
    unfold disjunctive_result, filter; simpl.
    rewrite (HB w i g h Hn Hd), (extension_at_agree (dom F) (update p1 F) w g h Ha),
      (extension_at_agree (dom F) (update p2 F) w g h Ha); tauto.
  - apply IHp; exact HB.
  - exact HB.
Qed.

Theorem update_preserves_support : forall p F,
  supported F -> supported (update p F).
Proof.
  induction p; intros F HF.
  - intros w g h Ha; simpl in *.
    assert (Hf : agree (dom F) g h) by (intros i Hi; apply Ha; left; exact Hi).
    assert (Hv : values n g t = values n h t).
    { apply values_agree; intros i Hi; apply Ha; right; exact Hi. }
    rewrite (HF w g h Hf), Hv; tauto.
  - apply IHp2, IHp1; exact HF.
  - intros w g h Ha; simpl in Ha.
    unfold update, universal_result, filter; fold update; simpl.
    rewrite (HF w g h Ha), (universal_test_agree F (update p1 F)
      (update p2 (update p1 F)) w g h Ha); tauto.
  - intros w g h Ha; simpl in Ha.
    change ((sat F w g /\ ~ extension_at (dom F) (update p F) w g) <->
      (sat F w h /\ ~ extension_at (dom F) (update p F) w h)).
    rewrite (HF w g h Ha), (extension_at_agree (dom F) (update p F) w g h Ha); tauto.
  - intros w g h Ha; simpl in Ha.
    change ((sat F w g /\ (extension_at (dom F) (update p1 F) w g \/ extension_at (dom F) (update p2 F) w g)) <->
      (sat F w h /\ (extension_at (dom F) (update p1 F) w h \/ extension_at (dom F) (update p2 F) w h))).
    rewrite (HF w g h Ha), (extension_at_agree (dom F) (update p1 F) w g h Ha),
      (extension_at_agree (dom F) (update p2 F) w g h Ha); tauto.
  - apply IHp; exact HF.
  - exact HF.
Qed.

Definition unary i (P : W -> D -> Prop) : Formula :=
  Atom 1 (i, tt) (fun w xs => P w (fst xs)).
Definition binary i j (P : W -> D -> D -> Prop) : Formula :=
  Atom 2 (i, (j, tt)) (fun w xs => P w (fst xs) (fst (snd xs))).
Definition closed_atom (P : W -> Prop) : Formula := Atom 0 tt (fun w _ => P w).
Definition indefinite i P := Mark false i (unary i P).
Definition definite i P := Mark true i (unary i P).

Theorem indefinite_felicity : forall i P F,
  licensed (indefinite i P) F <-> ~ dom F i.
Proof. intros; simpl; tauto. Qed.
Theorem definite_felicity : forall i P F,
  licensed (definite i P) F <->
  dom F i /\ (forall w g, sat F w g -> P w (g i)).
Proof. intros; unfold definite, unary, entails; simpl; firstorder. Qed.
Theorem fresh_indefinite_truth : forall F i P w,
  condition_B F -> ~ dom F i ->
  (world_content (update (indefinite i P) F) w <->
   world_content F w /\ exists x, P w x).
Proof.
  intros F i P w HB Hnew; split.
  - intros [g [HF HP]]; split; [exists g; exact HF | exists (g i); exact HP].
  - intros [[g HF] [x HP]]; exists (put g i x); split.
    + apply (proj2 (fresh_put F HB w g i x Hnew)); exact HF.
    + change (P w (put g i x i)); rewrite put_same; exact HP.
Qed.
Theorem descriptive_update_is_vacuous : forall F i P,
  licensed (definite i P) F -> file_equiv (update (definite i P) F) F.
Proof.
  intros F i P H; apply definite_felicity in H; destruct H as [Hi HP].
  split; simpl.
  - intros j; split; [intros [Hj | [E | []]]; [exact Hj | subst; exact Hi] | auto].
  - intros w g; split; [tauto | intro H; split; [exact H | apply HP; exact H]].
Qed.
Theorem introduction_licenses_anaphor : forall F i P,
  licensed (Use i) (update (indefinite i P) F).
Proof. intros; simpl; right; left; reflexivity. Qed.
Theorem negation_does_not_export : forall F p i,
  licensed (Use i) (update (Not p) F) <-> dom F i.
Proof. intros; reflexivity. Qed.
Theorem universal_does_not_export : forall F p q i,
  licensed (Use i) (update (Every p q) F) <-> dom F i.
Proof. intros; reflexivity. Qed.
Theorem disjunction_does_not_export : forall F p q i,
  licensed (Use i) (update (Or p q) F) <-> dom F i.
Proof. intros; reflexivity. Qed.
Theorem negation_projects_felicity : forall F p,
  licensed (Not p) F <-> licensed p F.
Proof. intros; reflexivity. Qed.
Theorem local_descriptive_projection : forall F i P,
  licensed (Seq (indefinite i P) (definite i P)) F <-> ~ dom F i.
Proof.
  intros F i P; simpl; unfold entails; simpl; firstorder.
Qed.

(* p.238 fn.21: constructive part. Recovering positive membership of an
   arbitrary predicate-valued domain uses a classical/decidability step. *)
Theorem nontrivial_entailment_not_not_familiar : forall F i P,
  condition_B F -> entails F (unary i P) ->
  (exists w g x, sat F w g /\ ~ P w x) -> ~ ~ dom F i.
Proof.
  intros F i P HB HE [w [g [x [HF Hnot]]]] Hnew.
  pose proof (proj2 (fresh_put F HB w g i x Hnew) HF) as Hput.
  specialize (HE w (put g i x) Hput); simpl in HE.
  destruct HE as [_ HP]; rewrite put_same in HP; contradiction.
Qed.

End Semantics.

Arguments fresh_put {W D} F _ w g i x _.
Arguments extension_at_agree {W D} d G w g h _.
Arguments universal_test_agree {W D} F R S w g h _.

Print Assumptions update_preserves_B.
Print Assumptions update_preserves_support.
Print Assumptions fresh_indefinite_truth.
Print Assumptions nontrivial_entailment_not_not_familiar.
