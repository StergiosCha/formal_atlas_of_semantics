Require Import DPL.
Require Import List Arith.
Import ListNotations.

(* ========================================================================== *)
(*  DRT_DPL.v — Discourse Representation Theory and its translation into DPL  *)
(*  FORMAL-ATLAS / atlas/dynamic                                               *)
(* ========================================================================== *)
(*
   SOURCES
     Kamp, H., van Genabith, J. & Reyle, U. (2011). Discourse Representation
       Theory.  In D. Gabbay & F. Guenthner (eds.), Handbook of Philosophical
       Logic, vol. 15.  Springer.  [DRS syntax: universe and conditions,
       complex conditions ¬, ⇒, ∨; verifying embeddings]
     Muskens, R. (1996). Combining Montague semantics and discourse
       representation.  Linguistics and Philosophy 19(2): 143–186.
       [a DRS read as a relation between assignments]
     Groenendijk, J. & Stokhof, M. (1991). Dynamic Predicate Logic.
       Linguistics and Philosophy 14(1): 39–100.  [the comparison with DRT:
       a box becomes existential quantification over its universe followed
       by dynamic conjunction of its conditions]
   Design document: atlas_data/designs/drt_dpl.md.
   Builds on DPL.v (models, assignments, the relational semantics [sem],
   truth, the donkey sentences), which this file leaves unchanged: DRT and
   DPL are interpreted in the same models.

   WHAT IS FORMALIZED
     Part 1  DRSs [u1 … un | γ1 … γm] with atomic, identity, ¬, ⇒ and ∨
             conditions, and an induction principle for the nested syntax.
     Part 2  Verification: g verifies K from f iff g differs from f at most
             on the universe of K and satisfies its conditions; truth.
     Part 3  The translation tr into DPL: a box becomes ∃u1…∃un(γ1 ∧ … ∧ γm).
               T1 verifies_same, csat_same   verification depends only on
                                             the values of assignments
               T4 dpl_to_drt, drt_to_dpl     tr is correct in both directions
               T4' drt_dpl_meaning           the same relation, exactly
               T5 drt_dpl_truth              truth is preserved
               cond_test                     every condition becomes a test
     Part 4  The donkey sentences as DRSs.  Their DRT truth conditions are
             proved directly, and agree with DPL.v's dk1 and dk2 through T5.
     Part 5  The converse direction fails for a naive translation:
             reading DPL conjunction as DRS merge is wrong when a variable
             is reused (merge_not_conj).

   NOT FORMALIZED (and why)
     * Accessibility as a syntactic relation between boxes: the relational
       semantics makes the antecedent's referents available in the
       consequent of ⇒ by construction, so no separate notion is needed.
     * A translation from DPL to DRT, with the side condition (no reuse of
       a variable already free in the left conjunct) under which merge is
       correct.  Only the counterexample without it is proved.
     * Duplex and proportional conditions, DRS construction from syntax.

   REPRESENTATION CHOICES
     A DRS universe is a list of variables, and the "differs at most on the
     universe" clause is stated pointwise.  DPL.v's tests return the input
     assignment itself, while a verifying embedding is only determined
     pointwise, so the exact equality of the two relations (T4') needs
     functional extensionality, as DPL.v's own dk1_meaning does.  T4 states
     the translation's correctness up to pointwise equality and uses no
     axioms; so does truth preservation (T5).
*)

(* ========================================================================== *)
(*  Part 1 — DRS syntax                                                        *)
(* ========================================================================== *)

Section Syntax.
Context {Σ : signature}.

(* A box: a universe of discourse referents and a list of conditions. *)
Inductive drs : Type :=
| Box : list Var -> list cond -> drs
with cond : Type :=
| CAtom : Pred Σ -> list (term Σ) -> cond
| CEq   : term Σ -> term Σ -> cond
| CNeg  : drs -> cond
| CImp  : drs -> drs -> cond
| COr   : drs -> drs -> cond.

(* Induction over the nested syntax: a box's conditions are a list. *)
Section Ind.
Variables (P : drs -> Prop) (Q : cond -> Prop).
Hypotheses
  (HBox  : forall us cs, Forall Q cs -> P (Box us cs))
  (HAtom : forall R ts, Q (CAtom R ts))
  (HEq   : forall t u, Q (CEq t u))
  (HNeg  : forall K, P K -> Q (CNeg K))
  (HImp  : forall K1 K2, P K1 -> P K2 -> Q (CImp K1 K2))
  (HOr   : forall K1 K2, P K1 -> P K2 -> Q (COr K1 K2)).

Fixpoint drs_ind' (K : drs) : P K :=
  match K with
  | Box us cs => HBox us cs
      ((fix go (cs : list cond) : Forall Q cs :=
          match cs with
          | [] => @Forall_nil _ Q
          | c :: cs => @Forall_cons _ Q c cs (cond_ind' c) (go cs)
          end) cs)
  end
with cond_ind' (c : cond) : Q c :=
  match c with
  | CAtom R ts => HAtom R ts
  | CEq t u => HEq t u
  | CNeg K => HNeg K (drs_ind' K)
  | CImp K1 K2 => HImp K1 K2 (drs_ind' K1) (drs_ind' K2)
  | COr K1 K2 => HOr K1 K2 (drs_ind' K1) (drs_ind' K2)
  end.

Lemma drs_cond_ind : (forall K, P K) /\ (forall c, Q c).
Proof. exact (conj drs_ind' cond_ind'). Qed.
End Ind.

(* Merging two boxes: union of universes and of conditions. *)
Definition merge (K1 K2 : drs) : drs :=
  match K1, K2 with Box us1 cs1, Box us2 cs2 => Box (us1 ++ us2) (cs1 ++ cs2) end.

End Syntax.

Arguments drs : clear implicits.
Arguments cond : clear implicits.

(* ========================================================================== *)
(*  Part 2 — Verification (verifying embeddings, read relationally)           *)
(* ========================================================================== *)

Fixpoint all_of {A} (p : A -> Prop) (l : list A) : Prop :=
  match l with [] => True | x :: l => p x /\ all_of p l end.

Section Semantics.
Context {Σ : signature} (M : model Σ).

(* Assignments with the same values. *)
Definition same (g h : G M) : Prop := forall v, g v = h v.

Lemma same_refl : forall g, same g g.
Proof. intros g v; reflexivity. Qed.

Lemma same_sym : forall g h, same g h -> same h g.
Proof. intros g h H v; symmetry; apply H. Qed.

(* g verifies K from f: g differs from f at most on the universe of K, and
   g satisfies every condition of K.  ¬K: no verifier from g; K1 ⇒ K2: every
   verifier of K1 from g extends to a verifier of K2; K1 ∨ K2: one of them
   has a verifier from g. *)
Fixpoint verifies (K : drs Σ) (f g : G M) {struct K} : Prop :=
  match K with
  | Box us cs => (forall v, ~ In v us -> g v = f v) /\ all_of (fun c => csat c g) cs
  end
with csat (c : cond Σ) (g : G M) {struct c} : Prop :=
  match c with
  | CAtom R ts => F_pred M R (map (tval M g) ts)
  | CEq t u => tval M g t = tval M g u
  | CNeg K => ~ exists h, verifies K g h
  | CImp K1 K2 => forall h, verifies K1 g h -> exists k, verifies K2 h k
  | COr K1 K2 => exists h, verifies K1 g h \/ verifies K2 g h
  end.

(* A DRS is true with respect to f iff it has a verifier from f. *)
Definition true_drs (K : drs Σ) (f : G M) : Prop := exists g, verifies K f g.

Lemma tval_same : forall g g' t, same g g' -> tval M g t = tval M g' t.
Proof. intros g g' [v|c] H; [apply H | reflexivity]. Qed.

(* T1.  Verification depends only on the values of the assignments. *)
Lemma verifies_csat_same :
  (forall K f f' g g', verifies K f g -> same f f' -> same g g' -> verifies K f' g') /\
  (forall c g g', csat c g -> same g g' -> csat c g').
Proof.
  apply drs_cond_ind.
  - intros us cs HQ f f' g g' [Hext Hc] Hf Hg; split.
    + intros v Hv; rewrite <- (Hg v), <- (Hf v); apply Hext; exact Hv.
    + clear Hext; induction HQ as [|c cs Hc0 _ IH]; [exact I|].
      destruct Hc as [H1 H2]; split; [exact (Hc0 _ _ H1 Hg) | exact (IH H2)].
  - intros R ts g g' H Hs; cbn in *.
    replace (map (tval M g') ts) with (map (tval M g) ts); [exact H|].
    apply map_ext; intro t; apply tval_same; exact Hs.
  - intros t u g g' H Hs; cbn in *.
    rewrite <- (tval_same _ _ t Hs), <- (tval_same _ _ u Hs); exact H.
  - intros K IH g g' Hn Hs [h Hh]; apply Hn; exists h.
    exact (IH _ _ _ _ Hh (same_sym _ _ Hs) (same_refl h)).
  - intros K1 K2 IH1 _ g g' H Hs h Hh.
    exact (H h (IH1 _ _ _ _ Hh (same_sym _ _ Hs) (same_refl h))).
  - intros K1 K2 IH1 IH2 g g' [h [Hh|Hh]] Hs; exists h; [left|right].
    + exact (IH1 _ _ _ _ Hh Hs (same_refl h)).
    + exact (IH2 _ _ _ _ Hh Hs (same_refl h)).
Qed.

Definition verifies_same := proj1 verifies_csat_same.
Definition csat_same := proj2 verifies_csat_same.

Lemma all_of_csat_same : forall cs g g',
  all_of (fun c => csat c g) cs -> same g g' -> all_of (fun c => csat c g') cs.
Proof.
  induction cs as [|c cs IH]; intros g g' H Hs; [exact I|].
  destruct H as [H1 H2]; split; [exact (csat_same _ _ _ H1 Hs) | exact (IH _ _ H2 Hs)].
Qed.

End Semantics.

(* ========================================================================== *)
(*  Part 3 — The translation into DPL                                          *)
(* ========================================================================== *)

Section Translation.
Context {Σ : signature}.

(* The empty box's body: a tautological test. *)
Definition dtrue : form Σ := Eq (TVar 0) (TVar 0).

(* ∃u1 … ∃un φ *)
Fixpoint exs (us : list Var) (φ : form Σ) : form Σ :=
  match us with [] => φ | u :: us => Ex u (exs us φ) end.

(* φ1 ∧ … ∧ φm, dynamic conjunction, right-nested. *)
Fixpoint conj_all (φs : list (form Σ)) : form Σ :=
  match φs with
  | [] => dtrue
  | [φ] => φ
  | φ :: φs => Conj φ (conj_all φs)
  end.

(* G&S 1991: [u1 … un | γ1 … γm] becomes ∃u1 … ∃un (γ1 ∧ … ∧ γm). *)
Fixpoint tr (K : drs Σ) : form Σ :=
  match K with Box us cs => exs us (conj_all (map tr_c cs)) end
with tr_c (c : cond Σ) : form Σ :=
  match c with
  | CAtom R ts => Atom R ts
  | CEq t u => Eq t u
  | CNeg K => Neg (tr K)
  | CImp K1 K2 => Impl (tr K1) (tr K2)
  | COr K1 K2 => Disj (tr K1) (tr K2)
  end.

Context (M : model Σ).

(* A box's body is a test that checks every condition. *)
Lemma conj_all_sem : forall cs,
  Forall (fun c => forall g h, sem M (tr_c c) g h <-> h = g /\ csat M c g) cs ->
  forall g h, sem M (conj_all (map tr_c cs)) g h <-> h = g /\ all_of (fun c => csat M c g) cs.
Proof.
  induction 1 as [|c cs Hc Hcs IH]; intros g h.
  - cbn; split; intros [-> _]; split; auto.
  - destruct cs as [|c' cs'].
    + cbn [map conj_all all_of]; rewrite Hc; split; intros [-> H]; auto.
      destruct H; auto.
    + change (sem M (conj_all (map tr_c (c :: c' :: cs'))) g h)
        with (exists k, sem M (tr_c c) g k /\ sem M (conj_all (map tr_c (c' :: cs'))) k h).
      split.
      * intros [k [Hk Hr]]; apply Hc in Hk as [-> H0]; apply IH in Hr as [-> Hr].
        split; [reflexivity | split; assumption].
      * intros [-> [H0 Hr]]; exists g; split.
        -- apply Hc; split; [reflexivity | exact H0].
        -- apply IH; split; [reflexivity | exact Hr].
Qed.

(* An output of ∃u1 … ∃un φ is an output of φ from some assignment that
   differs from the input at most on u1 … un. *)
Lemma exs_elim : forall us φ f h, sem M (exs us φ) f h ->
  exists k, (forall v, ~ In v us -> k v = f v) /\ sem M φ k h.
Proof.
  induction us as [|u us IH]; intros φ f h H.
  - exists f; split; [reflexivity | exact H].
  - destruct H as [k1 [Hd Hr]]; destruct (IH _ _ _ Hr) as [k [Hk Hs]].
    exists k; split; [|exact Hs]; intros v Hv.
    rewrite Hk by (intro; apply Hv; right; assumption).
    apply Hd; intro E; apply Hv; left; congruence.
Qed.

(* Conversely, ∃u1 … ∃un φ reaches (up to values) any assignment that
   differs from the input at most on u1 … un and from which φ succeeds. *)
Lemma exs_intro : forall us φ f g, (forall v, ~ In v us -> g v = f v) ->
  (forall k, same M g k -> exists h, sem M φ k h /\ same M g h) ->
  exists h, sem M (exs us φ) f h /\ same M g h.
Proof.
  induction us as [|u us IH]; intros φ f g Hext Hφ.
  - apply Hφ; intro v; apply Hext; intros [].
  - destruct (IH φ (upd f u (g u)) g) as [h [Hh Hs]].
    + intros v Hv; destruct (Nat.eq_dec v u) as [->|Hne]; [rewrite upd_eq; reflexivity|].
      rewrite upd_neq by exact Hne; apply Hext; intros [E|E]; [congruence | contradiction].
    + exact Hφ.
    + exists h; split; [|exact Hs]; exists (upd f u (g u)); split; [apply dif_upd | exact Hh].
Qed.

Lemma tr_correct :
  (forall K, (forall f g, sem M (tr K) f g -> verifies M K f g) /\
             (forall f g, verifies M K f g -> exists h, sem M (tr K) f h /\ same M g h)) /\
  (forall c g h, sem M (tr_c c) g h <-> h = g /\ csat M c g).
Proof.
  apply drs_cond_ind.
  - intros us cs HQ; pose proof (conj_all_sem cs HQ) as Hb; split.
    + intros f g H; apply exs_elim in H as [k [Hk Hs]].
      apply Hb in Hs as [-> Hc]; split; [exact Hk | exact Hc].
    + intros f g [Hext Hc]; apply exs_intro; [exact Hext|].
      intros k Hgk; exists k; split; [|exact Hgk].
      apply Hb; split; [reflexivity | exact (all_of_csat_same M _ _ _ Hc Hgk)].
  - intros R ts g h; split; intros [-> H]; split; auto.
  - intros t u g h; split; intros [-> H]; split; auto.
  - intros K [IHs IHc] g h; split.
    + intros [-> Hn]; split; [reflexivity|]; intros [k Hk].
      destruct (IHc _ _ Hk) as [k' [Hk' _]]; apply Hn; exists k'; exact Hk'.
    + intros [-> Hn]; split; [reflexivity|]; intros [k Hk].
      apply Hn; exists k; exact (IHs _ _ Hk).
  - intros K1 K2 [IH1s IH1c] [IH2s IH2c] g h; split.
    + intros [-> H]; split; [reflexivity|]; intros k Hk.
      destruct (IH1c _ _ Hk) as [k' [Hk' Hs]]; destruct (H k' Hk') as [j Hj].
      exists j; exact (verifies_same M _ _ _ _ _ (IH2s _ _ Hj) (same_sym M _ _ Hs) (same_refl M j)).
    + intros [-> H]; split; [reflexivity|]; intros k Hk.
      destruct (H k (IH1s _ _ Hk)) as [j Hj]; destruct (IH2c _ _ Hj) as [j' [Hj' _]].
      exists j'; exact Hj'.
  - intros K1 K2 [IH1s IH1c] [IH2s IH2c] g h; split.
    + intros [-> [k [Hk|Hk]]]; split; [reflexivity| |reflexivity|]; exists k.
      * left; exact (IH1s _ _ Hk).
      * right; exact (IH2s _ _ Hk).
    + intros [-> [k [Hk|Hk]]]; split; [reflexivity| |reflexivity|].
      * destruct (IH1c _ _ Hk) as [k' [Hk' _]]; exists k'; left; exact Hk'.
      * destruct (IH2c _ _ Hk) as [k' [Hk' _]]; exists k'; right; exact Hk'.
Qed.

(* T4 (DPL to DRT).  Every DPL output of tr K verifies K.  G&S 1991, the
   comparison with DRT; Muskens 1996 (boxes as relations). *)
Theorem dpl_to_drt : forall K f g, sem M (tr K) f g -> verifies M K f g.
Proof. intros K; exact (proj1 (proj1 tr_correct K)). Qed.

(* T4 (DRT to DPL).  Every verifier of K is, up to values, a DPL output of
   tr K.  Same sources. *)
Theorem drt_to_dpl : forall K f g, verifies M K f g ->
  exists h, sem M (tr K) f h /\ same M g h.
Proof. intros K; exact (proj2 (proj1 tr_correct K)). Qed.

(* Every condition translates to a DPL test (G&S 1991 Def. 11): conditions
   do not change the assignment. *)
Theorem cond_test : forall c g h, sem M (tr_c c) g h -> h = g /\ csat M c g.
Proof. intros c g h; apply (proj2 tr_correct). Qed.

(* T5.  A DRS is true iff its translation is true in DPL (Def. 3).
   Uses no axioms. *)
Theorem drt_dpl_truth : forall K f, true_drs M K f <-> true_wrt M (tr K) f.
Proof.
  intros K f; split.
  - intros [g Hg]; destruct (drt_to_dpl _ _ _ Hg) as [h [Hh _]]; exists h; exact Hh.
  - intros [g Hg]; exists g; exact (dpl_to_drt _ _ _ Hg).
Qed.

(* T4'.  The verification relation of K is exactly the DPL meaning of tr K.
   Needs functional extensionality (via DPL.assign_ext): DPL's output is
   determined as a function, the DRT verifier only by its values. *)
Theorem drt_dpl_meaning : forall K f g, verifies M K f g <-> sem M (tr K) f g.
Proof.
  intros K f g; split; [|apply dpl_to_drt].
  intros Hg; destruct (drt_to_dpl _ _ _ Hg) as [h [Hh Hs]].
  replace g with h; [exact Hh|]; apply assign_ext; intro v; symmetry; apply Hs.
Qed.

End Translation.

(* ========================================================================== *)
(*  Part 4 — The donkey sentences as DRSs                                      *)
(* ========================================================================== *)

Section Donkey.
Variables (Dm : Type) (d0 : Dm) (Fa Dk : Dm -> Prop) (Ow Bt : Dm -> Dm -> Prop).
Let Md := M_dk Dm d0 Fa Dk Ow Bt.

Definition c_farmer : cond Σ_dk := @CAtom Σ_dk farmer [TVar 0].
Definition c_donkey : cond Σ_dk := @CAtom Σ_dk donkey [TVar 1].
Definition c_own    : cond Σ_dk := @CAtom Σ_dk own [TVar 0; TVar 1].
Definition c_beat   : cond Σ_dk := @CAtom Σ_dk beat [TVar 0; TVar 1].

(* "A farmer owns a donkey.  He beats it." — the second sentence's
   conditions are added to the box built for the first, so the pronouns
   pick up x and y (KvGR 2011, DRS construction for discourse). *)
Definition K_dk1 : drs Σ_dk := Box [0; 1] [c_farmer; c_donkey; c_own; c_beat].

(* "If a farmer owns a donkey, he beats it." — [ | [x y | farmer x,
   donkey y, own x y] ⇒ [ | beat x y]]. *)
Definition K_dk2 : drs Σ_dk :=
  Box [] [CImp (Box [0; 1] [c_farmer; c_donkey; c_own]) (Box [] [c_beat])].

Lemma upd2_0 : forall (g : G Md) a b, upd (upd g 0 a) 1 b 0 = a.
Proof. intros; rewrite upd_neq by discriminate; apply upd_eq. Qed.

Lemma upd2_1 : forall (g : G Md) a b, upd (upd g 0 a) 1 b 1 = b.
Proof. intros; apply upd_eq. Qed.

Lemma upd2_out : forall (g : G Md) a b v, ~ In v [0; 1] -> upd (upd g 0 a) 1 b v = g v.
Proof.
  intros g a b v Hv; rewrite !upd_neq; [reflexivity | |];
    intro E; apply Hv; subst; cbn; auto.
Qed.

(* An assignment that differs from g at most on x, y and maps them to a, b. *)
Lemma two_refs : forall (g : G Md) a b, exists k : G Md,
  (forall v, ~ In v [0; 1] -> k v = g v) /\ k 0 = a /\ k 1 = b.
Proof.
  intros g a b; exists (upd (upd g 0 a) 1 b).
  split; [apply upd2_out | split; [apply upd2_0 | apply upd2_1]].
Qed.

(* The first sentence's DRS has the classical ∃∃ truth conditions. *)
Theorem drs_dk1_truth : forall g : G Md,
  true_drs Md K_dk1 g <-> exists a b, Fa a /\ Dk b /\ Ow a b /\ Bt a b.
Proof.
  intros g; split.
  - intros [h [_ [HF [HD [HO [HB _]]]]]]; exists (h 0), (h 1); auto.
  - intros [a [b [HF [HD [HO HB]]]]].
    destruct (two_refs g a b) as [k [Hk [H0 H1]]]; exists k; split; [exact Hk|].
    cbn; rewrite H0, H1; repeat split; assumption.
Qed.

(* The conditional's DRS has the ∀∀ truth conditions (KvGR 2011: the
   antecedent's referents are universally quantified through ⇒). *)
Theorem drs_dk2_truth : forall g : G Md,
  true_drs Md K_dk2 g <-> (forall a b, Fa a -> Dk b -> Ow a b -> Bt a b).
Proof.
  intros g; split.
  - intros [h [_ [Himp _]]] a b HF HD HO.
    destruct (two_refs h a b) as [k [Hk [H0 H1]]].
    assert (Hv : verifies Md (Box [0; 1] [c_farmer; c_donkey; c_own]) h k).
    { split; [exact Hk|]; cbn; rewrite H0, H1; repeat split; assumption. }
    destruct (Himp _ Hv) as [j [Hj [HB _]]]; cbn in HB.
    rewrite (Hj 0), (Hj 1), H0, H1 in HB by (intros []); exact HB.
  - intros Hall; exists g; split; [reflexivity|split; [|exact I]].
    intros k [_ [HF [HD [HO _]]]]; exists k; split; [reflexivity|split; [|exact I]].
    exact (Hall _ _ HF HD HO).
Qed.

(* Through T5, the translations have the truth conditions of DPL.v's
   donkey sentences dk1 ((1b), §2.3) and dk2 ((2b), §2.4). *)
Corollary tr_dk1_truth : forall g : G Md, true_wrt Md (tr K_dk1) g <-> true_wrt Md dk1 g.
Proof.
  intros g; rewrite <- drt_dpl_truth, drs_dk1_truth; symmetry; exact (dk1_truth Dm d0 Fa Dk Ow Bt g).
Qed.

Corollary tr_dk2_truth : forall g : G Md, true_wrt Md (tr K_dk2) g <-> true_wrt Md dk2 g.
Proof.
  intros g; rewrite <- drt_dpl_truth, drs_dk2_truth; symmetry; exact (dk2_truth Dm d0 Fa Dk Ow Bt g).
Qed.

End Donkey.

(* ========================================================================== *)
(*  Part 5 — Merge is not DPL conjunction                                      *)
(* ========================================================================== *)

(* [ | P x] and [x | Q x].  Their translations are Px and ∃x Qx. *)
Definition K_P : drs Σ_ex := Box [] [@CAtom Σ_ex Pe [TVar 0]].
Definition K_Q : drs Σ_ex := Box [0] [@CAtom Σ_ex Qe [TVar 0]].

Example tr_K_P : tr K_P = Px.
Proof. reflexivity. Qed.

Example tr_K_Q : tr K_Q = Ex 0 Qx.
Proof. reflexivity. Qed.

(* In DPL, Px ∧ ∃x Qx says that the old x is P and some new x is Q.  The
   merged box [x | P x, Q x] requires one x that is both.  In the model
   with P = {true} and Q = {false} the first is true and the second false,
   so a translation from DPL to DRT cannot read ∧ as merge when the right
   conjunct reuses a variable of the left. *)
Theorem merge_not_conj : exists g : G M_boolQ,
  true_wrt M_boolQ (Conj (tr K_P) (tr K_Q)) g /\ ~ true_drs M_boolQ (merge K_P K_Q) g.
Proof.
  exists (fun _ => true); split.
  - exists (upd (fun _ => true) 0 false), (fun _ => true); split.
    + split; reflexivity.
    + exists (upd (fun _ => true) 0 false); split; [apply dif_upd|].
      split; [reflexivity | exact (upd_eq _ (fun _ => true) 0 false)].
  - intros [h [_ [HP [HQ _]]]]; cbn in HP, HQ; congruence.
Qed.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Under Coq 8.20.1 (2026-11-15):
     "Closed under the global context" — every theorem except
       drt_dpl_meaning: the correctness of the translation up to values,
       truth preservation, and the donkey and merge results use no axioms.
     drt_dpl_meaning — functional_extensionality_dep only (DPL.v's
       assign_ext), for the reason given in the header. *)
Print Assumptions verifies_csat_same.
Print Assumptions dpl_to_drt.
Print Assumptions drt_to_dpl.
Print Assumptions cond_test.
Print Assumptions drt_dpl_truth.
Print Assumptions drs_dk1_truth.
Print Assumptions drs_dk2_truth.
Print Assumptions tr_dk1_truth.
Print Assumptions tr_dk2_truth.
Print Assumptions merge_not_conj.
Print Assumptions drt_dpl_meaning.
