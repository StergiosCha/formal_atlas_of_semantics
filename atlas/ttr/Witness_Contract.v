(* A bounded comparison contract, not a TTR/MTT/Ranta equivalence.
   Sources rechecked 2026-09-25: Cooper 2023 pp. 11-14, A8-A9 pp. 404-406;
   CL20 pp. 15-16, 19-21; Ranta sections 2.11-2.12 and 2.16.
   See atlas_data/designs/ttr_mtt_ranta_contract_v0.md.

   The common carrier, equality and model-indexed predicates are ADDED
   comparison infrastructure. Type codes are not identified with extensions.
   MTT supports both weak exists and strong Sigma; the generic package layer
   below even permits Type-valued fibres. The TTR instance uses Prop-valued
   satisfaction. We do not infer native architectural identity from this
   re-encoding, or implement the source theories' complete type languages.

   All proofs are constructive. In particular we do not assume choice,
   functional extensionality, proof irrelevance or UIP. *)
Require Import List Bool.
Require ttr.TTR ttr.TTR_Model mtt_ranta.MTT mtt_ranta.Ranta.
Import ListNotations.

Module Packages.
Section CommonCarrier.
Variable W : Type.
Variables P Q : W -> Type.

Definition shared : Type := {w : W & (P w * Q w)%type}.
Definition independent : Type := ({w : W & P w} * {w : W & Q w})%type.

Definition split_shared (s : shared) : independent :=
  match s with
  | existT _ w (p, q) => (existT P w p, existT Q w q)
  end.

Definition aligned (u : independent) : Prop := projT1 (fst u) = projT1 (snd u).

Theorem split_aligned : forall s, aligned (split_shared s).
Proof. intros [w [p q]]; reflexivity. Qed.

Definition join_aligned (u : independent) (h : aligned u) : shared.
Proof.
  destruct u as [[x p] [y q]]; unfold aligned in h; cbn in h.
  destruct h; exact (existT _ x (p, q)).
Defined.

(* Canonical alignment proof on an actual split; not a choice of equality
   proofs for arbitrary packages, nor an equality of alignment-proof pairs. *)
Theorem join_split : forall s,
  join_aligned (split_shared s)
    (match s as z return aligned (split_shared z) with
     | existT _ w (p, q) => eq_refl
     end) = s.
Proof. intros [w [p q]]; reflexivity. Qed.

Theorem split_join : forall u h, split_shared (join_aligned u h) = u.
Proof.
  intros [[x p] [y q]] h; unfold aligned in h; cbn in h.
  destruct h; reflexivity.
Qed.

Theorem image_exactly_aligned : forall u,
  (exists s, split_shared s = u) <-> aligned u.
Proof.
  intros u; split.
  - intros [s <-]; apply split_aligned.
  - intros h; exists (join_aligned u h); apply split_join.
Qed.

Theorem join_preserves_left_witness : forall u h,
  projT1 (join_aligned u h) = projT1 (fst u).
Proof. intros [[x p] [y q]] h; unfold aligned in h; cbn in h; destruct h; reflexivity. Qed.

Theorem join_preserves_right_witness : forall u h,
  projT1 (join_aligned u h) = projT1 (snd u).
Proof. intros [[x p] [y q]] h; unfold aligned in h; cbn in h; destruct h; reflexivity. Qed.

Definition as_mtt (s : shared) :
  MTT.strong_package W (fun w => (P w * Q w)%type) := s.
Definition as_ranta (s : shared) :
  Ranta.some W (fun w => Ranta.rand (P w) (Q w)) := s.

Theorem strong_encodings_preserve_witness : forall s,
  projT1 (as_mtt s) = projT1 s /\ projT1 (as_ranta s) = projT1 s.
Proof. intros; split; reflexivity. Qed.
End CommonCarrier.

Section PropositionalObservation.
Variable W : Type.
Variables P Q : W -> Prop.

Theorem shared_truth : inhabited (shared W P Q) <->
  MTT.some W (fun w => P w /\ Q w).
Proof.
  split.
  - intros [[w [p q]]]; exists w; split; assumption.
  - intros [w [p q]]; constructor; exact (existT _ w (p, q)).
Qed.

Theorem independent_truth : inhabited (independent W P Q) <->
  MTT.some W P /\ MTT.some W Q.
Proof.
  split.
  - intros [[[x p] [y q]]]; split; [exists x | exists y]; assumption.
  - intros [[x p] [y q]]; constructor; exact (existT _ x p, existT _ y q).
Qed.
End PropositionalObservation.

Module Separation.
Definition P (w : bool) : Prop := w = true.
Definition Q (w : bool) : Prop := w = false.

Theorem independent_inhabited : inhabited (independent bool P Q).
Proof. constructor; exact (existT P true eq_refl, existT Q false eq_refl). Qed.

Theorem shared_empty : ~ inhabited (shared bool P Q).
Proof. intros [[w [p q]]]; unfold P in p; unfold Q in q; congruence. Qed.

Theorem no_total_recovery : ~ inhabited (independent bool P Q -> shared bool P Q).
Proof.
  intros [f]; destruct independent_inhabited as [u].
  apply shared_empty; constructor; exact (f u).
Qed.
End Separation.
End Packages.

Module Fragment.
(* Explicit object-language fragment: zero-argument ptypes and binary meet.
   No dependent records, type-of-types, variable type domains or subtyping. *)
Inductive code (Pred : Type) : Type :=
| atom : Pred -> code Pred
| meet : code Pred -> code Pred -> code Pred.
Arguments atom {Pred} _.
Arguments meet {Pred} _ _.

Section Semantics.
Variables D Base Pred : Type.

Fixpoint ttr_code (c : code Pred) : TTR.ty Base Pred :=
  match c with
  | atom p => TTR.TPty p []
  | meet a b => TTR.TMeet (ttr_code a) (ttr_code b)
  end.

Fixpoint sat (M : TTR_Model.model D Base Pred) (c : code Pred)
  (w : TTR.val D) : Prop :=
  match c with
  | atom p => TTR_Model.ptype_extension M p [] w
  | meet a b => sat M a w /\ sat M b w
  end.

Theorem ttr_adequacy : forall M c w,
  sat M c w <-> TTR_Model.typing M [] w (ttr_code c).
Proof. intros M c; induction c; intro w; cbn; [reflexivity | rewrite IHc1, IHc2; reflexivity]. Qed.

Definition mtt_realization M c := MTT.strong_some (TTR.val D) (sat M c).
Definition ranta_realization M c := Ranta.some (TTR.val D) (sat M c).
Definition ttr_realization M c :=
  {w : TTR.val D & TTR_Model.typing M [] w (ttr_code c)}.

Definition ttr_to_mtt M c (s : ttr_realization M c) : mtt_realization M c :=
  existT _ (projT1 s) (proj2 (ttr_adequacy M c (projT1 s)) (projT2 s)).
Definition mtt_to_ttr M c (s : mtt_realization M c) : ttr_realization M c :=
  existT _ (projT1 s) (proj1 (ttr_adequacy M c (projT1 s)) (projT2 s)).
Definition mtt_to_ranta M c (s : mtt_realization M c) : ranta_realization M c := s.
Definition ranta_to_mtt M c (s : ranta_realization M c) : mtt_realization M c := s.

Theorem ttr_mtt_carrier_roundtrips : forall M c,
  (forall s, projT1 (mtt_to_ttr M c (ttr_to_mtt M c s)) = projT1 s) /\
  (forall s, projT1 (ttr_to_mtt M c (mtt_to_ttr M c s)) = projT1 s).
Proof. intros; split; intros; reflexivity. Qed.

Theorem mtt_ranta_roundtrips : forall M c,
  (forall s, ranta_to_mtt M c (mtt_to_ranta M c s) = s) /\
  (forall s, mtt_to_ranta M c (ranta_to_mtt M c s) = s).
Proof. intros; split; intros; reflexivity. Qed.

Theorem inhabitation_preserved_and_reflected : forall M c,
  inhabited (ttr_realization M c) <-> MTT.some (TTR.val D) (sat M c).
Proof.
  intros M c; split.
  - intros [s]; exists (projT1 s); apply (proj2 (ttr_adequacy M c _)), (projT2 s).
  - intros [w h]; constructor; exact (mtt_to_ttr M c (existT _ w h)).
Qed.

Definition meet_package M a b (s : mtt_realization M (meet a b)) :
  Packages.shared (TTR.val D) (sat M a) (sat M b) :=
  match s with existT _ w (conj p q) => existT _ w (p, q) end.

Definition package_meet M a b
  (s : Packages.shared (TTR.val D) (sat M a) (sat M b)) :
  mtt_realization M (meet a b) :=
  existT _ (projT1 s) (conj (fst (projT2 s)) (snd (projT2 s))).

Theorem meet_compositional_at_witness : forall M a b w,
  sat M (meet a b) w <-> sat M a w /\ sat M b w.
Proof. reflexivity. Qed.

Theorem meet_package_roundtrips : forall M a b,
  (forall s, package_meet M a b (meet_package M a b s) = s) /\
  (forall s, meet_package M a b (package_meet M a b s) = s).
Proof. intros; split; intros [w [p q]]; reflexivity. Qed.

(* A specified compatibility condition on assignments and a witness map.
   It is not asserted for arbitrary changes of model. *)
Definition preserves (M N : TTR_Model.model D Base Pred)
  (f : TTR.val D -> TTR.val D) : Prop :=
  forall p w, TTR_Model.ptype_extension M p [] w ->
              TTR_Model.ptype_extension N p [] (f w).

Definition reflects (M N : TTR_Model.model D Base Pred)
  (f : TTR.val D -> TTR.val D) : Prop :=
  forall p w, TTR_Model.ptype_extension N p [] (f w) ->
              TTR_Model.ptype_extension M p [] w.

Theorem preservation_extends_to_meets : forall M N f,
  preserves M N f -> forall c w, sat M c w -> sat N c (f w).
Proof.
  intros M N f h c; induction c; intros w hw; cbn in *.
  - apply h; exact hw.
  - destruct hw; split; [apply IHc1 | apply IHc2]; assumption.
Qed.

Theorem reflection_extends_to_meets : forall M N f,
  reflects M N f -> forall c w, sat N c (f w) -> sat M c w.
Proof.
  intros M N f h c; induction c; intros w hw; cbn in *.
  - apply h; exact hw.
  - destruct hw; split; [apply IHc1 | apply IHc2]; assumption.
Qed.

Definition transport M N f (h : preserves M N f) c
  (s : mtt_realization M c) : mtt_realization N c :=
  existT _ (f (projT1 s))
    (preservation_extends_to_meets M N f h c (projT1 s) (projT2 s)).

Theorem transport_witness : forall M N f h c s,
  projT1 (transport M N f h c s) = f (projT1 s).
Proof. reflexivity. Qed.

Theorem identity_preserves : forall M, preserves M M (fun w => w).
Proof. intros M p w h; exact h. Qed.

Theorem composition_preserves : forall M N O f g,
  preserves M N f -> preserves N O g -> preserves M O (fun w => g (f w)).
Proof. intros M N O f g hf hg p w h; apply hg, hf, h. Qed.

(* Naturality at the carrier observation, NOT equality of proof packages. *)
Theorem transport_split_commutes_on_witnesses : forall M N f h a b s,
  let before := Packages.split_shared _ _ _ (meet_package M a b s) in
  let after := Packages.split_shared _ _ _
    (meet_package N a b (transport M N f h (meet a b) s)) in
  (projT1 (fst after), projT1 (snd after)) =
  (f (projT1 (fst before)), f (projT1 (snd before))).
Proof.
  intros M N f h a b [w [p q]]; cbn zeta; unfold transport; cbn [projT1 projT2].
  destruct (preservation_extends_to_meets M N f h (meet a b) w (conj p q)).
  reflexivity.
Qed.

Theorem reversible_transport_recovers_witness : forall M N f g hf hg,
  (forall w, g (f w) = w) -> forall c s,
  projT1 (transport N M g hg c (transport M N f hf c s)) = projT1 s.
Proof. intros M N f g hf hg h c s; apply h. Qed.

(* Reflection covers only the image of f. Surjectivity is an additional
   hypothesis for reflection of existence in the entire target carrier. *)
Theorem whole_carrier_inhabitation : forall M N f,
  preserves M N f -> reflects M N f ->
  (forall v, exists w, f w = v) -> forall c,
  (exists w, sat M c w) <-> (exists v, sat N c v).
Proof.
  intros M N f hp hr hs c; split.
  - intros [w h]; exists (f w); exact (preservation_extends_to_meets M N f hp c w h).
  - intros [v h]; destruct (hs v) as [w hw]; exists w.
    apply (reflection_extends_to_meets M N f hr c w); rewrite hw; exact h.
Qed.
End Semantics.

Module ModelSeparation.
Definition yes := TTR_Model.Countermodels.assignment true.
Definition no := TTR_Model.Countermodels.assignment false.

Theorem separating_models_admissible :
  TTR_Model.admissible bool bool bool (fun _ => []) yes /\
  TTR_Model.admissible bool bool bool (fun _ => []) no.
Proof. split; apply TTR_Model.Countermodels.assignments_admissible. Qed.

Theorem atomic_truth_agrees : forall p,
  (exists w, sat bool bool bool yes (atom p) w) <->
  (exists w, sat bool bool bool no (atom p) w).
Proof. intros; apply TTR_Model.Countermodels.erased_assignments_agree. Qed.

Theorem atomic_truth_agreement_not_meet_agreement :
  ~ (exists w, sat bool bool bool yes (meet (atom true) (atom false)) w) /\
  (exists w, sat bool bool bool no (meet (atom true) (atom false)) w).
Proof.
  split.
  - intros [w [[_ ht] [_ hf]]]; congruence.
  - exists (TTR.VBase false); cbn; repeat split; reflexivity.
Qed.

Theorem identity_does_not_preserve_assignment_change :
  ~ preserves bool bool bool yes no (fun w => w).
Proof.
  intros h.
  assert (hy : TTR_Model.ptype_extension yes true [] (TTR.VBase true))
    by (split; reflexivity).
  destruct (h true (TTR.VBase true) hy) as [_ bad]; discriminate.
Qed.
End ModelSeparation.
End Fragment.
