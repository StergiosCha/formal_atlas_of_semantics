(* Prospective P3 pilot, paper 4. Davidson 1967 pp.81-83,92-93 (17)-(20).
   Action verbs have an event argument, not a neo-Davidsonian decomposition
   into separate thematic roles. Modifiers share that event. Deliberately
   and reference-class-sensitive slowly are EXCLUDED as on p.82.
   The modifier-list syntax is added finite machinery; the source schema
   is retained for each list. No theory of intention or event identity. *)
Require Import List.
Import ListNotations.

Section Events.
Variables Individual Event : Type.
Variable action : Individual -> Individual -> Event -> Prop.
Definition reading agent object (mods : list (Event -> Prop)) :=
  exists e, action agent object e /\ Forall (fun p => p e) mods.

Theorem drop_modifiers : forall agent object keep full,
  incl keep full -> reading agent object full -> reading agent object keep.
Proof.
  intros agent object keep full Hin [e [Ha Hmods]]; exists e; split; [exact Ha |].
  apply Forall_forall; intros p Hp; apply (proj1 (Forall_forall _ _) Hmods).
  apply Hin; exact Hp.
Qed.

Theorem drop_all_modifiers : forall agent object mods,
  reading agent object mods -> exists e, action agent object e.
Proof. intros agent object mods [e [Ha _]]; exists e; exact Ha. Qed.

Theorem equal_names_substitute : forall agent object other mods,
  object = other -> reading agent object mods -> reading agent other mods.
Proof. intros agent object other mods E; subst; auto. Qed.

(* Pp.82-83: the same buttering is in the bathroom, with a knife,
   and at midnight. Dropping the last two descriptions is licensed. *)
Theorem buttering_example : forall j toast bathroom knife midnight,
  reading j toast [bathroom; knife; midnight] -> reading j toast [bathroom].
Proof.
  intros; eapply drop_modifiers; [|eassumption].
  intros p [E | []]; subst; simpl; auto.
Qed.
End Events.

(* P.81: separate existentials do NOT recover a shared event. Two
   butterings can satisfy different modifiers without either having both. *)
Theorem separate_events_not_shared :
  let action := fun (_ _ : unit) (_ : bool) => True in
  let bathroom := fun e : bool => e = true in
  let midnight := fun e : bool => e = false in
  reading unit bool action tt tt [bathroom] /\
  reading unit bool action tt tt [midnight] /\
  ~ reading unit bool action tt tt [bathroom; midnight].
Proof.
  cbn; split.
  - exists true; split; [exact I | repeat constructor].
  - split.
    + exists false; split; [exact I | repeat constructor].
    + intros [e [_ H]]; inversion H; subst; inversion H3; subst; discriminate.
Qed.
