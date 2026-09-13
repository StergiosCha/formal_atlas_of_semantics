(* ========================================================================== *)
(*  TTR.v — Type Theory with Records (Cooper)                                  *)
(*  FORMAL-ATLAS / atlas/ttr                                                   *)
(* ========================================================================== *)
(*
   SOURCES
     [CDLL15] Cooper, Dobnik, Lappin & Larsson (2015). "Probabilistic
       Type Theory and Natural Language Semantics", LiLT 10(4).  (PDF on
       disk: papers/probabilistic/.)  §2 pp. 17-18 is the official
       compact definition of dependent record types, cited by clause:
         (1) [] = Rec; r : Rec iff r is a record.
         (2) r : T1 ∪ {<l,T2>} iff r : T1, r.l is defined, and r.l : T2.
         (3) dependent field <l, <T, <pi_1..pi_n>>>: r.l : T(r.pi_1, ...,
             r.pi_n) — the arguments are PATHS resolved against the
             record r itself.
       Also p. 17: records are functional on labels; paths r.l1.l2...ln.
     [C23] Cooper (2023). From Perception to Communication. OUP.  (PDF on
       disk: papers/foundations/.)  §1.4.3.5 pp. 36-37: subtyping is
       SEMANTIC — "T1 ⊑ T2 just in case for any a, a : T1 implies
       a : T2, no matter what is assigned to the basic types and
       ptypes".  Appendix A2 systems of basic types; A3.1 predicates and
       ptypes; A8 meet types: "a : (T1 ∧ T2) iff a : T1 and a : T2";
       A11 records and record types; A11.3 the merge operation μ
       (main-text §~(102)-(106)): clauses 1-2 simplify (T1 ∧ T2) to T1
       when T1 ⊑ T2 (resp. T2), clause 3 merges labelled sets
       recursively, label-wise, keeping single-side fields.
   Design document: formalizing_formal_semantics/atlas/designs/ttr.md
     (Design B adopted there: deep labelled records; this file follows
     it, with one upgrade: instead of a PARTIAL meet returning option,
     the type language carries first-class meet types TMeet — [C23] A8
     verbatim — which makes the μ-merge total, as in [C23] A11.3.)

   WHAT IS FORMALIZED
     Part 1  Syntax: labels (nat), paths, types (basic, ptype with path
             arguments, meet, record type), values (base, record) —
             both nested inductives with association lists; size
             measures; boolean equality with reflect specs.
     Part 2  The typing judgement of_ty/of_rty, transcribing [CDLL15]
             clauses (1)-(3): field lookup, path resolution against the
             ambient record, witness-sensitive ptype membership; unfolding lemmas
             (Forall form) and judgement basics (empty type, cons,
             field access).
     Part 3  Subtyping.  Width subtyping sub_w (more fields = subtype)
             with soundness; the full syntactic subtyping boolean subb
             (depth + meets), reflexive, transitive, and SOUND for the
             semantic ⊑ of [C23] §1.4.3.5 — soundness is proved with
             the model (base_of, holds) universally quantified, which
             is exactly the "no matter what is assigned" clause.
     Part 4  Merge.  Cooper's μ ([C23] A11.3): subsumption clauses via
             subb, recursive label-wise merge on record types, TMeet
             fallback; THE meet theorem: r : μ(T1,T2) iff r : T1 and
             r : T2 ([C23] A8's condition, so the syntactic merge
             realizes the semantic meet).
     Part 5  Relabelling: an injective label renaming preserves the
             judgement when the model's ptype assignment respects it.
     Part 6  Worked examples over a concrete signature: the "a man
             runs" record type [x:Ind, c1:man(x), c2:run(x)] with a
             witness; the subtype chain [x,c1,c2] ⊑ [x,c1] ⊑ [x] by
             computation; a two-argument ptype (hug(x,y)) exercising
             path resolution; a merge computed by cbn.
     Part 7  A concrete subject check in the example model.  The general,
             model-indexed comparison lives in TTR_vs_MTT.v: it proves
             an inhabitation correspondence and loss of witness data,
             not an equivalence of TTR and MTT semantics.
     Companion TTR_Model.v: explicit assignments A/F, admissible arities,
             model families and countermodels separating coextension,
             identity, witness membership and mere inhabitation.

   NOT FORMALIZED (and why)
     * Function types and their (contravariant) subtyping, join types,
       singleton types, string/regular types ([C23] A4-A7, A13):
       STRETCH in the design; the record core stands alone.
     * General n-ary dependent types as lambda abstractions ([CDLL15]
       clause 3 allows any function to types): here dependent types are
       PTYPES (predicate + path arguments), the canonical case every
       worked TTR example uses.  μ's dependent-field clause (a)(i)
       concatenating argument lists is subsumed: two ptype fields merge
       to their TMeet, which has the same witnesses under A8.
     * Completeness of subb for semantic ⊑: subb is a sound syntactic
       approximation (it does not, e.g., derive [x] ∧ [c] ⊑ [x,c]
       without merging first).  [C23] works with the semantic notion;
       no semantic completeness or complete normalization is claimed.
     * Probabilistic TTR ([CDLL15] §3-4), stratification (A10), A9's
       varying Type_M domains (the companion treats a fixed syntax),
       ERec, polymorphic arities, and general dependent type functions.
     * Base types classify atoms here; ptypes may classify atoms or
       records.  Arguments terminate at atoms.  Source arity formation
       is represented only by the companion's admissible model condition.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   Labels are nat; record types and records are
                    association lists (nested inductives).  "Functional
                    on labels" ([CDLL15] p. 17) is the explicit
                    predicate wf_rty/wf_rec (NoDup on the label
                    projection), listed as a hypothesis exactly where a
                    theorem needs it.
     [ARTIFACT-ii]  Dependency by reference: ptype arguments are label
                    paths resolved against the ambient record — the
                    letter of [CDLL15] clause (3) (r.pi_i), not a
                    binding discipline.  Resolution is partial; a
                    failed resolution falsifies the judgement (matching
                    the "0 otherwise" of the probabilistic clauses).
     [ARTIFACT-iii] Ptype membership is holds(P, resolved args, witness).
                    These are object-language witnesses, possibly
                    records, not Coq proofs identified or discarded.
                    Propositional erasure occurs only in the explicitly
                    information-losing TTR_vs_MTT comparison.
     [ARTIFACT-iv]  The model (D, Base, Pred, base_of, holds) and the
                    decidable equalities on Base/Pred enter as Section
                    Variables/Hypotheses — zero axioms, zero global
                    Parameters; subtyping soundness therefore quantifies
                    over ALL models, which is [C23]'s "no matter what is
                    assigned".
     [ARTIFACT-v]   All structural inductions are size inductions (a
                    nat measure over the nested inductive), avoiding
                    hand-rolled mutual induction principles.
*)

Require Import List Arith Lia Bool Setoid.
Import ListNotations.

(* ========================================================================== *)
(*  Part 0 — Labels, paths, generic list equality                             *)
(* ========================================================================== *)

Definition label := nat.
Definition path := list label.   (* r.l1.l2...ln, [CDLL15] p. 17 *)

Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => eqb x y && list_eqb eqb xs' ys'
  | _, _ => false
  end.

Lemma list_eqb_spec {A : Type} (eqb : A -> A -> bool)
  (H : forall x y : A, reflect (x = y) (eqb x y)) :
  forall xs ys : list A, reflect (xs = ys) (list_eqb eqb xs ys).
Proof.
  induction xs as [|x xs' IH]; destruct ys as [|y ys']; cbn.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (H x y).
    + destruct (IH ys').
      * left; congruence.
      * right; congruence.
    + right; congruence.
Qed.

Definition path_eqb : path -> path -> bool := list_eqb Nat.eqb.
Definition args_eqb : list path -> list path -> bool := list_eqb path_eqb.

Lemma path_eqb_spec : forall p q : path, reflect (p = q) (path_eqb p q).
Proof. apply list_eqb_spec, Nat.eqb_spec. Qed.

Lemma args_eqb_spec : forall a b : list path, reflect (a = b) (args_eqb a b).
Proof. apply list_eqb_spec, path_eqb_spec. Qed.

Section TTR.

(* The model, as Section variables (ARTIFACT-iv): a flat domain of
   atoms, a set of basic types with their witness assignment ([C23]
   A2), and a witness assignment to ptypes ([C23] A3.2,
   ARTIFACT-iii).  The model is packaged explicitly in TTR_Model.v. *)
Variable D : Type.
Variable Base : Type.
Variable Pred : Type.
Variable base_of : D -> Base -> Prop.

(* ========================================================================== *)
(*  Part 1 — Types and values                                                 *)
(* ========================================================================== *)

(* Types: basic types, ptypes with path arguments ([CDLL15] clause 3),
   meet types ([C23] A8), record types as labelled association lists
   ([C23] A11). *)
Inductive ty : Type :=
| TBase : Base -> ty
| TPty  : Pred -> list path -> ty
| TMeet : ty -> ty -> ty
| TRec  : list (label * ty) -> ty.

Definition rty := list (label * ty).

(* Values: domain elements and records. *)
Inductive val : Type :=
| VBase : D -> val
| VRec  : list (label * val) -> val.

Definition rec := list (label * val).

(* Cooper 2023, A3.2(7-8), pp. 400-401: F assigns a SET OF WITNESSES
   to a ptype.  The candidate object is an argument of membership; a
   true predicate does not make every object a witness.  Witnesses may
   themselves be records (section 1.4.1, p. 19). *)
Variable holds : Pred -> list D -> val -> Prop.
Variable base_eqb : Base -> Base -> bool.
Variable pred_eqb : Pred -> Pred -> bool.
Hypothesis base_eqb_spec : forall a b, reflect (a = b) (base_eqb a b).
Hypothesis pred_eqb_spec : forall p q, reflect (p = q) (pred_eqb p q).

(* "Records are required to be functional on labels" ([CDLL15] p. 17);
   in record types, "l is a label not occurring in T1" (clause 2).  As
   association lists both are side predicates here (ARTIFACT-i). *)
Definition wf_rty (F : rty) : Prop := NoDup (map fst F).
Definition wf_rec (r : rec) : Prop := NoDup (map fst r).

(* ---- lookups ---- *)

Fixpoint rlookup (r : rec) (l : label) : option val :=
  match r with
  | [] => None
  | (l', v) :: r' => if Nat.eqb l' l then Some v else rlookup r' l
  end.

Fixpoint rty_lookup (F : rty) (l : label) : option ty :=
  match F with
  | [] => None
  | (l', T) :: F' => if Nat.eqb l' l then Some T else rty_lookup F' l
  end.

(* ---- path resolution ([CDLL15] p. 17: r.l1.l2...ln) ---- *)

Fixpoint resolve (v : val) (p : path) : option val :=
  match p with
  | [] => Some v
  | l :: p' => match v with
               | VRec r => match rlookup r l with
                           | Some v' => resolve v' p'
                           | None => None
                           end
               | VBase _ => None
               end
  end.

(* A ptype argument must come out at a domain element. *)
Definition resolve_arg (amb : rec) (p : path) : option D :=
  match resolve (VRec amb) p with
  | Some (VBase d) => Some d
  | _ => None
  end.

Fixpoint resolve_args (amb : rec) (ps : list path) : option (list D) :=
  match ps with
  | [] => Some []
  | p :: ps' => match resolve_arg amb p, resolve_args amb ps' with
                | Some d, Some ds => Some (d :: ds)
                | _, _ => None
                end
  end.

(* ---- size measures (ARTIFACT-v) ---- *)

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TBase _ => 1
  | TPty _ _ => 1
  | TMeet A B => S (ty_size A + ty_size B)
  | TRec F => S ((fix szF (F : rty) : nat :=
                    match F with
                    | [] => 0
                    | (_, T') :: F' => ty_size T' + szF F'
                    end) F)
  end.

Definition rty_size (F : rty) : nat :=
  (fix szF (F : rty) : nat :=
     match F with
     | [] => 0
     | (_, T') :: F' => ty_size T' + szF F'
     end) F.

Lemma ty_size_rec : forall F, ty_size (TRec F) = S (rty_size F).
Proof. reflexivity. Qed.

Lemma ty_size_pos : forall T, 0 < ty_size T.
Proof. destruct T; cbn; lia. Qed.

Lemma rty_size_cons : forall l T F,
  rty_size ((l, T) :: F) = ty_size T + rty_size F.
Proof. reflexivity. Qed.

Lemma rty_size_in : forall F l T, In (l, T) F -> ty_size T <= rty_size F.
Proof.
  induction F as [|[l' T'] F' IH]; intros l T HIn.
  - destruct HIn.
  - rewrite rty_size_cons; destruct HIn as [E | HIn].
    + injection E as -> ->; lia.
    + specialize (IH _ _ HIn); lia.
Qed.

Lemma rty_lookup_in : forall F l T, rty_lookup F l = Some T -> In (l, T) F.
Proof.
  induction F as [|[l' T'] F' IH]; cbn; intros l T H.
  - discriminate.
  - destruct (Nat.eqb_spec l' l).
    + injection H as ->; left; congruence.
    + right; apply IH, H.
Qed.

Lemma rty_lookup_size : forall F l T,
  rty_lookup F l = Some T -> ty_size T <= rty_size F.
Proof. intros F l T H; eapply rty_size_in, rty_lookup_in, H. Qed.

(* ========================================================================== *)
(*  Part 2 — The typing judgement ([CDLL15] §2 clauses (1)-(3))               *)
(* ========================================================================== *)

(* of_ty amb v T: v is of type T, ptype arguments resolved against the
   AMBIENT record amb.  For a record type checked against a record r,
   the ambient switches to r — the letter of clause (3), where the
   arguments are r.pi for the record r being judged. *)
Fixpoint of_ty (amb : rec) (v : val) (T : ty) {struct T} : Prop :=
  match T with
  | TBase b => match v with
               | VBase d => base_of d b
               | VRec _ => False
               end
  | TPty P args => match resolve_args amb args with
                   | Some ds => holds P ds v
                   | None => False        (* failed resolution falsifies:
                                             [CDLL15] "0 otherwise" *)
                   end
  | TMeet A B => of_ty amb v A /\ of_ty amb v B   (* [C23] A8, verbatim *)
  | TRec F => match v with
              | VRec r => (fix ofF (F : rty) : Prop :=
                             match F with
                             | [] => True                    (* clause (1) *)
                             | (l, T') :: F' =>
                                 match rlookup r l with      (* clause (2):
                                                                r.l defined *)
                                 | Some v' => of_ty r v' T'  (* r.l : T' *)
                                 | None => False
                                 end /\ ofF F'
                             end) F
              | VBase _ => False
              end
  end.

(* The record-type judgement: r : F.  Clause-faithful special case. *)
Definition of_rty (r : rec) (F : rty) : Prop := of_ty r (VRec r) (TRec F).

(* ---- unfolding lemmas: the judgement in Forall form ---- *)

Definition field_ok (r : rec) (lt : label * ty) : Prop :=
  exists v, rlookup r (fst lt) = Some v /\ of_ty r v (snd lt).

Lemma of_ty_rec_iff : forall amb r F,
  of_ty amb (VRec r) (TRec F) <-> Forall (field_ok r) F.
Proof.
  intros amb r F; induction F as [|[l T] F' IH]; cbn.
  - split; intro; [constructor | exact I].
  - split.
    + intros [Hf Hrest].
      destruct (rlookup r l) as [v'|] eqn:E; [|destruct Hf].
      constructor.
      * exists v'; split; [exact E | exact Hf].
      * apply IH, Hrest.
    + intros H; inversion H as [|? ? [v' [Hl Hv]] Hrest]; subst; cbn in *.
      rewrite Hl; split; [exact Hv | apply IH, Hrest].
Qed.

(* Note the ambient is discarded: a record type's fields are checked
   against the record itself. *)
Lemma of_rty_iff : forall r F, of_rty r F <-> Forall (field_ok r) F.
Proof. intros; apply of_ty_rec_iff. Qed.

(* TTR-J1.  Clause (1): everything (that is a record) is of the empty
   record type Rec. *)
Theorem of_rty_nil : forall r, of_rty r [].
Proof. intros r; apply of_rty_iff; constructor. Qed.

(* TTR-J2.  Clause (2) as an equivalence: adding a field. *)
Theorem of_rty_cons : forall r l T F,
  of_rty r ((l, T) :: F) <->
  (exists v, rlookup r l = Some v /\ of_ty r v T) /\ of_rty r F.
Proof.
  intros r l T F.
  rewrite !of_rty_iff.
  split.
  - intros H; inversion H; subst; split; assumption.
  - intros [Hf Hrest]; constructor; assumption.
Qed.

(* TTR-J3.  Field access: a well-typed record delivers a well-typed
   value at every declared label (via the FIRST declaration; with
   wf_rty there is exactly one). *)
Theorem of_rty_field : forall r F l T,
  of_rty r F -> rty_lookup F l = Some T ->
  exists v, rlookup r l = Some v /\ of_ty r v T.
Proof.
  intros r F l T H HL.
  rewrite of_rty_iff in H.
  rewrite Forall_forall in H.
  exact (H _ (rty_lookup_in _ _ _ HL)).
Qed.

(* TTR-J4.  Values at a label are unique — record projection r.l is a
   function ([CDLL15] p. 17 "functional on labels" is about SYNTAX;
   this is the corresponding fact about lookup). *)
Theorem rlookup_det : forall (r : rec) l v1 v2,
  rlookup r l = Some v1 -> rlookup r l = Some v2 -> v1 = v2.
Proof. intros r l v1 v2 H1 H2; congruence. Qed.


(* ========================================================================== *)
(*  Part 3 — Subtyping ([C23] §1.4.3.5, A8)                                    *)
(* ========================================================================== *)

(* ---- width subtyping: more fields = subtype ---- *)

(* TTR-S1.  sub_w F1 F2: every field declared by the SUPERTYPE F2 is
   declared by F1 with the same type — F1 says at least as much. *)
Definition sub_w (F1 F2 : rty) : Prop :=
  forall l T, rty_lookup F2 l = Some T -> rty_lookup F1 l = Some T.

Theorem sub_w_refl : forall F, sub_w F F.
Proof. intros F l T H; exact H. Qed.

Theorem sub_w_trans : forall F1 F2 F3,
  sub_w F1 F2 -> sub_w F2 F3 -> sub_w F1 F3.
Proof. intros F1 F2 F3 H12 H23 l T H; exact (H12 _ _ (H23 _ _ H)). Qed.

Lemma wf_rty_lookup : forall F l T,
  wf_rty F -> In (l, T) F -> rty_lookup F l = Some T.
Proof.
  induction F as [|[l' T'] F' IH]; intros l T Hwf HIn.
  - destruct HIn.
  - inversion Hwf as [|? ? Hnin Hnd]; subst; cbn.
    destruct HIn as [E | HIn].
    + injection E as -> ->; rewrite Nat.eqb_refl; reflexivity.
    + destruct (Nat.eqb_spec l' l) as [-> | Hne].
      * exfalso; apply Hnin.
        change l with (fst (l, T)); apply in_map, HIn.
      * apply IH; assumption.
Qed.

(* TTR-S2.  Width soundness — the TTR slogan: a record of the richer
   type is a record of the poorer one ([C23] §1.4.3.5's (53): dropping
   fields goes up).  wf_rty F2 is needed because the judgement checks
   every DECLARED field while sub_w speaks through lookup. *)
Theorem sub_w_sound : forall F1 F2 r,
  wf_rty F2 -> sub_w F1 F2 -> of_rty r F1 -> of_rty r F2.
Proof.
  intros F1 F2 r Hwf Hsub H1.
  apply of_rty_iff; apply Forall_forall; intros [l T] HIn.
  apply (of_rty_field r F1 l T H1).
  apply Hsub, wf_rty_lookup; assumption.
Qed.

(* ---- deep well-formedness: functional-on-labels, hereditarily ---- *)

Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | TBase _ => True
  | TPty _ _ => True
  | TMeet A B => wf_ty A /\ wf_ty B
  | TRec F => NoDup (map fst F) /\
              (fix wfF (F : rty) : Prop :=
                 match F with
                 | [] => True
                 | (_, T') :: F' => wf_ty T' /\ wfF F'
                 end) F
  end.

Lemma wf_ty_fields : forall F,
  (fix wfF (F : rty) : Prop :=
     match F with
     | [] => True
     | (_, T') :: F' => wf_ty T' /\ wfF F'
     end) F <-> Forall (fun lt => wf_ty (snd lt)) F.
Proof.
  induction F as [|[l T] F' IH]; cbn.
  - split; intros _; [constructor | exact I].
  - split.
    + intros [HT Hrest]; constructor; [exact HT | apply IH, Hrest].
    + intros H; inversion H; subst; split; [assumption | apply IH; assumption].
Qed.

Lemma wf_ty_rec_iff : forall F,
  wf_ty (TRec F) <-> wf_rty F /\ Forall (fun lt => wf_ty (snd lt)) F.
Proof.
  intros F; cbn; unfold wf_rty.
  destruct (wf_ty_fields F) as [A B].
  split; intros [H1 H2]; split;
    [exact H1 | exact (A H2) | exact H1 | exact (B H2)].
Qed.

(* ---- the syntactic subtyping boolean ---- *)

(* subb T1 T2: T1 is (syntactically) a subtype of T2.  Structural on the
   SUPERTYPE; meets on the left are handled by an inner descent.  Sound
   for [C23]'s semantic notion (subb_sound below); NOT complete — see
   the header.  Ptypes and basic types are invariant (equal or nothing:
   the model is abstract, so no other safe rule exists). *)
Fixpoint subb (T1 T2 : ty) {struct T2} : bool :=
  match T2 with
  | TMeet A B => subb T1 A && subb T1 B
  | TBase b2 =>
      (fix lft (T1 : ty) : bool :=
         match T1 with
         | TBase b1 => base_eqb b1 b2
         | TMeet A B => lft A || lft B
         | _ => false
         end) T1
  | TPty P2 a2 =>
      (fix lft (T1 : ty) : bool :=
         match T1 with
         | TPty P1 a1 => pred_eqb P1 P2 && args_eqb a1 a2
         | TMeet A B => lft A || lft B
         | _ => false
         end) T1
  | TRec F2 =>
      (fix lft (T1 : ty) : bool :=
         match T1 with
         | TRec F1 =>
             forallb (fun lt2 : label * ty =>
                        match lt2 with
                        | (l, T2') =>
                            match rty_lookup F1 l with
                            | Some T1' => subb T1' T2'
                            | None => false
                            end
                        end) F2
         | TMeet A B => lft A || lft B
         | _ => false
         end) T1
  end.

(* Unfolding equations — all definitional. *)
Lemma subb_meet_r : forall T1 A B,
  subb T1 (TMeet A B) = subb T1 A && subb T1 B.
Proof. reflexivity. Qed.

Lemma subb_meet_l_base : forall A B b,
  subb (TMeet A B) (TBase b) = subb A (TBase b) || subb B (TBase b).
Proof. reflexivity. Qed.

Lemma subb_meet_l_pty : forall A B P a,
  subb (TMeet A B) (TPty P a) = subb A (TPty P a) || subb B (TPty P a).
Proof. reflexivity. Qed.

Lemma subb_meet_l_rec : forall A B F,
  subb (TMeet A B) (TRec F) = subb A (TRec F) || subb B (TRec F).
Proof. reflexivity. Qed.

Lemma subb_rec_rec : forall F1 F2,
  subb (TRec F1) (TRec F2) =
  forallb (fun lt2 : label * ty =>
             match lt2 with
             | (l, T2') => match rty_lookup F1 l with
                           | Some T1' => subb T1' T2'
                           | None => false
                           end
             end) F2.
Proof. reflexivity. Qed.

(* Field-wise reading of record-record subtyping. *)
Lemma subb_rec_in : forall F1 F2 l T2',
  subb (TRec F1) (TRec F2) = true -> In (l, T2') F2 ->
  exists T1', rty_lookup F1 l = Some T1' /\ subb T1' T2' = true.
Proof.
  intros F1 F2 l T2' H HIn.
  rewrite subb_rec_rec in H; rewrite forallb_forall in H.
  specialize (H _ HIn); cbn in H.
  destruct (rty_lookup F1 l) as [T1'|]; [eauto | discriminate].
Qed.

Lemma subb_rec_intro : forall F1 F2,
  (forall l T2', In (l, T2') F2 ->
     exists T1', rty_lookup F1 l = Some T1' /\ subb T1' T2' = true) ->
  subb (TRec F1) (TRec F2) = true.
Proof.
  intros F1 F2 H.
  rewrite subb_rec_rec; rewrite forallb_forall; intros [l T2'] HIn.
  destruct (H _ _ HIn) as [T1' [HL Hs]]; rewrite HL; exact Hs.
Qed.

(* Meets on the left: either conjunct suffices. *)
Lemma subb_meet_l_mono : forall A B T2,
  subb A T2 = true \/ subb B T2 = true -> subb (TMeet A B) T2 = true.
Proof.
  intros A B T2; revert A B.
  induction T2; intros A B H.
  - rewrite subb_meet_l_base; destruct H as [H|H]; rewrite H;
      [reflexivity | apply orb_true_r].
  - rewrite subb_meet_l_pty; destruct H as [H|H]; rewrite H;
      [reflexivity | apply orb_true_r].
  - rewrite subb_meet_r in *.
    apply andb_true_iff; destruct H as [H|H];
      apply andb_true_iff in H; destruct H as [Ha Hb]; split.
    + apply IHT2_1; left; exact Ha.
    + apply IHT2_2; left; exact Hb.
    + apply IHT2_1; right; exact Ha.
    + apply IHT2_2; right; exact Hb.
  - rewrite subb_meet_l_rec; destruct H as [H|H]; rewrite H;
      [reflexivity | apply orb_true_r].
Qed.

(* TTR-S3.  Reflexivity — under hereditary well-formedness only: with a
   duplicated label in a nested record type, the checker sees the first
   declaration twice and subb T T can FAIL, which is why [CDLL15]'s
   definition of record types forbids duplicated labels outright. *)
Lemma subb_refl_size : forall n T,
  ty_size T <= n -> wf_ty T -> subb T T = true.
Proof.
  induction n as [|n IH]; intros T Hsz Hwf.
  - pose proof (ty_size_pos T); lia.
  - destruct T as [b | P a | A B | F].
    + cbn; destruct (base_eqb_spec b b); [reflexivity | congruence].
    + cbn; destruct (pred_eqb_spec P P) as [_|NE]; [|congruence].
      destruct (args_eqb_spec a a) as [_|NE]; [reflexivity | congruence].
    + cbn in Hsz; destruct Hwf as [HA HB].
      rewrite subb_meet_r; apply andb_true_iff; split;
        apply subb_meet_l_mono.
      * left; apply IH; [lia | exact HA].
      * right; apply IH; [lia | exact HB].
    + apply subb_rec_intro; intros l T2' HIn.
      apply wf_ty_rec_iff in Hwf; destruct Hwf as [Hnd Hall].
      exists T2'; split.
      * apply wf_rty_lookup; assumption.
      * apply IH.
        -- pose proof (rty_size_in F l T2' HIn).
           rewrite ty_size_rec in Hsz; lia.
        -- rewrite Forall_forall in Hall; exact (Hall _ HIn).
Qed.

Theorem subb_refl : forall T, wf_ty T -> subb T T = true.
Proof. intros T; apply (subb_refl_size (ty_size T)); lia. Qed.

(* TTR-S4.  Transitivity. *)
Lemma subb_trans_size : forall n T1 T2 T3,
  ty_size T1 + ty_size T2 + ty_size T3 <= n ->
  subb T1 T2 = true -> subb T2 T3 = true -> subb T1 T3 = true.
Proof.
  induction n as [|n IH]; intros T1 T2 T3 Hsz H12 H23.
  - pose proof (ty_size_pos T1); pose proof (ty_size_pos T3); lia.
  - destruct T3 as [b3 | P3 a3 | A3 B3 | F3].
    + (* T3 basic *)
      destruct T2 as [b2 | P2 a2 | A2 B2 | F2]; try discriminate H23.
      * cbn in H23; destruct (base_eqb_spec b2 b3) as [->|];
          [exact H12 | discriminate].
      * rewrite subb_meet_l_base in H23.
        rewrite subb_meet_r in H12; apply andb_true_iff in H12;
          destruct H12 as [HA HB].
        cbn in Hsz.
        apply orb_true_iff in H23; destruct H23 as [H23|H23];
          [apply (IH T1 A2) | apply (IH T1 B2)]; try (cbn; lia); assumption.
    + (* T3 ptype *)
      destruct T2 as [b2 | P2 a2 | A2 B2 | F2]; try discriminate H23.
      * cbn in H23; apply andb_true_iff in H23; destruct H23 as [Hp Ha].
        destruct (pred_eqb_spec P2 P3) as [->|]; [|discriminate].
        destruct (args_eqb_spec a2 a3) as [->|]; [exact H12 | discriminate].
      * rewrite subb_meet_l_pty in H23.
        rewrite subb_meet_r in H12; apply andb_true_iff in H12;
          destruct H12 as [HA HB].
        cbn in Hsz.
        apply orb_true_iff in H23; destruct H23 as [H23|H23];
          [apply (IH T1 A2) | apply (IH T1 B2)]; try (cbn; lia); assumption.
    + (* T3 meet *)
      rewrite subb_meet_r in H23; apply andb_true_iff in H23;
        destruct H23 as [HA HB].
      rewrite subb_meet_r; apply andb_true_iff; cbn in Hsz; split;
        [apply (IH T1 T2 A3) | apply (IH T1 T2 B3)]; try lia; assumption.
    + (* T3 record *)
      destruct T2 as [b2 | P2 a2 | A2 B2 | F2]; try discriminate H23.
      * (* T2 meet *)
        rewrite subb_meet_l_rec in H23.
        rewrite subb_meet_r in H12; apply andb_true_iff in H12;
          destruct H12 as [HA HB].
        cbn in Hsz.
        apply orb_true_iff in H23; destruct H23 as [H23|H23];
          [apply (IH T1 A2) | apply (IH T1 B2)]; try (cbn; lia); assumption.
      * (* T2 record: chase fields *)
        destruct T1 as [b1 | P1 a1 | A1 B1 | F1]; try discriminate H12.
        -- (* T1 meet *)
           rewrite subb_meet_l_rec in H12.
           apply orb_true_iff in H12; cbn in Hsz.
           apply subb_meet_l_mono.
           destruct H12 as [H12|H12];
             [left; apply (IH A1 (TRec F2)) | right; apply (IH B1 (TRec F2))];
             try (cbn; lia); assumption.
        -- (* T1 record *)
           apply subb_rec_intro; intros l T3' HIn3.
           destruct (subb_rec_in _ _ _ _ H23 HIn3) as [T2' [HL2 Hs23]].
           destruct (subb_rec_in _ _ _ _ H12 (rty_lookup_in _ _ _ HL2))
             as [T1' [HL1 Hs12]].
           exists T1'; split; [exact HL1|].
           apply (IH T1' T2' T3'); [| assumption | assumption].
           pose proof (rty_lookup_size _ _ _ HL1).
           pose proof (rty_lookup_size _ _ _ HL2).
           pose proof (rty_size_in _ _ _ HIn3).
           rewrite !ty_size_rec in Hsz; lia.
Qed.

Theorem subb_trans : forall T1 T2 T3,
  subb T1 T2 = true -> subb T2 T3 = true -> subb T1 T3 = true.
Proof.
  intros T1 T2 T3.
  apply (subb_trans_size (ty_size T1 + ty_size T2 + ty_size T3)); lia.
Qed.

(* TTR-S5.  SOUNDNESS for the semantic subtyping of [C23] §1.4.3.5.
   The model is a Section variable, so on discharge this reads: for
   EVERY assignment to the basic types and ptypes, every witness of T1
   is a witness of T2 — which is [C23]'s definition of T1 ⊑ T2,
   "no matter what is assigned". *)
Lemma subb_sound_size : forall n T1 T2 amb v,
  ty_size T1 + ty_size T2 <= n ->
  subb T1 T2 = true -> of_ty amb v T1 -> of_ty amb v T2.
Proof.
  induction n as [|n IH]; intros T1 T2 amb v Hsz Hs Hv.
  - pose proof (ty_size_pos T1); pose proof (ty_size_pos T2); lia.
  - destruct T2 as [b2 | P2 a2 | A2 B2 | F2].
    + (* basic *)
      destruct T1 as [b1 | P1 a1 | A1 B1 | F1]; try discriminate Hs.
      * cbn in Hs; destruct (base_eqb_spec b1 b2) as [->|];
          [exact Hv | discriminate].
      * rewrite subb_meet_l_base in Hs; cbn in Hv; cbn in Hsz.
        destruct Hv as [HA HB].
        apply orb_true_iff in Hs; destruct Hs as [Hs|Hs];
          [apply (IH A1 _ amb v) | apply (IH B1 _ amb v)];
          try (cbn; lia); assumption.
    + (* ptype *)
      destruct T1 as [b1 | P1 a1 | A1 B1 | F1]; try discriminate Hs.
      * cbn in Hs; apply andb_true_iff in Hs; destruct Hs as [Hp Ha].
        destruct (pred_eqb_spec P1 P2) as [->|]; [|discriminate].
        destruct (args_eqb_spec a1 a2) as [->|]; [exact Hv | discriminate].
      * rewrite subb_meet_l_pty in Hs; cbn in Hv; cbn in Hsz.
        destruct Hv as [HA HB].
        apply orb_true_iff in Hs; destruct Hs as [Hs|Hs];
          [apply (IH A1 _ amb v) | apply (IH B1 _ amb v)];
          try (cbn; lia); assumption.
    + (* meet *)
      rewrite subb_meet_r in Hs; apply andb_true_iff in Hs;
        destruct Hs as [HA HB].
      cbn in Hsz; cbn; split;
        [apply (IH T1 A2 amb v) | apply (IH T1 B2 amb v)];
        try lia; assumption.
    + (* record *)
      destruct T1 as [b1 | P1 a1 | A1 B1 | F1]; try discriminate Hs.
      * rewrite subb_meet_l_rec in Hs; cbn in Hv; cbn in Hsz.
        destruct Hv as [HA HB].
        apply orb_true_iff in Hs; destruct Hs as [Hs|Hs];
          [apply (IH A1 _ amb v) | apply (IH B1 _ amb v)];
          try (cbn; lia); assumption.
      * destruct v as [d | r]; [destruct Hv|].
        rewrite of_ty_rec_iff in Hv |- *.
        rewrite Forall_forall in Hv |- *.
        intros [l T2'] HIn2.
        destruct (subb_rec_in _ _ _ _ Hs HIn2) as [T1' [HL1 Hs']].
        destruct (Hv _ (rty_lookup_in _ _ _ HL1)) as [v' [Hlk Hv']].
        exists v'; split; [exact Hlk|].
        apply (IH T1' T2' r v'); [| assumption | assumption].
        pose proof (rty_lookup_size _ _ _ HL1).
        pose proof (rty_size_in _ _ _ HIn2).
        rewrite !ty_size_rec in Hsz; lia.
Qed.

Theorem subb_sound : forall T1 T2 amb v,
  subb T1 T2 = true -> of_ty amb v T1 -> of_ty amb v T2.
Proof.
  intros T1 T2 amb v.
  apply (subb_sound_size (ty_size T1 + ty_size T2)); lia.
Qed.

(* TTR-S6.  Width subtyping is a special case of subb (same types on
   shared fields), so it inherits everything above. *)
Theorem sub_w_subb : forall F1 F2,
  wf_ty (TRec F2) -> sub_w F1 F2 -> subb (TRec F1) (TRec F2) = true.
Proof.
  intros F1 F2 Hwf Hsub.
  apply wf_ty_rec_iff in Hwf; destruct Hwf as [Hnd Hall].
  apply subb_rec_intro; intros l T2' HIn.
  exists T2'; split.
  - apply Hsub, wf_rty_lookup; assumption.
  - apply subb_refl; rewrite Forall_forall in Hall; exact (Hall _ HIn).
Qed.

(* ========================================================================== *)
(*  Part 4 — Merge: Cooper's μ ([C23] A11.3, main text (102)-(106))            *)
(* ========================================================================== *)

Definition labelb_in (l : label) (F : rty) : bool :=
  match rty_lookup F l with Some _ => true | None => false end.

(* μ, transcribed: clauses 1-2 are the subsumption tests (via the sound
   syntactic subb — [C23] states them with semantic ⊑); clause 3 merges
   record types label-wise, recursing on shared labels and keeping
   single-side fields ((103) in the text); everything else falls back to
   the meet type, which A8 gives the right witnesses by definition. *)
Fixpoint merge_ty (T1 T2 : ty) {struct T1} : ty :=
  if subb T1 T2 then T1
  else if subb T2 T1 then T2
  else match T1, T2 with
       | TRec F1, TRec F2 =>
           TRec (map (fun lt1 : label * ty =>
                        match lt1 with
                        | (l, T1') =>
                            (l, match rty_lookup F2 l with
                                | Some T2' => merge_ty T1' T2'
                                | None => T1'
                                end)
                        end) F1
                 ++ filter (fun lt2 : label * ty =>
                              negb (labelb_in (fst lt2) F1)) F2)
       | _, _ => TMeet T1 T2
       end.

Lemma merge_unfold : forall T1 T2,
  merge_ty T1 T2 =
  if subb T1 T2 then T1
  else if subb T2 T1 then T2
  else match T1, T2 with
       | TRec F1, TRec F2 =>
           TRec (map (fun lt1 : label * ty =>
                        match lt1 with
                        | (l, T1') =>
                            (l, match rty_lookup F2 l with
                                | Some T2' => merge_ty T1' T2'
                                | None => T1'
                                end)
                        end) F1
                 ++ filter (fun lt2 : label * ty =>
                              negb (labelb_in (fst lt2) F1)) F2)
       | _, _ => TMeet T1 T2
       end.
Proof. destruct T1; reflexivity. Qed.

(* TTR-M1.  μ clause 1 in action: merging a type with itself gives it
   back (subsumption fires; hereditary wf per TTR-S3). *)
Theorem merge_idem : forall T, wf_ty T -> merge_ty T T = T.
Proof.
  intros T Hwf; rewrite merge_unfold, (subb_refl T Hwf); reflexivity.
Qed.

(* TTR-M2.  THE MEET THEOREM: the syntactic merge has exactly the meet
   type's witnesses — a : μ(T1,T2) iff a : T1 and a : T2, which is
   [C23] A8's defining condition.  wf is needed on T2 only (a duplicated
   shared label in F2 would be silently dropped by the label-wise
   merge). *)
Lemma merge_sound_size : forall n T1 T2 amb v,
  ty_size T1 + ty_size T2 <= n -> wf_ty T2 ->
  (of_ty amb v (merge_ty T1 T2) <-> of_ty amb v T1 /\ of_ty amb v T2).
Proof.
  induction n as [|n IH]; intros T1 T2 amb v Hsz Hwf.
  - pose proof (ty_size_pos T1); pose proof (ty_size_pos T2); lia.
  - rewrite merge_unfold.
    destruct (subb T1 T2) eqn:E1.
    { split; [intros H1 | tauto].
      split; [exact H1 | exact (subb_sound _ _ _ _ E1 H1)]. }
    destruct (subb T2 T1) eqn:E2.
    { split; [intros H2 | tauto].
      split; [exact (subb_sound _ _ _ _ E2 H2) | exact H2]. }
    destruct T1 as [b1 | P1 a1 | A1 B1 | F1];
      destruct T2 as [b2 | P2 a2 | A2 B2 | F2];
      try (cbn; tauto).
    (* TRec / TRec *)
    destruct v as [d | r].
    { cbn; tauto. }
    apply wf_ty_rec_iff in Hwf; destruct Hwf as [Hnd Hall].
    rewrite Forall_forall in Hall.
    rewrite !ty_size_rec in Hsz.
    rewrite !of_ty_rec_iff.
    rewrite Forall_app, Forall_map, !Forall_forall.
    split.
    + intros [HM HF]; split.
      * (* recover F1 *)
        intros [l T1'] In1.
        specialize (HM _ In1); cbn in HM.
        destruct (rty_lookup F2 l) as [T2'|] eqn:E2'; [|exact HM].
        destruct HM as [v' [Hlk Hv']].
        assert (Hs' : ty_size T1' + ty_size T2' <= n).
        { pose proof (rty_size_in _ _ _ In1).
          pose proof (rty_lookup_size _ _ _ E2'); lia. }
        assert (Hw' : wf_ty T2')
          by exact (Hall _ (rty_lookup_in _ _ _ E2')).
        destruct (IH T1' T2' r v' Hs' Hw') as [IHf _].
        destruct (IHf Hv') as [Ha _].
        exists v'; split; [exact Hlk | exact Ha].
      * (* recover F2 *)
        intros [l T2'] In2.
        destruct (rty_lookup F1 l) as [T1s|] eqn:E1s.
        -- pose proof (rty_lookup_in _ _ _ E1s) as In1.
           specialize (HM _ In1); cbn in HM.
           rewrite (wf_rty_lookup F2 l T2' Hnd In2) in HM.
           destruct HM as [v' [Hlk Hv']].
           assert (Hs' : ty_size T1s + ty_size T2' <= n).
           { pose proof (rty_lookup_size _ _ _ E1s).
             pose proof (rty_size_in _ _ _ In2); lia. }
           assert (Hw' : wf_ty T2') by exact (Hall _ In2).
           destruct (IH T1s T2' r v' Hs' Hw') as [IHf _].
           destruct (IHf Hv') as [_ Hb].
           exists v'; split; [exact Hlk | exact Hb].
        -- apply HF; apply filter_In; split; [exact In2|].
           cbn; unfold labelb_in; rewrite E1s; reflexivity.
    + intros [H1 H2]; split.
      * (* build the merged F1 fields *)
        intros [l T1'] In1; cbn.
        specialize (H1 _ In1).
        destruct (rty_lookup F2 l) as [T2'|] eqn:E2'; [|exact H1].
        destruct H1 as [v' [Hlk Hv1]]; cbn in Hlk.
        pose proof (rty_lookup_in _ _ _ E2') as In2.
        destruct (H2 _ In2) as [v'' [Hlk2 Hv2]]; cbn in Hlk2.
        assert (v'' = v') by congruence; subst v''.
        assert (Hs' : ty_size T1' + ty_size T2' <= n).
        { pose proof (rty_size_in _ _ _ In1).
          pose proof (rty_lookup_size _ _ _ E2'); lia. }
        assert (Hw' : wf_ty T2') by exact (Hall _ In2).
        destruct (IH T1' T2' r v' Hs' Hw') as [_ IHb].
        exists v'; split; [exact Hlk | apply IHb; split; assumption].
      * (* build the filtered F2 fields *)
        intros lt HInf.
        apply filter_In in HInf; destruct HInf as [In2 _].
        exact (H2 _ In2).
Qed.

Theorem merge_sound : forall T1 T2 amb v, wf_ty T2 ->
  (of_ty amb v (merge_ty T1 T2) <-> of_ty amb v T1 /\ of_ty amb v T2).
Proof.
  intros T1 T2 amb v.
  apply (merge_sound_size (ty_size T1 + ty_size T2)); lia.
Qed.

(* TTR-M3.  The meet theorem in record-type judgement notation. *)
Corollary merge_rec_sound : forall F1 F2 r, wf_ty (TRec F2) ->
  (of_ty r (VRec r) (merge_ty (TRec F1) (TRec F2)) <->
   of_rty r F1 /\ of_rty r F2).
Proof. intros F1 F2 r Hwf; unfold of_rty; apply merge_sound, Hwf. Qed.

(* ========================================================================== *)
(*  Part 5 — Relabelling                                                       *)
(* ========================================================================== *)
(*  An injective renaming applies throughout fields and argument paths.
    Invariance in the same model additionally requires holds_rename:
    A3.2 allows assignments that distinguish structured witnesses. *)

Section Relabel.

Variable sigma : label -> label.
Hypothesis sigma_inj : forall a b : label, sigma a = sigma b -> a = b.

Fixpoint rename_ty (T : ty) : ty :=
  match T with
  | TBase b => TBase b
  | TPty P args => TPty P (map (map sigma) args)
  | TMeet A B => TMeet (rename_ty A) (rename_ty B)
  | TRec F => TRec (map (fun lt : label * ty =>
                           match lt with
                           | (l, T') => (sigma l, rename_ty T')
                           end) F)
  end.

Fixpoint rename_val (v : val) : val :=
  match v with
  | VBase d => VBase d
  | VRec r => VRec (map (fun lv : label * val =>
                           match lv with
                           | (l, v') => (sigma l, rename_val v')
                           end) r)
  end.

Definition rename_rec (r : rec) : rec :=
  map (fun lv : label * val =>
         match lv with (l, v') => (sigma l, rename_val v') end) r.

Definition rename_rty (F : rty) : rty :=
  map (fun lt : label * ty =>
         match lt with (l, T') => (sigma l, rename_ty T') end) F.

(* Relabelling RECORD witnesses need not preserve an arbitrary F.
   This condition states exactly when the SAME model is invariant.
   Atomic witnesses are unchanged; structured witnesses require this
   explicit compatibility.  It is discharged as a theorem premise. *)
Hypothesis holds_rename : forall P ds v,
  holds P ds (rename_val v) <-> holds P ds v.

Lemma rename_val_rec : forall r, rename_val (VRec r) = VRec (rename_rec r).
Proof. reflexivity. Qed.

Lemma rename_ty_rec : forall F, rename_ty (TRec F) = TRec (rename_rty F).
Proof. reflexivity. Qed.

Lemma rlookup_rename : forall r l,
  rlookup (rename_rec r) (sigma l) = option_map rename_val (rlookup r l).
Proof.
  induction r as [|[l' v'] r' IH]; intros l; cbn.
  - reflexivity.
  - destruct (Nat.eqb_spec l' l) as [-> | Hne].
    + rewrite Nat.eqb_refl; reflexivity.
    + destruct (Nat.eqb_spec (sigma l') (sigma l)) as [E | _].
      * exfalso; exact (Hne (sigma_inj _ _ E)).
      * apply IH.
Qed.

Lemma resolve_rename : forall p v,
  resolve (rename_val v) (map sigma p) = option_map rename_val (resolve v p).
Proof.
  induction p as [|l p' IH]; intros v; cbn.
  - reflexivity.
  - destruct v as [d | r]; cbn; [reflexivity|].
    rewrite rlookup_rename.
    destruct (rlookup r l) as [v'|]; cbn; [apply IH | reflexivity].
Qed.

Lemma resolve_arg_rename : forall amb p,
  resolve_arg (rename_rec amb) (map sigma p) = resolve_arg amb p.
Proof.
  intros amb p; unfold resolve_arg.
  change (VRec (rename_rec amb)) with (rename_val (VRec amb)).
  rewrite resolve_rename.
  destruct (resolve (VRec amb) p) as [[d | r'] |]; reflexivity.
Qed.

Lemma resolve_args_rename : forall amb args,
  resolve_args (rename_rec amb) (map (map sigma) args) = resolve_args amb args.
Proof.
  induction args as [|p args' IH]; cbn.
  - reflexivity.
  - rewrite resolve_arg_rename, IH; reflexivity.
Qed.

(* TTR-R1.  Invariance under injective, model-compatible relabelling. *)
Lemma rename_sound_size : forall n T amb v,
  ty_size T <= n ->
  (of_ty (rename_rec amb) (rename_val v) (rename_ty T) <-> of_ty amb v T).
Proof.
  induction n as [|n IH]; intros T amb v Hsz.
  - pose proof (ty_size_pos T); lia.
  - destruct T as [b | P a | A B | F].
    + destruct v as [d | r]; cbn; tauto.
    + cbn [rename_ty of_ty].
      rewrite resolve_args_rename.
      destruct (resolve_args amb a); [apply holds_rename | tauto].
    + cbn in Hsz; cbn [rename_ty of_ty].
      assert (HA := IH A amb v ltac:(lia)).
      assert (HB := IH B amb v ltac:(lia)).
      tauto.
    + destruct v as [d | r]; [cbn; tauto|].
      rewrite rename_val_rec, rename_ty_rec.
      rewrite !of_ty_rec_iff.
      unfold rename_rty; rewrite Forall_map, !Forall_forall.
      rewrite ty_size_rec in Hsz.
      split.
      * intros H [l T'] HIn.
        specialize (H _ HIn); unfold field_ok in H; cbn [fst snd] in H.
        destruct H as [v' [Hlk Hv']].
        rewrite rlookup_rename in Hlk.
        destruct (rlookup r l) as [v0|] eqn:E0; [|discriminate].
        cbn in Hlk; injection Hlk as <-.
        assert (Hs' : ty_size T' <= n)
          by (pose proof (rty_size_in _ _ _ HIn); lia).
        exists v0; split; [exact E0|].
        exact (proj1 (IH T' r v0 Hs') Hv').
      * intros H [l T'] HIn.
        specialize (H _ HIn); unfold field_ok in H |- *; cbn [fst snd] in H |- *.
        destruct H as [v0 [Hlk Hv0]].
        exists (rename_val v0); split.
        -- rewrite rlookup_rename, Hlk; reflexivity.
        -- assert (Hs' : ty_size T' <= n)
             by (pose proof (rty_size_in _ _ _ HIn); lia).
           exact (proj2 (IH T' r v0 Hs') Hv0).
Qed.

Theorem rename_sound : forall T amb v,
  of_ty (rename_rec amb) (rename_val v) (rename_ty T) <-> of_ty amb v T.
Proof. intros T amb v; apply (rename_sound_size (ty_size T)); lia. Qed.

(* TTR-R2.  At the record-type level. *)
Theorem of_rty_rename : forall r F,
  of_rty (rename_rec r) (rename_rty F) <-> of_rty r F.
Proof.
  intros r F; unfold of_rty.
  rewrite <- rename_ty_rec, <- rename_val_rec.
  apply rename_sound.
Qed.

End Relabel.

End TTR.

Arguments TBase {Base Pred} _.
Arguments TPty {Base Pred} _ _.
Arguments TMeet {Base Pred} _ _.
Arguments TRec {Base Pred} _.
Arguments VBase {D} _.
Arguments VRec {D} _.
Arguments rlookup {D} r l.
Arguments rty_lookup {Base Pred} F l.

(* ========================================================================== *)
(*  Part 6 — Worked examples over a concrete signature                        *)
(* ========================================================================== *)

Module Examples.

Inductive ExD : Set := d_john | d_mary.
Inductive ExB : Set := b_ind.
Inductive ExP : Set := p_man | p_run | p_hug.

Definition exb_eqb (a b : ExB) : bool := true.
Lemma exb_eqb_spec : forall a b : ExB, reflect (a = b) (exb_eqb a b).
Proof. intros [] []; left; reflexivity. Qed.

Definition exp_eqb (p q : ExP) : bool :=
  match p, q with
  | p_man, p_man | p_run, p_run | p_hug, p_hug => true
  | _, _ => false
  end.
Lemma exp_eqb_spec : forall p q : ExP, reflect (p = q) (exp_eqb p q).
Proof.
  intros [] []; cbn; ((left; reflexivity) || (right; discriminate)).
Qed.

Definition ex_base_of (d : ExD) (b : ExB) : Prop := True.
Definition ex_holds (p : ExP) (ds : list ExD) (v : val ExD) : Prop :=
  match p, ds with
  | p_man, [d] => d = d_john /\ v = VBase d_john
  | p_run, [d] => d = d_john /\ v = VBase d_john
  | p_hug, [a; b] => a = d_john /\ b = d_mary /\ v = VBase d_john
  | _, _ => False
  end.

(* The model pinned once. *)
Definition OF (r : rec ExD) (F : rty ExB ExP) : Prop :=
  of_rty ExD ExB ExP ex_base_of ex_holds r F.
Definition SUBB : ty ExB ExP -> ty ExB ExP -> bool :=
  subb ExB ExP exb_eqb exp_eqb.
Definition MERGE : ty ExB ExP -> ty ExB ExP -> ty ExB ExP :=
  merge_ty ExB ExP exb_eqb exp_eqb.

Definition l_x : label := 0.
Definition l_y : label := 1.
Definition l_c1 : label := 2.
Definition l_c2 : label := 3.
Definition l_e : label := 4.

(* The running example of the TTR literature: a man runs —
   [x : Ind, c1 : man(x), c2 : run(x)] ([CDLL15] §2, [C23] ch. 1). *)
Definition man_runs : rty ExB ExP :=
  [(l_x, TBase b_ind);
   (l_c1, TPty p_man [[l_x]]);
   (l_c2, TPty p_run [[l_x]])].

Definition john_rec : rec ExD :=
  [(l_x, VBase d_john); (l_c1, VBase d_john); (l_c2, VBase d_john)].

(* TTR-E1.  The witness judgement, fully computed: field lookup, path
   resolution, ptype checks. *)
Theorem man_runs_witness : OF john_rec man_runs.
Proof. cbv; repeat split; reflexivity. Qed.

(* TTR-E2.  The subtype chain [x,c1,c2] ⊑ [x,c1] ⊑ [x], by computation,
   and its strictness. *)
Theorem chain_1 :
  SUBB (TRec man_runs)
       (TRec [(l_x, TBase b_ind); (l_c1, TPty p_man [[l_x]])]) = true.
Proof. reflexivity. Qed.

Theorem chain_2 :
  SUBB (TRec [(l_x, TBase b_ind); (l_c1, TPty p_man [[l_x]])])
       (TRec [(l_x, TBase b_ind)]) = true.
Proof. reflexivity. Qed.

Theorem chain_strict :
  SUBB (TRec [(l_x, TBase b_ind)]) (TRec man_runs) = false.
Proof. reflexivity. Qed.

(* TTR-E3.  The chain semantically, through soundness: every man-runs
   record is an [x : Ind] record. *)
Theorem chain_semantic : forall r,
  OF r man_runs -> OF r [(l_x, TBase b_ind)].
Proof.
  intros r H.
  apply (subb_sound ExD ExB ExP ex_base_of ex_holds exb_eqb exp_eqb
           exb_eqb_spec exp_eqb_spec (TRec man_runs));
    [reflexivity | exact H].
Qed.

(* TTR-E4.  A two-argument ptype exercising path resolution:
   [x : Ind, y : Ind, e : hug(x,y)]. *)
Definition hug_rty : rty ExB ExP :=
  [(l_x, TBase b_ind); (l_y, TBase b_ind);
   (l_e, TPty p_hug [[l_x]; [l_y]])].

Theorem hug_dependent :
  OF [(l_x, VBase d_john); (l_y, VBase d_mary); (l_e, VBase d_john)]
     hug_rty.
Proof. cbv; repeat split; reflexivity. Qed.

(* TTR-E5.  Failed path resolution falsifies the judgement
   (ARTIFACT-ii): without the y field, hug(x,y) cannot check. *)
Theorem hug_missing_arg :
  ~ OF [(l_x, VBase d_john); (l_e, VBase d_john)] hug_rty.
Proof. cbv; intros [_ [F _]]; exact F. Qed.

(* TTR-E6.  A merge, computed: disjoint labels concatenate ([C23]
   (103)). *)
Theorem merge_example :
  MERGE (TRec [(l_x, TBase b_ind)]) (TRec [(l_c1, TPty p_man [[l_x]])])
  = TRec [(l_x, TBase b_ind); (l_c1, TPty p_man [[l_x]])].
Proof. reflexivity. Qed.

(* TTR-E7.  ... and its semantic content, an instance of the meet
   theorem: the merged type has exactly the conjunction of witnesses. *)
Theorem merge_example_semantic : forall r,
  OF r [(l_x, TBase b_ind); (l_c1, TPty p_man [[l_x]])] <->
  OF r [(l_x, TBase b_ind)] /\ OF r [(l_c1, TPty p_man [[l_x]])].
Proof.
  intros r.
  assert (W : wf_ty ExB ExP (TRec [(l_c1, TPty p_man [[l_x]])])).
  { cbn; split; [constructor; [intros [] | constructor] | split; exact I]. }
  exact (merge_rec_sound ExD ExB ExP ex_base_of ex_holds exb_eqb exp_eqb
           exb_eqb_spec exp_eqb_spec
           [(l_x, TBase b_ind)] [(l_c1, TPty p_man [[l_x]])] r W).
Qed.

(* ========================================================================== *)
(*  Part 7 — Concrete subject check (legacy example names)                    *)
(* ========================================================================== *)
(*  MTT/Ranta render "a man runs" as a strong sum (mtt_ranta.MTT's
    guarded quantification, mtt_ranta.Ranta's some/Sigma):
    { d : D | man d /\ run d }.  On this fragment the TTR record type
    man_runs has the same witnesses, constructively in both directions —
    a local example only.  This model explicitly assigns the individual
    itself as each ptype witness; this is not imposed on other models.
    See TTR_vs_MTT.v for the general, model-indexed erasure result. *)

Definition mtt_man_runs : Type :=
  { d : ExD | ex_holds p_man [d] (VBase d) /\
              ex_holds p_run [d] (VBase d) }.

Definition to_rec (d : ExD) : rec ExD :=
  [(l_x, VBase d); (l_c1, VBase d); (l_c2, VBase d)].

(* TTR-H1.  Strong-sum witness -> record witness. *)
Theorem mtt_to_ttr : forall s : mtt_man_runs,
  OF (to_rec (proj1_sig s)) man_runs.
Proof.
  intros [d H]; destruct d; cbv in *; intuition congruence.
Qed.

(* Computation helper: a one-argument ptype field checks exactly its
   predicate at the value the path finds. *)
Lemma of_ty_pty1 : forall (r : rec ExD) (v : val ExD) (P : ExP)
                          (l : label) (d : ExD),
  rlookup r l = Some (VBase d) ->
  (of_ty ExD ExB ExP ex_base_of ex_holds r v (TPty P [[l]]) <->
   ex_holds P [d] v).
Proof.
  intros r v P l d E; cbn.
  try unfold resolve_arg; cbn; rewrite E; cbn; tauto.
Qed.

(* TTR-H2.  Record witness -> strong-sum witness, COMPUTABLY: the
   individual is extracted through the decidable field lookup, so no
   choice principle and no Prop-to-Type escape is involved; the exists
   in the judgement is only opened once the goal is a Prop. *)
Theorem ttr_to_mtt : forall r : rec ExD, OF r man_runs ->
  { d : ExD | rlookup r l_x = Some (VBase d) /\
              ex_holds p_man [d] (VBase d) /\
              ex_holds p_run [d] (VBase d) }.
Proof.
  intros r H.
  assert (H' : of_rty ExD ExB ExP ex_base_of ex_holds r man_runs)
    by exact H.
  destruct (rlookup r l_x) as [[d | rr] |] eqn:E.
  - exists d; split; [reflexivity|].
    destruct (of_rty_field _ _ _ _ _ r man_runs l_c1
                (TPty p_man [[l_x]]) H' eq_refl) as [v1 [E1 H1]].
    destruct (of_rty_field _ _ _ _ _ r man_runs l_c2
                (TPty p_run [[l_x]]) H' eq_refl) as [v2 [E2 H2]].
    rewrite (of_ty_pty1 r v1 p_man l_x d E) in H1.
    rewrite (of_ty_pty1 r v2 p_run l_x d E) in H2.
    cbn in H1; destruct H1 as [-> _]; cbn; repeat split; reflexivity.
  - exfalso.
    destruct (of_rty_field _ _ _ _ _ r man_runs l_x
                (TBase b_ind) H' eq_refl) as [vx [Ex Hx]].
    rewrite E in Ex; injection Ex as Ex2; subst vx.
    exact Hx.
  - exfalso.
    destruct (of_rty_field _ _ _ _ _ r man_runs l_x
                (TBase b_ind) H' eq_refl) as [vx [Ex Hx]].
    rewrite E in Ex; discriminate Ex.
Qed.

(* TTR-H3.  Round trip on the individual. *)
Theorem hook_roundtrip : forall s : mtt_man_runs,
  rlookup (to_rec (proj1_sig s)) l_x = Some (VBase (proj1_sig s)).
Proof. intros [d Hd]; reflexivity. Qed.

End Examples.

(* ========================================================================== *)
(*  Part 8 — Assumption audit                                                  *)
(* ========================================================================== *)
(* Expected under Coq 8.20.1: every theorem below prints "Closed under
   the global context" — zero axioms, zero Parameters (ARTIFACT-iv). *)
Print Assumptions of_rty_nil.
Print Assumptions of_rty_cons.
Print Assumptions of_rty_field.
Print Assumptions rlookup_det.
Print Assumptions sub_w_refl.
Print Assumptions sub_w_trans.
Print Assumptions sub_w_sound.
Print Assumptions subb_refl.
Print Assumptions subb_trans.
Print Assumptions subb_sound.
Print Assumptions sub_w_subb.
Print Assumptions merge_idem.
Print Assumptions merge_sound.
Print Assumptions merge_rec_sound.
Print Assumptions rename_sound.
Print Assumptions of_rty_rename.
Print Assumptions Examples.man_runs_witness.
Print Assumptions Examples.chain_1.
Print Assumptions Examples.chain_2.
Print Assumptions Examples.chain_strict.
Print Assumptions Examples.chain_semantic.
Print Assumptions Examples.hug_dependent.
Print Assumptions Examples.hug_missing_arg.
Print Assumptions Examples.merge_example.
Print Assumptions Examples.merge_example_semantic.
Print Assumptions Examples.mtt_to_ttr.
Print Assumptions Examples.ttr_to_mtt.
Print Assumptions Examples.hook_roundtrip.
