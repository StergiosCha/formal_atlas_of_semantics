(* ========================================================================== *)
(*  TTR.v — Type Theory with Records (Cooper)                                  *)
(*  FORMAL-ATLAS / atlas/ttr                                                   *)
(* ========================================================================== *)
(*
   *** WORK IN PROGRESS — checkpoint of 2026-09-06 ***
   Built and compiling: Parts 0-2 (syntax, sizes, the of_ty/of_rty
   judgement with unfolding lemmas and basics TTR-J1..J4) and Part 3
   through width subtyping (sub_w_refl/trans/sound), deep
   well-formedness (wf_ty), the subtyping boolean subb with its
   definitional unfolding equations, field-wise reading
   (subb_rec_in/intro), and subb_meet_l_mono.
   Pending (see the Part plan below and designs/ttr.md):
     subb_refl (needs wf_ty; size induction), subb_trans (size
     induction on the summed measure), subb_sound (the [C23] §1.4.3.5
     semantic soundness — size induction, uses of_ty_rec_iff +
     subb_rec_in), sub_w_subb; Part 4 merge (μ) + merge_sound; Part 5
     relabelling; Part 6 examples; Part 7 MTT hook; Part 8 audit block.
   Deliberately NOT in _CoqProject, no record, no claims.lock entries
   until complete — nothing here is counted by the atlas yet.

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
             ambient record, proof-irrelevant ptypes; unfolding lemmas
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
             judgement in both directions.
     Part 6  Worked examples over a concrete signature: the "a man
             runs" record type [x:Ind, c1:man(x), c2:run(x)] with a
             witness; the subtype chain [x,c1,c2] ⊑ [x,c1] ⊑ [x] by
             computation; a two-argument ptype (hug(x,y)) exercising
             path resolution; a merge computed by cbn.
     Part 7  The MTT hook (for the future ttr__mtt edge): on the
             fragment, witnesses of the man-runs record type correspond
             to MTT-style strong-sum witnesses {d : D | man d /\ run d}
             — both directions, with round-trip on the individual.

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
       decidable completeness would require μ-normalization first —
       merge_sound + subb after merge covers the record-type case.
     * Probabilistic TTR ([CDLL15] §3-4), stratification (A10), modal
       systems of types (A9).
     * The intensional distinction between ptype witnesses: of_ty for
       a ptype checks that the ptype HOLDS (proof-irrelevantly); see
       ARTIFACT-iii.

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
     [ARTIFACT-iii] Ptypes are proof-irrelevant: the field's witness is
                    required to EXIST (r.l defined) but its identity is
                    ignored; what is checked is holds(P, resolved
                    args).  TTR's proof objects for ptypes are opaque
                    here.
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

Require Import List Arith Lia Bool.
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
   objects, a set of basic types with their witness assignment ([C23]
   A2), predicates with proof-irrelevant inhabitation ([C23] A3.1,
   ARTIFACT-iii). *)
Variable D : Type.
Variable Base : Type.
Variable Pred : Type.
Variable base_of : D -> Base -> Prop.
Variable holds : Pred -> list D -> Prop.
Variable base_eqb : Base -> Base -> bool.
Variable pred_eqb : Pred -> Pred -> bool.
Hypothesis base_eqb_spec : forall a b, reflect (a = b) (base_eqb a b).
Hypothesis pred_eqb_spec : forall p q, reflect (p = q) (pred_eqb p q).

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
                   | Some ds => holds P ds
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

End TTR.

