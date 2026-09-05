(* ========================================================================== *)
(*  InqB.v — Basic Inquisitive Semantics (propositional InqB)                 *)
(*  FORMAL-ATLAS / atlas/inquisitive                                          *)
(* ========================================================================== *)
(*
   SOURCES
     [CGR18] Ciardelli, I., Groenendijk, J. & Roelofsen, F. (2018).
       Inquisitive Semantics. OUP.  [chs. 2–4: Defs 2.1–2.24, Facts 2.14,
       2.18–2.19, 2.23, 2.25; Facts 3.1–3.5, Defs 3.6–3.13, Facts 3.7,
       3.10, 3.12, 3.14–3.15; Defs 4.2–4.11, Facts 4.4, 4.8, 4.10,
       4.12–4.19]  (printed pages; PDF page = printed + 13)
     [R13]  Roelofsen, F. (2013). Algebraic foundations for the semantic
       treatment of inquisitive content. Synthese 190: 79–102.
       [Defs 1–12, Facts 2–15, Thms 1–3]
     [CR11] Ciardelli, I. & Roelofsen, F. (2011). Inquisitive logic.
       JPL 40: 55–94 (author manuscript).  [§2, §3, App. A: Defs 2.1–2.3,
       2.9, 2.13–2.15, 3.1, 3.5; Props 2.4–2.6, 2.12, 2.18–2.25, 3.2–3.4,
       3.6–3.10; Remark 3.8; Thm 3.34, Cor 3.35, Thm 5.5 soundness]
     [C16]  Ciardelli, I. (2016). Questions in Logic. PhD dissertation,
       ILLC Amsterdam.  [Defs 2.1.1, 2.1.3, 2.2.2, 2.4.1; Props 2.2.3,
       2.2.7–2.2.9, 2.4.3, 2.5.5–2.5.6, 2.5.16–2.5.17, 2.5.21;
       Cor 2.5.11]  (printed pages; PDF page = printed + 18)
   Design document: formalizing_formal_semantics/atlas/designs/inqb.md.

   WHAT IS FORMALIZED  (propositional InqB over an arbitrary logical space)
     Part 1  Syntax: formulas p | bot | /\ | \/ | -> over an arbitrary Atom
             type; Neg/Bang/Quest as notations; the or-free fragment;
             uniform substitution (for the substitution-failure result).
     Part 2  Information states over an arbitrary W : Type; enhancement
             (sub); propositions as non-empty downward-closed sets of
             states; info, truth, informative/inquisitive, alternatives,
             greatest elements; entailment as inclusion (T1–T7).
     Part 3  The algebra: binary and arbitrary (family) meets and joins,
             relative pseudo-complement pimp, absolute pseudo-complement
             pstar, the Heyting laws packaged as a record; only top and
             bottom have Boolean complements (T8–T13).
     Part 4  Projections pbang / pquest, decision sets, uniqueness of the
             issue-/info-cancelling maps, division P = !P /\ ?P,
             !P vs P** (T14–T20).
     Part 5  Support semantics: support as a Fixpoint, persistence, the
             empty-state property, [[phi]] is a proposition, the singleton
             collapse to classical truth, pointwise negation, the
             truth-conditional-antecedent lemma, info = truth set
             (T22–T30).
     Part 6  The algebraic recursion alg (CGR18 Def 4.3) and the
             coincidence theorem alg f = sem f (Leibniz!, R13 Fact 7);
             the five clause equations; [[phi -> psi]] is the relative
             pseudo-complement (T24–T26).
     Part 7  Sentence-level notions: assertions = truth-conditional
             sentences, questions, hybrids; !phi and ?phi; division;
             syntactic sufficient conditions; the or-free fragment is
             truth-conditional (T31–T41).
     Part 8  Entailment, validity, deduction theorem, disjunction
             property (per model), InqL <= CPL, DNE valid iff
             truth-conditional, LEM characterisation (T42–T52).
     Part 9  Soundness of KP^n = IPL(9 schemes) + KP + atomic ~~p -> p,
             with MP only, per model and over all models; consistency
             (T59–T62).
     Part 10 Countermodels over W2 = bool and W4 = bool*bool: LEM fails,
             DNE fails for ?p and for p\/q, p\/q is hybrid with two
             incomparable alternatives, atomic DNE is valid but not
             closed under uniform substitution (T54–T58).

   NOT FORMALIZED (and why)
     * First-order InqB (CGR18 Def 4.3(6-7), C16 ch. 4): out of scope.
     * Contexts and update (CGR18 §2.5), compliance (R13 §3.9): out of scope.
     * Completeness (CR11 Thm 3.34 <=; T70 of the design): needs the
       resolution machinery at the derivation level plus classical
       completeness of the or-free fragment (Kalmar/Lindenbaum, several
       hundred lines).  Route documented at the end of the file; a
       separate file if ever attempted.
     * Facts that genuinely need finiteness (CGR18 Facts 2.8, 2.17 "=>",
       CR11 Prop 2.10 normality): the sources flag this themselves
       (CGR18 fn. 6 p. 25); only the general directions appear here.
     * STRETCH items of the design (resolutions/normal form, disjoint-
       union models, decision procedure, Kripke correspondence,
       extensional epilogue): dropped for budget; the MUST list is
       complete.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   support cannot be an Inductive relation: the -> clause
                    has support in negative position (strict positivity).
                    It is a Fixpoint on the formula into Prop; every
                    metatheorem is by induction on syntax, matching the
                    sources' "induction on the complexity of phi".
     [ARTIFACT-ii]  Issues, propositions, decision sets and powersets are
                    all the one type iprop W := state W -> Prop with the
                    side predicate is_prop; membership s in [[phi]] and
                    support s |= phi are literally the same Prop, which is
                    why R13 Fact 7 (alg_eq_sem) holds by reflexivity in
                    every clause.
     [ARTIFACT-iii] support quantifies over all substates; nothing
                    computes.  Countermodels are by explicit substates and
                    worlds, never vm_compute.  empty s (a predicate)
                    replaces s = emptyset.
     [ARTIFACT-iv]  No Heyting/lattice classes in the stdlib: is_glb,
                    is_lub, is_rpc, greatest, alt are hand-rolled;
                    the Heyting algebra is a bespoke record over the
                    extensional equality peq.  Equations between
                    propositions are peq/seq, never Leibniz — EXCEPT the
                    five clause equations sem_atom .. sem_imp, which hold
                    by reflexivity.
     [ARTIFACT-v]   Decidability reversed: with the (faithful, C16
                    Def 2.1.1) Boolean valuation V : W -> Atom -> bool the
                    whole MUST list is axiom-free.  Residual EM appears
                    only for ABSTRACT propositions in T17/T20, isolated in
                    the hypothesis decided_info P and discharged for every
                    [[phi]] by decided_info_sem.
     Classical logic and extensionality are not used anywhere: see the
     Print Assumptions block at the end (13 theorems, all "Closed under
     the global context").
*)

From Coq Require Import Bool Setoid List.
Import ListNotations.

(* ========================================================================== *)
(*  Part 1 — Syntax                                                           *)
(* ========================================================================== *)

Section Syntax.

Variable Atom : Type.

(* D1.  Formulas of L_P: CR11 §2 p. 3; C16 Def 2.1.2 + §2.2 (inquisitive
   disjunction is the primitive \/); R13 §3.3. *)
Inductive form : Type :=
| FAtom : Atom -> form
| FBot  : form
| FAnd  : form -> form -> form
| FOr   : form -> form -> form
| FImp  : form -> form -> form.

(* D3.  The or-free (classical) fragment L_P^c: C16 §2.1 p. 47;
   CR11 Cor 2.20 "disjunction-free". *)
Inductive orfree : form -> Prop :=
| of_atom : forall p, orfree (FAtom p)
| of_bot  : orfree FBot
| of_and  : forall f g, orfree f -> orfree g -> orfree (FAnd f g)
| of_imp  : forall f g, orfree f -> orfree g -> orfree (FImp f g).

End Syntax.

Arguments FAtom {Atom} _.
Arguments FBot  {Atom}.
Arguments FAnd  {Atom} _ _.
Arguments FOr   {Atom} _ _.
Arguments FImp  {Atom} _ _.

(* D2.  Abbreviations (notations, not Definitions, so clause lemmas and
   rewrite apply without unfold): CR11 p. 3; CGR18 Fact 4.12 p. 64 and
   p. 65 "! and ? do not have to be added as primitive connectives";
   R13 Fact 12 p. 97; C16 Def 2.2.5. *)
Notation Neg f   := (FImp f FBot).
Notation Bang f  := (FImp (FImp f FBot) FBot).
Notation Quest f := (FOr f (FImp f FBot)).

(* D4.  Uniform substitution of g for atom p (stated over a decidable
   Atom; used only with Atom := bool in the countermodels):
   CR11 Remark 3.8 p. 10; C16 Prop 2.5.21 p. 67. *)
Fixpoint subst (p : bool) (g : form bool) (f : form bool) : form bool :=
  match f with
  | FAtom q    => if Bool.eqb p q then g else FAtom q
  | FBot       => FBot
  | FAnd f1 f2 => FAnd (subst p g f1) (subst p g f2)
  | FOr  f1 f2 => FOr  (subst p g f1) (subst p g f2)
  | FImp f1 f2 => FImp (subst p g f1) (subst p g f2)
  end.

(* ========================================================================== *)
(*  Part 2 — Information states and abstract propositions                     *)
(* ========================================================================== *)

Section Propositions.

Variable W : Type.

(* D5.  Information states and enhancement: CGR18 Defs 2.1-2.2 p. 16,
   p. 17; R13 Def 1 p. 84; C16 Def 2.1.1 p. 46.  Plain predicates; the
   empty state is only ever used through the predicate [empty]
   (ARTIFACT-iii). *)
Definition state := W -> Prop.
Definition sub (t s : state) : Prop := forall w, t w -> s w.
Definition empty (s : state) : Prop := forall w, ~ s w.
Definition nil_state : state := fun _ => False.
Definition ignorant : state := fun _ => True.
Definition single (w : W) : state := fun v => v = w.
Definition inter (s t : state) : state := fun w => s w /\ t w.
Definition seq (s t : state) : Prop := forall w, s w <-> t w.

(* D6.  The powerset of a state, CGR18 p. 18. *)
Definition pow (a : state) : state -> Prop := fun s => sub s a.

Lemma sub_refl : forall s, sub s s.
Proof. intros s w Hw; exact Hw. Qed.

Lemma sub_trans : forall s t u, sub s t -> sub t u -> sub s u.
Proof. intros s t u H1 H2 w Hw; apply H2, H1, Hw. Qed.

Lemma seq_refl : forall s, seq s s.
Proof. intros s w; tauto. Qed.

Lemma seq_sym : forall s t, seq s t -> seq t s.
Proof. intros s t H w; split; apply H. Qed.

Lemma seq_sub : forall s t, seq s t -> sub s t.
Proof. intros s t H w Hw; apply H, Hw. Qed.

Hint Unfold sub empty ignorant single inter pow : inq.
Hint Resolve sub_refl sub_trans : inq.

(* D7.  Sets of states; propositions as non-empty downward-closed sets:
   CGR18 Def 2.3 p. 17, Def 2.9 p. 21, Def 2.22 p. 27; R13 Def 5,
   Fact 2 p. 86.  Issues (CGR18 Def 2.3) are the same type iprop
   (ARTIFACT-ii). *)
Definition iprop := state -> Prop.
Definition down_closed (P : iprop) : Prop :=
  forall s t, P s -> sub t s -> P t.
Definition is_prop (P : iprop) : Prop :=
  (exists s, P s) /\ down_closed P.
Definition peq (P Q : iprop) : Prop := forall s, P s <-> Q s.
Definition ple (P Q : iprop) : Prop := forall s, P s -> Q s.
Definition proposition := { P : iprop | is_prop P }.

Lemma peq_refl : forall P, peq P P.
Proof. intros P s; tauto. Qed.

Lemma peq_sym : forall P Q, peq P Q -> peq Q P.
Proof. intros P Q H s; split; apply H. Qed.

Lemma peq_trans : forall P Q R, peq P Q -> peq Q R -> peq P R.
Proof. intros P Q R H1 H2 s; rewrite (H1 s); apply H2. Qed.

Lemma peq_ple : forall P Q, peq P Q -> ple P Q.
Proof. intros P Q H s Hs; apply H, Hs. Qed.

(* D8.  Resolving/supporting a proposition is membership; refinement is
   inclusion: CGR18 Defs 2.4, 2.6, 2.13 pp. 17-22. *)
Definition resolves (s : state) (P : iprop) : Prop := P s.
Definition supports (s : state) (P : iprop) : Prop := P s.
Definition refines (P Q : iprop) : Prop := ple P Q.

(* D9.  info P = union of P: CGR18 Def 2.10 p. 22; R13 Def 2 p. 84. *)
Definition info (P : iprop) : state := fun w => exists s, P s /\ s w.

(* D10.  Truth of an abstract proposition at a world: CGR18 Def 2.12 p. 22. *)
Definition ptrue (P : iprop) (w : W) : Prop := info P w.

(* D11.  Informative / inquisitive / hybrid / tautology, with positive
   forms: CGR18 Def 2.15 p. 23, Fact 2.18 p. 25; R13 Defs 10-11 p. 92. *)
Definition noninformative (P : iprop) : Prop := forall w, info P w.
Definition noninquisitive (P : iprop) : Prop := P (info P).
Definition informative (P : iprop) : Prop := ~ noninformative P.
Definition inquisitive (P : iprop) : Prop := ~ noninquisitive P.
Definition hybrid (P : iprop) : Prop := informative P /\ inquisitive P.
Definition tautology_p (P : iprop) : Prop := P ignorant.

(* D12.  Alternatives (maximal elements) and greatest elements — kept
   distinct, CGR18 fn. 6 p. 25 (pitfall 9): CGR18 Def 2.7 p. 19,
   Def 2.16 p. 23; CR11 Def 2.9(1). *)
Definition alt (P : iprop) (s : state) : Prop :=
  P s /\ forall t, P t -> sub s t -> sub t s.
Definition greatest (P : iprop) (s : state) : Prop :=
  P s /\ forall t, P t -> sub t s.

(* D13.  The explicit excluded-middle hypothesis for ARTIFACT-v; discharged
   for every [[phi]] by decided_info_sem below. *)
Definition decided_info (P : iprop) : Prop :=
  forall w, info P w \/ ~ info P w.

(* D14.  Top and bottom: CGR18 Def 2.24 p. 27; R13 p. 87.  pbot is the
   PREDICATE "s is empty", i.e. the set {emptyset} (ARTIFACT-iii). *)
Definition ptop : iprop := pow ignorant.
Definition pbot : iprop := fun s => empty s.

(* -------------------------------------------------------------------- *)
(*  T1.  Basic proposition-hood: CGR18 p. 18, Def 2.24, fn. 2 p. 17.    *)
(* -------------------------------------------------------------------- *)

Lemma pow_is_prop : forall a, is_prop (pow a).
Proof.
  intros a; split.
  - exists nil_state; intros w [].
  - intros s t Hs Hts w Hw; apply Hs, Hts, Hw.
Qed.

Lemma top_is_prop : is_prop ptop.
Proof. apply pow_is_prop. Qed.

Lemma bot_is_prop : is_prop pbot.
Proof.
  split.
  - exists nil_state; intros w [].
  - intros s t Hs Hts w Hw; exact (Hs w (Hts w Hw)).
Qed.

Lemma nil_in_prop : forall P, is_prop P -> P nil_state.
Proof.
  intros P [[s Hs] Hdc]; apply (Hdc s); [exact Hs | intros w []].
Qed.

Lemma empty_in_prop : forall P s, is_prop P -> empty s -> P s.
Proof.
  intros P s [[t Ht] Hdc] He; apply (Hdc t); [exact Ht |].
  intros w Hw; destruct (He w Hw).
Qed.

(* T2.  Propositions respect extensional equality of states — the
   encoding lemma replacing set extensionality (design §2). *)
Lemma prop_respects_seq : forall P s t,
  is_prop P -> seq s t -> P s -> P t.
Proof.
  intros P s t [_ Hdc] Hst Hs.
  apply (Hdc s); [exact Hs | intros w Hw; apply Hst, Hw].
Qed.

(* T3.  Truth via singletons: CGR18 Fact 2.14 p. 22. *)
Lemma true_iff_single : forall P w,
  is_prop P -> (info P w <-> P (single w)).
Proof.
  intros P w HP; split.
  - intros [s [Hs Hw]]; destruct HP as [_ Hdc].
    apply (Hdc s); [exact Hs | intros v Hv; unfold single in Hv; subst v; exact Hw].
  - intros Hw; exists (single w); split; [exact Hw | reflexivity].
Qed.

(* T5.  Triviality characterisations: CGR18 Fact 2.18 p. 25, p. 26. *)
Lemma noninq_char_def : forall P, noninquisitive P <-> P (info P).
Proof. intros P; unfold noninquisitive; tauto. Qed.

Lemma noninf_char_def : forall P, noninformative P <-> forall w, info P w.
Proof. intros P; unfold noninformative; tauto. Qed.

Lemma tautology_top : forall P,
  is_prop P -> tautology_p P -> peq P ptop.
Proof.
  intros P HP Htaut s; split.
  - intros _ w _; exact I.
  - intros _; destruct HP as [_ Hdc].
    apply (Hdc ignorant); [exact Htaut | intros w _; exact I].
Qed.

(* T4.  The four-way characterisation of non-inquisitiveness, proved as
   the book's chain (1)=>(2)=>(3)=>(4)=>(1): CGR18 Fact 2.19 p. 25. *)
Lemma noninq_1_2 : forall P,
  is_prop P -> P (info P) -> peq P (pow (info P)).
Proof.
  intros P HP H1 s; split.
  - intros Hs w Hw; exists s; split; assumption.
  - intros Hs; destruct HP as [_ Hdc]; exact (Hdc _ _ H1 Hs).
Qed.

Lemma noninq_2_3 : forall P,
  is_prop P -> peq P (pow (info P)) -> exists g, greatest P g.
Proof.
  intros P HP H2; exists (info P); split.
  - apply H2; intros w Hw; exact Hw.
  - intros t Ht w Hw; exists t; split; assumption.
Qed.

Lemma noninq_3_4 : forall P,
  is_prop P -> (exists g, greatest P g) ->
  forall s, P s <-> forall w, s w -> P (single w).
Proof.
  intros P HP [g [Hg Hmax]] s; split.
  - intros Hs w Hw; destruct HP as [_ Hdc].
    apply (Hdc s); [exact Hs |].
    intros v Hv; unfold single in Hv; subst v; exact Hw.
  - intros Hall; destruct HP as [_ Hdc].
    apply (Hdc g); [exact Hg |].
    intros w Hw; apply (Hmax (single w) (Hall w Hw)); reflexivity.
Qed.

Lemma noninq_4_1 : forall P,
  is_prop P -> (forall s, P s <-> forall w, s w -> P (single w)) ->
  P (info P).
Proof.
  intros P HP H4; apply H4; intros w Hw.
  apply true_iff_single; assumption.
Qed.

(* T6.  The entailment order: CGR18 Facts 2.23, 2.25 p. 27; R13 Fact 2
   p. 86, Def 4. *)
Lemma ple_refl : forall P, ple P P.
Proof. intros P s Hs; exact Hs. Qed.

Lemma ple_trans : forall P Q R, ple P Q -> ple Q R -> ple P R.
Proof. intros P Q R H1 H2 s Hs; apply H2, H1, Hs. Qed.

Lemma ple_antisym_peq : forall P Q, ple P Q -> ple Q P -> peq P Q.
Proof. intros P Q H1 H2 s; split; [apply H1 | apply H2]. Qed.

Lemma bot_least : forall P, is_prop P -> ple pbot P.
Proof. intros P HP s Hs; apply empty_in_prop; assumption. Qed.

Lemma top_greatest : forall P, ple P ptop.
Proof. intros P s _ w _; exact I. Qed.

Lemma ple_info : forall P Q, ple P Q -> sub (info P) (info Q).
Proof.
  intros P Q H w [s [Hs Hw]]; exists s; split; [apply H, Hs | exact Hw].
Qed.

(* T7.  Two incomparable alternatives force inquisitiveness; under
   non-inquisitiveness the only alternative is info P: CGR18 p. 23,
   Fact 2.17 "<=", Fact 2.19(3). *)
Lemma two_alts_inquisitive : forall P a b,
  is_prop P -> alt P a -> alt P b -> ~ sub a b -> inquisitive P.
Proof.
  intros P a b HP [Ha Hamax] [Hb Hbmax] Hab Hni.
  apply Hab.
  assert (Hsa : sub a (info P)) by (intros w Hw; exists a; split; assumption).
  assert (Hsb : sub b (info P)) by (intros w Hw; exists b; split; assumption).
  apply sub_trans with (info P).
  - exact Hsa.
  - exact (Hbmax (info P) Hni Hsb).
Qed.

Lemma noninq_alt : forall P s,
  is_prop P -> P (info P) -> (alt P s <-> seq s (info P)).
Proof.
  intros P s HP Hni; split.
  - intros [Hs Hmax] w; split.
    + intros Hw; exists s; split; assumption.
    + intros Hw.
      assert (Hsub : sub s (info P)) by (intros v Hv; exists s; split; assumption).
      exact (Hmax (info P) Hni Hsub w Hw).
  - intros Hseq; split.
    + apply (prop_respects_seq P (info P) s HP); [apply seq_sym, Hseq | exact Hni].
    + intros t Ht Hst w Hw; apply Hseq; exists t; split; assumption.
Qed.


(* ========================================================================== *)
(*  Part 3 — The algebra of propositions                                      *)
(* ========================================================================== *)

(* D15.  Binary and arbitrary (family) meets and joins: CGR18 Facts 3.1-3.2
   p. 49; R13 Facts 3-4 pp. 86-87.  pJoin carries the "empty s" disjunct
   so that the join of the empty family is {emptyset}, R13's stipulation
   (pitfall 8). *)
Definition pmeet (P Q : iprop) : iprop := fun s => P s /\ Q s.
Definition pjoin (P Q : iprop) : iprop := fun s => P s \/ Q s.
Definition pMeet (Sig : iprop -> Prop) : iprop :=
  fun s => forall P, Sig P -> P s.
Definition pJoin (Sig : iprop -> Prop) : iprop :=
  fun s => empty s \/ exists P, Sig P /\ P s.

(* D16.  Relative and absolute pseudo-complement: CGR18 Facts 3.3-3.4
   p. 51; R13 Def 6 p. 87, p. 88. *)
Definition pimp (P Q : iprop) : iprop :=
  fun s => forall t, sub t s -> P t -> Q t.
Definition pstar (P : iprop) : iprop := pimp P pbot.

(* D17.  Order-theoretic specifications: CGR18 pp. 47-51; R13 pp. 83,
   87-88.  Hand-rolled — no lattice classes in the stdlib (ARTIFACT-iv). *)
Definition is_glb (P Q R : iprop) : Prop :=
  ple R P /\ ple R Q /\
  forall C, is_prop C -> ple C P -> ple C Q -> ple C R.
Definition is_lub (P Q R : iprop) : Prop :=
  ple P R /\ ple Q R /\
  forall C, is_prop C -> ple P C -> ple Q C -> ple R C.
Definition is_glb_fam (Sig : iprop -> Prop) (R : iprop) : Prop :=
  (forall P, Sig P -> ple R P) /\
  forall C, is_prop C -> (forall P, Sig P -> ple C P) -> ple C R.
Definition is_lub_fam (Sig : iprop -> Prop) (R : iprop) : Prop :=
  (forall P, Sig P -> ple P R) /\
  forall C, is_prop C -> (forall P, Sig P -> ple P C) -> ple R C.
Definition is_rpc (P Q R : iprop) : Prop :=
  ple (pmeet P R) Q /\
  forall C, is_prop C -> ple (pmeet P C) Q -> ple C R.
Definition boolean_complement (P Q : iprop) : Prop :=
  peq (pmeet P Q) pbot /\ peq (pjoin P Q) ptop.

(* -------------------------------------------------------------------- *)
(*  T8.  The operations preserve proposition-hood: CGR18 Facts 3.1-3.4; *)
(*  R13 Facts 3-5.                                                      *)
(* -------------------------------------------------------------------- *)

Lemma meet_is_prop : forall P Q,
  is_prop P -> is_prop Q -> is_prop (pmeet P Q).
Proof.
  intros P Q HP HQ; split.
  - exists nil_state; split; apply nil_in_prop; assumption.
  - intros s t [Hs1 Hs2] Hts; split.
    + destruct HP as [_ D]; exact (D _ _ Hs1 Hts).
    + destruct HQ as [_ D]; exact (D _ _ Hs2 Hts).
Qed.

Lemma join_is_prop : forall P Q,
  is_prop P -> is_prop Q -> is_prop (pjoin P Q).
Proof.
  intros P Q HP HQ; split.
  - exists nil_state; left; apply nil_in_prop; exact HP.
  - intros s t [Hs | Hs] Hts.
    + left; destruct HP as [_ D]; exact (D _ _ Hs Hts).
    + right; destruct HQ as [_ D]; exact (D _ _ Hs Hts).
Qed.

Lemma Meet_is_prop : forall Sig,
  (forall P, Sig P -> is_prop P) -> is_prop (pMeet Sig).
Proof.
  intros Sig HS; split.
  - exists nil_state; intros P HP; apply nil_in_prop, HS, HP.
  - intros s t Hs Hts P HP; destruct (HS P HP) as [_ D];
      exact (D _ _ (Hs P HP) Hts).
Qed.

Lemma Join_is_prop : forall Sig,
  (forall P, Sig P -> is_prop P) -> is_prop (pJoin Sig).
Proof.
  intros Sig HS; split.
  - exists nil_state; left; intros w [].
  - intros s t Hs Hts; destruct Hs as [He | [P [HP Hs]]].
    + left; intros w Hw; exact (He w (Hts w Hw)).
    + right; exists P; split; [exact HP |].
      destruct (HS P HP) as [_ D]; exact (D _ _ Hs Hts).
Qed.

Lemma imp_is_prop : forall P Q,
  is_prop Q -> is_prop (pimp P Q).
Proof.
  intros P Q HQ; split.
  - exists nil_state; intros t Hts HPt.
    apply empty_in_prop; [exact HQ | intros w Hw; exact (Hts w Hw)].
  - intros s t Hs Hts u Hut HPu.
    apply Hs; [exact (sub_trans _ _ _ Hut Hts) | exact HPu].
Qed.

Lemma star_is_prop : forall P, is_prop (pstar P).
Proof. intros P; apply imp_is_prop, bot_is_prop. Qed.

(* T9.  Meets and joins are glbs and lubs: CGR18 Facts 3.1-3.2 p. 49;
   R13 Facts 3-4 pp. 86-87 ("any set of propositions"). *)
Lemma meet_glb : forall P Q, is_glb P Q (pmeet P Q).
Proof.
  intros P Q; split; [| split].
  - intros s [H _]; exact H.
  - intros s [_ H]; exact H.
  - intros C _ H1 H2 s Hs; split; [apply H1, Hs | apply H2, Hs].
Qed.

Lemma join_lub : forall P Q, is_lub P Q (pjoin P Q).
Proof.
  intros P Q; split; [| split].
  - intros s H; left; exact H.
  - intros s H; right; exact H.
  - intros C _ H1 H2 s [Hs | Hs]; [apply H1, Hs | apply H2, Hs].
Qed.

Lemma Meet_glb : forall Sig, is_glb_fam Sig (pMeet Sig).
Proof.
  intros Sig; split.
  - intros P HP s Hs; exact (Hs P HP).
  - intros C _ H s Hs P HP; exact (H P HP s Hs).
Qed.

Lemma Join_lub : forall Sig,
  (forall P, Sig P -> is_prop P) -> is_lub_fam Sig (pJoin Sig).
Proof.
  intros Sig HS; split.
  - intros P HP s Hs; right; exists P; split; assumption.
  - intros C HC H s [He | [P [HP Hs]]].
    + apply empty_in_prop; assumption.
    + exact (H P HP s Hs).
Qed.

(* T10.  The adjunction — pimp is the relative pseudo-complement:
   CGR18 Fact 3.3 p. 51; R13 Def 6, Fact 5 p. 87. *)
Lemma imp_adjunction : forall P Q R,
  is_prop R -> (ple R (pimp P Q) <-> ple (pmeet R P) Q).
Proof.
  intros P Q R HR; split.
  - intros H s [HRs HPs]; exact (H s HRs s (sub_refl s) HPs).
  - intros H s HRs t Hts HPt.
    apply H; split; [| exact HPt].
    destruct HR as [_ D]; exact (D _ _ HRs Hts).
Qed.

Lemma imp_is_rpc : forall P Q, is_rpc P Q (pimp P Q).
Proof.
  intros P Q; split.
  - intros s [HPs Himp]; exact (Himp s (sub_refl s) HPs).
  - intros C HC H s HCs t Hts HPt.
    apply H; split; [exact HPt |].
    destruct HC as [_ D]; exact (D _ _ HCs Hts).
Qed.

(* T11.  The Heyting laws, packaged: CGR18 p. 51 "<P, subseteq> forms a
   Heyting algebra"; R13 p. 88 (ARTIFACT-iv). *)
Lemma heyting_mp : forall P Q, ple (pmeet P (pimp P Q)) Q.
Proof. intros P Q s [HP Himp]; exact (Himp s (sub_refl s) HP). Qed.

Lemma heyting_intro : forall P Q,
  is_prop P -> ple P (pimp Q (pmeet Q P)).
Proof.
  intros P Q HP s Hs t Hts HQt; split; [exact HQt |].
  destruct HP as [_ D]; exact (D _ _ Hs Hts).
Qed.

Lemma imp_self_top : forall P, peq (pimp P P) ptop.
Proof.
  intros P s; split.
  - intros _ w _; exact I.
  - intros _ t _ H; exact H.
Qed.

Lemma meet_star_bot : forall P,
  is_prop P -> peq (pmeet P (pstar P)) pbot.
Proof.
  intros P HP s; split.
  - intros [HPs Hstar]; exact (Hstar s (sub_refl s) HPs).
  - intros He; split.
    + apply empty_in_prop; assumption.
    + intros t Hts _ w Hw; exact (He w (Hts w Hw)).
Qed.

Lemma meet_comm : forall P Q, peq (pmeet P Q) (pmeet Q P).
Proof. intros P Q s; unfold pmeet; tauto. Qed.

Lemma meet_assoc : forall P Q R,
  peq (pmeet P (pmeet Q R)) (pmeet (pmeet P Q) R).
Proof. intros P Q R s; unfold pmeet; tauto. Qed.

Lemma meet_idem : forall P, peq (pmeet P P) P.
Proof. intros P s; unfold pmeet; tauto. Qed.

Lemma join_comm : forall P Q, peq (pjoin P Q) (pjoin Q P).
Proof. intros P Q s; unfold pjoin; tauto. Qed.

Lemma join_assoc : forall P Q R,
  peq (pjoin P (pjoin Q R)) (pjoin (pjoin P Q) R).
Proof. intros P Q R s; unfold pjoin; tauto. Qed.

Lemma join_idem : forall P, peq (pjoin P P) P.
Proof. intros P s; unfold pjoin; tauto. Qed.

Lemma absorb_meet_join : forall P Q, peq (pmeet P (pjoin P Q)) P.
Proof. intros P Q s; unfold pmeet, pjoin; tauto. Qed.

Lemma absorb_join_meet : forall P Q, peq (pjoin P (pmeet P Q)) P.
Proof. intros P Q s; unfold pmeet, pjoin; tauto. Qed.

Lemma meet_join_distrib : forall P Q R,
  peq (pmeet P (pjoin Q R)) (pjoin (pmeet P Q) (pmeet P R)).
Proof. intros P Q R s; unfold pmeet, pjoin; tauto. Qed.

Lemma imp_meet_split : forall P Q R,
  peq (pimp P (pmeet Q R)) (pmeet (pimp P Q) (pimp P R)).
Proof.
  intros P Q R s; split.
  - intros H; split; intros t Hts HPt; apply (H t Hts HPt).
  - intros [H1 H2] t Hts HPt; split; [apply H1 | apply H2]; assumption.
Qed.

(* The bespoke record (ARTIFACT-iv): the Heyting-algebra structure on
   propositions, up to peq. *)
Record HeytingLaws : Prop := {
  hl_meet_glb   : forall P Q, is_glb P Q (pmeet P Q);
  hl_join_lub   : forall P Q, is_lub P Q (pjoin P Q);
  hl_rpc        : forall P Q, is_rpc P Q (pimp P Q);
  hl_top        : forall P, ple P ptop;
  hl_bot        : forall P, is_prop P -> ple pbot P;
  hl_meet_comm  : forall P Q, peq (pmeet P Q) (pmeet Q P);
  hl_meet_assoc : forall P Q R, peq (pmeet P (pmeet Q R)) (pmeet (pmeet P Q) R);
  hl_join_comm  : forall P Q, peq (pjoin P Q) (pjoin Q P);
  hl_join_assoc : forall P Q R, peq (pjoin P (pjoin Q R)) (pjoin (pjoin P Q) R);
  hl_distrib    : forall P Q R,
      peq (pmeet P (pjoin Q R)) (pjoin (pmeet P Q) (pmeet P R))
}.

Theorem inq_heyting : HeytingLaws.
Proof.
  constructor.
  - exact meet_glb.
  - exact join_lub.
  - exact imp_is_rpc.
  - exact top_greatest.
  - exact bot_least.
  - exact meet_comm.
  - exact meet_assoc.
  - exact join_comm.
  - exact join_assoc.
  - exact meet_join_distrib.
Qed.

(* T12.  The absolute pseudo-complement pointwise, P* = pow((info P)^c):
   CGR18 Facts 3.4-3.5 p. 51; R13 Fact 6 p. 88.  Constructive: the =>
   direction instantiates the substate with inter t s, in P by downward
   closure (design §4 Block B). *)
Lemma star_char : forall P s,
  is_prop P ->
  (pstar P s <-> forall t, P t -> forall w, ~ (s w /\ t w)).
Proof.
  intros P s HP; split.
  - intros Hstar t Ht w [Hsw Htw].
    assert (Hin : P (inter t s)).
    { destruct HP as [_ D]; apply (D t); [exact Ht | intros v [Hv _]; exact Hv]. }
    assert (He : empty (inter t s)).
    { apply (Hstar (inter t s)); [intros v [_ Hv]; exact Hv | exact Hin]. }
    exact (He w (conj Htw Hsw)).
  - intros H t Hts HPt w Hw.
    exact (H t HPt w (conj (Hts w Hw) Hw)).
Qed.

Lemma star_pow : forall P s,
  is_prop P ->
  (pstar P s <-> forall w, s w -> ~ info P w).
Proof.
  intros P s HP; split.
  - intros Hstar w Hw [t [Ht Htw]].
    exact (proj1 (star_char P s HP) Hstar t Ht w (conj Hw Htw)).
  - intros H t Hts HPt w Hw.
    apply (H w (Hts w Hw)); exists t; split; assumption.
Qed.

Lemma star_noninq : forall P,
  is_prop P -> noninquisitive (pstar P).
Proof.
  intros P HP; unfold noninquisitive.
  apply (star_pow P _ HP).
  intros w [t [Ht Htw]] HinfP.
  exact (proj1 (star_pow P t HP) Ht w Htw HinfP).
Qed.

Lemma star_antitone : forall P Q,
  ple P Q -> ple (pstar Q) (pstar P).
Proof.
  intros P Q H s Hs t Hts HPt; exact (Hs t Hts (H t HPt)).
Qed.

Lemma star_star_intro : forall P,
  is_prop P -> ple P (pstar (pstar P)).
Proof.
  intros P HP s Hs t Hts Hstar.
  intros w Hw.
  apply (proj1 (star_pow P t HP) Hstar w Hw).
  exists s; split; [exact Hs | apply Hts, Hw].
Qed.

Lemma star_star_star : forall P,
  is_prop P -> peq (pstar (pstar (pstar P))) (pstar P).
Proof.
  intros P HP s; split.
  - intros H t Hts HPt.
    apply (H t Hts).
    apply (star_star_intro P HP); exact HPt.
  - intros H t Hts H2.
    assert (HPt : pstar P t).
    { destruct (star_is_prop P) as [_ D]; exact (D _ _ H Hts). }
    exact (H2 t (sub_refl t) HPt).
Qed.

(* T13.  Only top and bottom have Boolean complements: CGR18 pp. 51-52;
   R13 p. 88.  Constructive: the ignorant state lies in P or Q by the
   join condition; downward closure collapses that side to ptop, and the
   meet condition forces the other side to pbot. *)
Lemma boolean_complements_extremal : forall P Q,
  is_prop P -> is_prop Q -> boolean_complement P Q ->
  (peq P ptop /\ peq Q pbot) \/ (peq P pbot /\ peq Q ptop).
Proof.
  intros P Q HP HQ [Hmeet Hjoin].
  destruct (proj2 (Hjoin ignorant) (fun w _ => I)) as [HPi | HQi].
  - left; split.
    + intros s; split; [intros _ w0 _; exact I |].
      intros _; destruct HP as [_ D]; apply (D ignorant); [exact HPi | intros w _; exact I].
    + intros s; split.
      * intros HQs; apply (Hmeet s); split; [| exact HQs].
        destruct HP as [_ D]; apply (D ignorant); [exact HPi | intros w _; exact I].
      * intros He; apply empty_in_prop; assumption.
  - right; split.
    + intros s; split.
      * intros HPs; apply (Hmeet s); split; [exact HPs |].
        destruct HQ as [_ D]; apply (D ignorant); [exact HQi | intros w _; exact I].
      * intros He; apply empty_in_prop; assumption.
    + intros s; split; [intros _ w0 _; exact I |].
      intros _; destruct HQ as [_ D]; apply (D ignorant); [exact HQi | intros w _; exact I].
Qed.

(* ========================================================================== *)
(*  Part 4 — Projections                                                      *)
(* ========================================================================== *)

(* D18.  Decision sets: CGR18 Defs 3.8-3.9 pp. 53-54; R13 Def 12 p. 96. *)
Definition contradicts (s : state) (P : iprop) : Prop :=
  forall w, s w -> ~ info P w.
Definition decides (s : state) (P : iprop) : Prop :=
  P s \/ contradicts s P.
Definition dset (P : iprop) : iprop := fun s => decides s P.

(* D19.  Issue-cancelling and info-cancelling maps: CGR18 Def 3.6 p. 53,
   Def 3.11 p. 54; R13 pp. 95-96. *)
Definition issue_cancelling (pi : iprop -> iprop) : Prop :=
  forall P, is_prop P ->
    is_prop (pi P) /\ noninquisitive (pi P) /\ seq (info (pi P)) (info P).
Definition info_cancelling (pi : iprop -> iprop) : Prop :=
  forall P, is_prop P ->
    is_prop (pi P) /\ noninformative (pi P) /\ peq (dset (pi P)) (dset P).

(* D20.  The projections: CGR18 Def 3.13 p. 55; R13 Thm 2 p. 95,
   Fact 11 p. 96. *)
Definition pbang (P : iprop) : iprop := pow (info P).
Definition pquest (P : iprop) : iprop := pjoin P (pstar P).

(* -------------------------------------------------------------------- *)
(*  T14.  pbang satisfies the issue-cancelling specification:           *)
(*  CGR18 Def 3.6; R13 Thm 2 "<=".                                       *)
(* -------------------------------------------------------------------- *)

Lemma bang_is_prop : forall P, is_prop (pbang P).
Proof. intros P; apply pow_is_prop. Qed.

Lemma ple_bang : forall P, ple P (pbang P).
Proof. intros P s Hs w Hw; exists s; split; assumption. Qed.

Lemma bang_info : forall P, seq (info (pbang P)) (info P).
Proof.
  intros P w; split.
  - intros [s [Hs Hsw]]; exact (Hs w Hsw).
  - intros Hw; exists (single w); split.
    + intros v Hv; unfold single in Hv; subst v; exact Hw.
    + reflexivity.
Qed.

Lemma bang_noninq : forall P, noninquisitive (pbang P).
Proof.
  intros P; unfold noninquisitive.
  intros w Hw; apply (bang_info P w); exact Hw.
Qed.

Lemma bang_issue_cancelling : issue_cancelling pbang.
Proof.
  intros P HP; split; [apply bang_is_prop | split].
  - apply bang_noninq.
  - apply bang_info.
Qed.

(* T15.  pbang is THE issue-cancelling map: CGR18 Fact 3.7 p. 53;
   R13 Thm 2 p. 95.  Via the (1)=>(2) leg of T4. *)
Lemma bang_unique : forall (pi : iprop -> iprop),
  issue_cancelling pi ->
  forall P, is_prop P -> peq (pi P) (pbang P).
Proof.
  intros pi Hpi P HP.
  destruct (Hpi P HP) as [Hprop [Hni Hinfo]].
  apply peq_trans with (pow (info (pi P))).
  - apply noninq_1_2; assumption.
  - intros s; split; intros Hs w Hw.
    + apply (Hinfo w), Hs, Hw.
    + apply (Hinfo w), Hs, Hw.
Qed.

(* T16.  The decision set is ?P: CGR18 Fact 3.10 p. 54. *)
Lemma decision_set : forall P,
  is_prop P -> peq (dset P) (pquest P).
Proof.
  intros P HP s; split.
  - intros [Hs | Hc]; [left; exact Hs |].
    right; apply (star_pow P s HP); exact Hc.
  - intros [Hs | Hstar]; [left; exact Hs |].
    right; exact (proj1 (star_pow P s HP) Hstar).
Qed.

(* T17.  pquest satisfies the info-cancelling specification.  The
   non-informativity of ?P for ABSTRACT P is the one genuinely classical
   step (R13 Thm 3's "union of [?phi] = W"), isolated in decided_info
   (ARTIFACT-v): CGR18 Def 3.11 p. 54; R13 Thm 3 "<=" p. 96. *)
Lemma quest_is_prop : forall P,
  is_prop P -> is_prop (pquest P).
Proof.
  intros P HP; apply join_is_prop; [exact HP | apply star_is_prop].
Qed.

Lemma ple_quest : forall P, ple P (pquest P).
Proof. intros P s Hs; left; exact Hs. Qed.

Lemma quest_decision : forall P,
  is_prop P -> peq (dset (pquest P)) (dset P).
Proof.
  intros P HP s; split.
  - intros [[Hs | Hstar] | Hc].
    + left; exact Hs.
    + right; intros w Hw; exact (proj1 (star_pow P s HP) Hstar w Hw).
    + right; intros w Hw HinfP.
      apply (Hc w Hw); apply (ple_info P (pquest P)).
      * apply ple_quest.
      * exact HinfP.
  - intros [Hs | Hc].
    + left; left; exact Hs.
    + left; right; apply (star_pow P s HP); exact Hc.
Qed.

Lemma quest_noninf : forall P,
  is_prop P -> decided_info P -> noninformative (pquest P).
Proof.
  intros P HP Hdec w.
  destruct (Hdec w) as [Hw | Hnw].
  - destruct Hw as [s [Hs Hsw]].
    exists s; split; [left; exact Hs | exact Hsw].
  - exists (single w); split; [| reflexivity].
    right; apply (star_pow P (single w) HP).
    intros v Hv; unfold single in Hv; subst v; exact Hnw.
Qed.

(* T18.  pquest is THE info-cancelling map — constructive (the design's
   route: a non-informative proposition equals its own decision set):
   CGR18 Fact 3.12 p. 54; R13 Thm 3 p. 96. *)
Lemma noninf_dset : forall Q,
  is_prop Q -> noninformative Q -> peq (dset Q) Q.
Proof.
  intros Q HQ Hni s; split.
  - intros [Hs | Hc]; [exact Hs |].
    apply empty_in_prop; [exact HQ |].
    intros w Hw; exact (Hc w Hw (Hni w)).
  - intros Hs; left; exact Hs.
Qed.

Lemma quest_unique : forall (pi : iprop -> iprop),
  info_cancelling pi ->
  (forall P, is_prop P -> noninformative (pquest P)) ->
  forall P, is_prop P -> peq (pi P) (pquest P).
Proof.
  intros pi Hpi Hqni P HP.
  destruct (Hpi P HP) as [Hprop [Hni Hdset]].
  apply peq_trans with (dset (pi P)).
  - apply peq_sym, noninf_dset; assumption.
  - apply peq_trans with (dset P); [exact Hdset |].
    apply decision_set; exact HP.
Qed.

(* T19.  Division, P = !P /\ ?P: CGR18 Fact 3.14 p. 55; R13 Fact 14
   p. 97.  Constructive: a state below info P supporting P* is empty. *)
Theorem division_p : forall P,
  is_prop P -> peq P (pmeet (pbang P) (pquest P)).
Proof.
  intros P HP s; split.
  - intros Hs; split.
    + apply ple_bang; exact Hs.
    + left; exact Hs.
  - intros [Hbang [Hs | Hstar]]; [exact Hs |].
    apply empty_in_prop; [exact HP |].
    intros w Hw.
    exact (proj1 (star_pow P s HP) Hstar w Hw (Hbang w Hw)).
Qed.

(* T20.  !P vs P**: constructively !P <= P**; equality under the
   explicit EM hypothesis; ?P = P join P* definitionally: CGR18
   Fact 3.15 p. 55; R13 Fact 11 p. 96. *)
Lemma bang_le_starstar : forall P,
  is_prop P -> ple (pbang P) (pstar (pstar P)).
Proof.
  intros P HP s Hs.
  apply (star_pow (pstar P) s (star_is_prop P)).
  intros w Hw [t [Ht Htw]].
  exact (proj1 (star_pow P t HP) Ht w Htw (Hs w Hw)).
Qed.

Lemma bang_eq_starstar : forall P,
  is_prop P -> decided_info P ->
  peq (pbang P) (pstar (pstar P)).
Proof.
  intros P HP Hdec s; split.
  - apply bang_le_starstar; exact HP.
  - intros Hss w Hw.
    destruct (Hdec w) as [Hi | Hni]; [exact Hi | exfalso].
    apply (proj1 (star_pow (pstar P) s (star_is_prop P)) Hss w Hw).
    exists (single w); split; [| reflexivity].
    apply (star_pow P (single w) HP).
    intros v Hv; unfold single in Hv; subst v; exact Hni.
Qed.

Lemma quest_eq : forall P, peq (pquest P) (pjoin P (pstar P)).
Proof. intros P; apply peq_refl. Qed.

End Propositions.

(* Implicit-argument discipline (pitfall 16): implicits per constant, no
   Set Implicit Arguments. *)
Arguments sub {W} _ _.
Arguments empty {W} _.
Arguments nil_state {W}.
Arguments ignorant {W}.
Arguments single {W} _.
Arguments inter {W} _ _.
Arguments seq {W} _ _.
Arguments pow {W} _ _.
Arguments down_closed {W} _.
Arguments is_prop {W} _.
Arguments peq {W} _ _.
Arguments ple {W} _ _.
Arguments info {W} _ _.
Arguments ptrue {W} _ _.
Arguments noninformative {W} _.
Arguments noninquisitive {W} _.
Arguments informative {W} _.
Arguments inquisitive {W} _.
Arguments hybrid {W} _.
Arguments tautology_p {W} _.
Arguments alt {W} _ _.
Arguments greatest {W} _ _.
Arguments decided_info {W} _.
Arguments ptop {W} _.
Arguments pbot {W} _.
Arguments pmeet {W} _ _ _.
Arguments pjoin {W} _ _ _.
Arguments pMeet {W} _ _.
Arguments pJoin {W} _ _.
Arguments pimp {W} _ _ _.
Arguments pstar {W} _ _.
Arguments is_glb {W} _ _ _.
Arguments is_lub {W} _ _ _.
Arguments is_rpc {W} _ _ _.
Arguments boolean_complement {W} _ _.
Arguments contradicts {W} _ _.
Arguments decides {W} _ _.
Arguments dset {W} _ _.
Arguments pbang {W} _ _.
Arguments pquest {W} _ _.
Arguments sub_refl {W} _.
Arguments sub_trans {W} _ _ _.
Arguments seq_sub {W} _ _.
Arguments seq_sym {W} _ _.
Arguments nil_in_prop {W} _.
Arguments empty_in_prop {W} _ _.
Arguments prop_respects_seq {W} _ _ _.
Arguments true_iff_single {W} _ _.
Arguments ple_info {W} _ _.
Arguments star_pow {W} _ _.
Arguments star_is_prop {W} _.
Arguments peq_refl {W} _.
Arguments peq_sym {W} _ _.
Arguments peq_trans {W} _ _ _.
Arguments noninq_1_2 {W} _.
Arguments pow_is_prop {W} _.
Arguments bot_is_prop {W}.
Arguments top_is_prop {W}.

(* ========================================================================== *)
(*  Part 5 — Support semantics                                                *)
(* ========================================================================== *)

Section Semantics.

Context {W Atom : Type}.
Variable V : W -> Atom -> bool.

(* D21.  Support as a Fixpoint on the formula (ARTIFACT-i: an Inductive
   is rejected — the -> clause has support in negative position):
   CR11 Def 2.3 p. 3; CGR18 Fact 4.8(1-5) pp. 62-63; R13 Def 9 p. 90;
   C16 Defs 2.1.3, 2.2.2.  The bot clause is the PREDICATE empty s. *)
Fixpoint support (s : state W) (f : form Atom) : Prop :=
  match f with
  | FAtom p  => forall w, s w -> V w p = true
  | FBot     => empty s
  | FAnd g h => support s g /\ support s h
  | FOr  g h => support s g \/ support s h
  | FImp g h => forall t, sub t s -> support t g -> support t h
  end.

(* ARTIFACT-i, made visible: the corresponding Inductive is rejected by
   the strict positivity checker.
     Fail Inductive support_rel : state W -> form Atom -> Prop :=
       | sr_imp : forall s g h,
           (forall t, sub t s -> support_rel t g -> support_rel t h) ->
           support_rel s (FImp g h).
   ("Non strictly positive occurrence of support_rel".) *)

(* Clause lemmas (all definitional), then support is frozen for simpl
   (pitfall 3). *)
Lemma support_atom : forall s p,
  support s (FAtom p) = (forall w, s w -> V w p = true).
Proof. reflexivity. Qed.

Lemma support_bot : forall s, support s FBot = empty s.
Proof. reflexivity. Qed.

Lemma support_and : forall s g h,
  support s (FAnd g h) = (support s g /\ support s h).
Proof. reflexivity. Qed.

Lemma support_or : forall s g h,
  support s (FOr g h) = (support s g \/ support s h).
Proof. reflexivity. Qed.

Lemma support_imp : forall s g h,
  support s (FImp g h) =
  (forall t, sub t s -> support t g -> support t h).
Proof. reflexivity. Qed.

Lemma support_neg_unfold : forall s g,
  support s (Neg g) = (forall t, sub t s -> support t g -> empty t).
Proof. reflexivity. Qed.

(* D22.  [[phi]] = the set of supporting states (CGR18/R13 convention;
   CR11's maximal-state [phi] is alt_f, pitfall 10): CGR18 Def 4.7 p. 62;
   R13 Fact 7 p. 90.  Membership and support are the same Prop
   (ARTIFACT-ii). *)
Definition sem (f : form Atom) : iprop W := fun s => support s f.

(* D23.  Classical truth, with implb/negb so simpl yields Boolean
   equations (pitfall 12): CGR18 Def 4.2 p. 60; CR11 Def 2.9(3);
   C16 Prop 2.1.7. *)
Fixpoint ctruth (w : W) (f : form Atom) : bool :=
  match f with
  | FAtom p  => V w p
  | FBot     => false
  | FAnd g h => andb (ctruth w g) (ctruth w h)
  | FOr  g h => orb (ctruth w g) (ctruth w h)
  | FImp g h => implb (ctruth w g) (ctruth w h)
  end.

Definition truthset (f : form Atom) : state W := fun w => ctruth w f = true.
Definition true_at (w : W) (f : form Atom) : Prop := support (single w) f.

(* D27.  Truth-conditionality, model-relative (CGR18 Fact 4.16 RHS p. 71;
   C16 Def 1.3.6 quantifies over all models — noted). *)
Definition truth_conditional (f : form Atom) : Prop :=
  forall s, support s f <-> forall w, s w -> ctruth w f = true.

(* -------------------------------------------------------------------- *)
(*  T22.  Persistence and the empty-state property: CR11 Prop 2.4 p. 3; *)
(*  C16 Prop 2.2.3 p. 50; CGR18 Fact 4.4.  Induction on the formula     *)
(*  generalising the state (pitfall 1).                                 *)
(* -------------------------------------------------------------------- *)

Theorem persistence : forall f s t,
  support s f -> sub t s -> support t f.
Proof.
  induction f as [p | | g IHg h IHh | g IHg h IHh | g IHg h IHh];
    intros s t Hs Hts; simpl in *.
  - intros w Hw; exact (Hs w (Hts w Hw)).
  - intros w Hw; exact (Hs w (Hts w Hw)).
  - destruct Hs as [H1 H2]; split; [exact (IHg _ _ H1 Hts) | exact (IHh _ _ H2 Hts)].
  - destruct Hs as [H1 | H2]; [left; exact (IHg _ _ H1 Hts) | right; exact (IHh _ _ H2 Hts)].
  - intros u Hut Hg; exact (Hs u (sub_trans _ _ _ Hut Hts) Hg).
Qed.

Theorem empty_state : forall f s, empty s -> support s f.
Proof.
  induction f as [p | | g IHg h IHh | g IHg h IHh | g IHg h IHh];
    intros s He; simpl.
  - intros w Hw; destruct (He w Hw).
  - exact He.
  - split; [apply IHg | apply IHh]; exact He.
  - left; apply IHg; exact He.
  - intros t Hts _; apply IHh; intros w Hw; exact (He w (Hts w Hw)).
Qed.

(* T23.  [[phi]] is a proposition: CGR18 Fact 4.4 p. 61; R13 p. 90;
   C16 p. 50. *)
Theorem sem_is_prop : forall f, is_prop (sem f).
Proof.
  intros f; split.
  - exists nil_state; apply empty_state; intros w [].
  - intros s t Hs Hts; exact (persistence f s t Hs Hts).
Qed.

Definition sem_prop (f : form Atom) : proposition W :=
  exist _ (sem f) (sem_is_prop f).

Corollary support_seq : forall f s t,
  seq s t -> support s f -> support t f.
Proof.
  intros f s t Hst Hs.
  exact (persistence f s t Hs (seq_sub t s (seq_sym s t Hst))).
Qed.

Arguments support : simpl never.

(* T27.  The singleton collapse to classical truth: CR11 Prop 2.5 p. 3;
   C16 Props 2.1.7 + 2.2.4; CGR18 Def 4.7.  Constructive: the key
   implication case decides ctruth w g by a bool case split; the
   emptiness of the substate is decided BY ctruth, never by case analysis
   on the state (pitfall 5). *)
Theorem singleton_collapse : forall f w,
  support (single w) f <-> ctruth w f = true.
Proof.
  induction f as [p | | g IHg h IHh | g IHg h IHh | g IHg h IHh]; intros w.
  - rewrite support_atom; simpl; split.
    + intros H; apply H; reflexivity.
    + intros H v Hv; unfold single in Hv; subst v; exact H.
  - rewrite support_bot; simpl; split.
    + intros He; destruct (He w eq_refl).
    + intros H; discriminate H.
  - rewrite support_and; simpl; rewrite andb_true_iff, <- IHg, <- IHh; tauto.
  - rewrite support_or; simpl; rewrite orb_true_iff, <- IHg, <- IHh; tauto.
  - rewrite support_imp; simpl; split.
    + intros H; destruct (ctruth w g) eqn:Eg; simpl.
      * apply IHh, H; [apply sub_refl | apply IHg; exact Eg].
      * reflexivity.
    + intros H t Hts Hg; destruct (ctruth w g) eqn:Eg; simpl in H.
      * (* antecedent classically true at w: persistence via {w} <= t is
           not available, but h is true at w and t <= {w}. *)
        apply (persistence h (single w) t); [apply IHh; exact H | exact Hts].
      * (* antecedent classically false at w: t must be empty. *)
        apply empty_state; intros v Hv.
        assert (Hvw : v = w) by (exact (Hts v Hv)).
        subst v.
        assert (Hsw : sub (single w) t).
        { intros u Hu; unfold single in Hu; subst u; exact Hv. }
        pose proof (persistence g t (single w) Hg Hsw) as Hgw.
        rewrite (IHg w) in Hgw; rewrite Hgw in Eg; discriminate Eg.
Qed.

(* CR11 Prop 2.5, second half: singletons decide every formula. *)
Corollary singleton_decides : forall f w,
  support (single w) f \/ support (single w) (Neg f).
Proof.
  intros f w; destruct (ctruth w f) eqn:E.
  - left; apply singleton_collapse; exact E.
  - right; rewrite support_neg_unfold.
    intros t Hts Hf v Hv.
    assert (Hvw : v = w) by (exact (Hts v Hv)); subst v.
    assert (Hsw : sub (single w) t).
    { intros u Hu; unfold single in Hu; subst u; exact Hv. }
    pose proof (persistence f t (single w) Hf Hsw) as Hfw.
    rewrite (singleton_collapse f w) in Hfw; rewrite Hfw in E; discriminate E.
Qed.

(* T28.  Negation is pointwise — the workhorse (CR11's proof through the
   singleton collapse): CR11 Prop 2.6 pp. 3-4; CGR18 Fact 4.8(2). *)
Theorem neg_pointwise : forall f s,
  support s (Neg f) <-> forall w, s w -> ctruth w f = false.
Proof.
  intros f s; rewrite support_neg_unfold; split.
  - intros H w Hw; destruct (ctruth w f) eqn:E; [exfalso | reflexivity].
    assert (Hsub : sub (single w) s).
    { intros v Hv; unfold single in Hv; subst v; exact Hw. }
    assert (He : empty (single w)).
    { apply (H (single w) Hsub); apply singleton_collapse; exact E. }
    exact (He w eq_refl).
  - intros H t Hts Hf w Hw.
    assert (Hsw : sub (single w) t).
    { intros u Hu; unfold single in Hu; subst u; exact Hw. }
    pose proof (persistence f t (single w) Hf Hsw) as Hfw.
    rewrite (singleton_collapse f w) in Hfw.
    rewrite (H w (Hts w Hw)) in Hfw; discriminate Hfw.
Qed.

Theorem bang_pointwise : forall f s,
  support s (Bang f) <-> forall w, s w -> ctruth w f = true.
Proof.
  intros f s; rewrite (neg_pointwise (Neg f) s); split.
  - intros H w Hw.
    specialize (H w Hw); simpl in H.
    destruct (ctruth w f); [reflexivity | discriminate H].
  - intros H w Hw; simpl; rewrite (H w Hw); reflexivity.
Qed.

(* The negated antecedent is truth-conditional; general
   truth-conditionality of Neg. *)
Lemma neg_tc : forall f, truth_conditional (Neg f).
Proof.
  intros f s; rewrite (neg_pointwise f s); split.
  - intros H w Hw; simpl; rewrite (H w Hw); reflexivity.
  - intros H w Hw; specialize (H w Hw); simpl in H.
    destruct (ctruth w f); [discriminate H | reflexivity].
Qed.

(* T29.  The truth-conditional-antecedent lemma — the KP workhorse
   replacing "take the maximal state supporting the antecedent"
   (pitfall 6): C16 Prop 2.2.9 p. 53. *)
Theorem imp_tc_antecedent : forall a g s,
  truth_conditional a ->
  (support s (FImp a g) <-> support (inter s (truthset a)) g).
Proof.
  intros a g s Ha; rewrite support_imp; split.
  - intros H.
    apply H; [intros w [Hw _]; exact Hw |].
    apply Ha; intros w [_ Hw]; exact Hw.
  - intros H t Hts Hat.
    apply (persistence g (inter s (truthset a)) t); [exact H |].
    intros w Hw; split; [exact (Hts w Hw) |].
    exact (proj1 (Ha t) Hat w Hw).
Qed.

Corollary neg_antecedent : forall f g s,
  support s (FImp (Neg f) g) <->
  support (inter s (fun w => ctruth w f = false)) g.
Proof.
  intros f g s.
  rewrite (imp_tc_antecedent (Neg f) g s (neg_tc f)).
  assert (Hseq : seq (inter s (truthset (Neg f)))
                     (inter s (fun w => ctruth w f = false))).
  { intros w; unfold inter, truthset; simpl.
    destruct (ctruth w f); simpl; split;
      intros [Hw Hc]; (split; [exact Hw | congruence]). }
  split; intros H.
  - exact (support_seq g _ _ Hseq H).
  - exact (support_seq g _ _ (seq_sym _ _ Hseq) H).
Qed.

(* T30.  Informative content is the truth set: CGR18 Fact 4.14 p. 70,
   Def 4.7; CR11 Prop 2.21 p. 7; R13 Fact 8 p. 92. *)
Theorem info_eq_truthset : forall f,
  seq (info (sem f)) (truthset f).
Proof.
  intros f w; split.
  - intros [s [Hs Hsw]].
    apply singleton_collapse.
    apply (persistence f s (single w)); [exact Hs |].
    intros v Hv; unfold single in Hv; subst v; exact Hsw.
  - intros Hw; exists (single w); split.
    + apply singleton_collapse; exact Hw.
    + reflexivity.
Qed.

Theorem true_at_iff : forall f w,
  true_at w f <-> info (sem f) w.
Proof.
  intros f w; unfold true_at.
  rewrite (singleton_collapse f w).
  split; intros H; [apply (info_eq_truthset f w); exact H |].
  exact (proj1 (info_eq_truthset f w) H).
Qed.

(* ========================================================================== *)
(*  Part 6 — The algebraic recursion and the coincidence theorem              *)
(* ========================================================================== *)

(* D24.  CGR18 Def 4.3(1-5) p. 61 / R13 Def 7 p. 88 transcribed verbatim;
   the bot clause is the one CGR18/R13 leave implicit (they have Neg
   primitive; [[Neg f]] = pstar [[f]] becomes the theorem sem_neg,
   pitfall 11). *)
Fixpoint alg (f : form Atom) : iprop W :=
  match f with
  | FAtom p  => pow (truthset (FAtom p))
  | FBot     => pbot
  | FAnd g h => pmeet (alg g) (alg h)
  | FOr  g h => pjoin (alg g) (alg h)
  | FImp g h => pimp (alg g) (alg h)
  end.

(* T24.  The five clause equations — the ONLY Leibniz equalities between
   propositions in the file, by reflexivity (ARTIFACT-ii, ARTIFACT-iv):
   CGR18 Def 4.3 as facts about support; R13 Def 7. *)
Lemma sem_atom : forall p, sem (FAtom p) = pow (truthset (FAtom p)).
Proof. reflexivity. Qed.

Lemma sem_bot : sem FBot = pbot.
Proof. reflexivity. Qed.

Lemma sem_and : forall f g, sem (FAnd f g) = pmeet (sem f) (sem g).
Proof. reflexivity. Qed.

Lemma sem_or : forall f g, sem (FOr f g) = pjoin (sem f) (sem g).
Proof. reflexivity. Qed.

Lemma sem_imp : forall f g, sem (FImp f g) = pimp (sem f) (sem g).
Proof. reflexivity. Qed.

Lemma sem_neg : forall f, sem (Neg f) = pstar (sem f).
Proof. reflexivity. Qed.

(* T25.  Support completely characterises the algebraic recursion —
   R13 Fact 7 p. 90 ("[phi] is precisely the set of states supporting
   phi"); CGR18 p. 62, Fact 4.8.  Leibniz equality, no extensionality:
   every clause is convertible (ARTIFACT-ii). *)
Theorem alg_eq_sem : forall f, alg f = sem f.
Proof.
  induction f as [p | | g IHg h IHh | g IHg h IHh | g IHg h IHh];
    simpl; try reflexivity.
  - rewrite IHg, IHh; reflexivity.
  - rewrite IHg, IHh; reflexivity.
  - rewrite IHg, IHh; reflexivity.
Qed.

(* T26.  [[f -> g]] is the relative pseudo-complement of [[f]] relative
   to [[g]]; the adjunction rho <= [[f->g]]  iff  rho /\ [[f]] <= [[g]]:
   CGR18 Fact 3.3 at [[phi->psi]]; R13 Fact 5, p. 88. *)
Theorem sem_imp_adjunction : forall f g (R : iprop W),
  is_prop R ->
  (ple R (sem (FImp f g)) <-> ple (pmeet R (sem f)) (sem g)).
Proof.
  intros f g R HR; exact (imp_adjunction _ (sem f) (sem g) R HR).
Qed.

Theorem sem_imp_is_rpc : forall f g,
  is_rpc (sem f) (sem g) (sem (FImp f g)).
Proof.
  intros f g; exact (imp_is_rpc _ (sem f) (sem g)).
Qed.

(* The Heyting-algebra laws hold at the semantic values in particular:
   inq_heyting W (T11) applies verbatim since sem_and/sem_or/sem_imp are
   definitional. *)
Definition sem_heyting : HeytingLaws W := inq_heyting W.

(* ========================================================================== *)
(*  Part 7 — Sentence-level notions                                           *)
(* ========================================================================== *)

(* D25.  CGR18 Def 4.5 p. 62; CR11 Def 2.9(1-2) p. 4 (CR11's [phi] is
   alt_f, pitfall 10). *)
Definition info_f (f : form Atom) : state W := info (sem f).
Definition alt_f (f : form Atom) : iprop W := alt (sem f).

(* D26.  Sentence categories: CGR18 Def 4.9 p. 64; CR11 Defs 2.13-2.15
   pp. 5-6; R13 Defs 10-11 p. 92.
   ENCODING NOTE (ARTIFACT-v): [assertion] is rendered by the POSITIVE
   form noninquisitive (sem f) — the same convention D11 adopts for the
   abstract notions.  The sources' "not inquisitive" is classically
   equivalent; constructively, ~~-elimination across the disjunction
   clause of support has no uniform realiser, and the positive form makes
   every downstream theorem (T33-T52) stronger.  [question]'s negative
   form IS constructively equivalent to its positive form (the matrix
   ctruth w f = true is Boolean, hence stable) — see question_iff_taut. *)
Definition informative_f (f : form Atom) : Prop := informative (sem f).
Definition inquisitive_f (f : form Atom) : Prop := inquisitive (sem f).
Definition question (f : form Atom) : Prop := ~ informative_f f.
Definition assertion (f : form Atom) : Prop := noninquisitive (sem f).
Definition hybrid_f (f : form Atom) : Prop := hybrid (sem f).
Definition tautology_f (f : form Atom) : Prop := tautology_p (sem f).
Definition contradiction (f : form Atom) : Prop :=
  forall s, support s f -> empty s.

(* Equivalence of formulas (part of D28, needed for T36): CR11 Def 2.22
   p. 7. *)
Definition equiv (f g : form Atom) : Prop := peq (sem f) (sem g).

(* Two Boolean bridges used throughout: ctruth of Bang and Quest. *)
Lemma ctruth_bang : forall w f, ctruth w (Bang f) = ctruth w f.
Proof. intros w f; simpl; destruct (ctruth w f); reflexivity. Qed.

Lemma ctruth_quest : forall w f, ctruth w (Quest f) = true.
Proof. intros w f; simpl; destruct (ctruth w f); reflexivity. Qed.

Lemma ctruth_neg : forall w f, ctruth w (Neg f) = negb (ctruth w f).
Proof. intros w f; simpl; destruct (ctruth w f); reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(*  T31.  The syntactic projections denote the algebraic ones, and      *)
(*  every [[phi]] has decidable informative content — so T17/T20 apply  *)
(*  to sentences UNCONDITIONALLY: CGR18 Def 4.11 + Fact 4.12 p. 64;     *)
(*  R13 Fact 12 p. 97; CR11 Prop 2.12 p. 5.                             *)
(* -------------------------------------------------------------------- *)

Theorem sem_bang_peq : forall f, peq (sem (Bang f)) (pbang (sem f)).
Proof.
  intros f s; split.
  - intros H w Hw.
    apply (info_eq_truthset f w).
    exact (proj1 (bang_pointwise f s) H w Hw).
  - intros H; apply (bang_pointwise f s).
    intros w Hw; exact (proj1 (info_eq_truthset f w) (H w Hw)).
Qed.

Theorem sem_quest_peq : forall f, peq (sem (Quest f)) (pquest (sem f)).
Proof. intros f; exact (peq_refl _). Qed.

Theorem decided_info_sem : forall f, decided_info (sem f).
Proof.
  intros f w; destruct (ctruth w f) eqn:E.
  - left; apply (info_eq_truthset f w); exact E.
  - right; intros Hi.
    rewrite (proj1 (info_eq_truthset f w) Hi) in E; discriminate E.
Qed.

(* T32.  Characterisations of the trivial categories: CGR18 Facts 4.10
   p. 64, 4.15 p. 70; CR11 Props 2.23(1-2), 2.24(1,3,5). *)
Theorem question_iff_taut : forall f,
  question f <-> forall w, ctruth w f = true.
Proof.
  intros f; split.
  - intros Hq w; destruct (ctruth w f) eqn:E; [reflexivity | exfalso].
    apply Hq; intros Hni.
    rewrite (proj1 (info_eq_truthset f w) (Hni w)) in E; discriminate E.
  - intros H Hinf; apply Hinf.
    intros w; apply (info_eq_truthset f w); exact (H w).
Qed.

Theorem assertion_iff_support_truthset : forall f,
  assertion f <-> support (truthset f) f.
Proof.
  intros f; unfold assertion, noninquisitive; split; intros H.
  - exact (support_seq f _ _ (info_eq_truthset f) H).
  - exact (support_seq f _ _ (seq_sym _ _ (info_eq_truthset f)) H).
Qed.

Theorem assertion_iff_pow : forall f,
  assertion f <-> peq (sem f) (pow (truthset f)).
Proof.
  intros f; split.
  - intros Ha.
    apply peq_trans with (pow (info_f f)).
    + exact (noninq_1_2 (sem f) (sem_is_prop f) Ha).
    + intros s; split; intros H w Hw.
      * apply (info_eq_truthset f w), H, Hw.
      * apply (info_eq_truthset f w), H, Hw.
  - intros Hp.
    apply assertion_iff_support_truthset.
    apply (proj2 (Hp (truthset f))).
    intros w Hw; exact Hw.
Qed.

Theorem assertion_iff_greatest : forall f,
  assertion f <-> greatest (sem f) (truthset f).
Proof.
  intros f; split.
  - intros Ha; split.
    + apply assertion_iff_support_truthset; exact Ha.
    + intros t Ht w Hw.
      apply singleton_collapse.
      apply (persistence f t (single w)); [exact Ht |].
      intros v Hv; unfold single in Hv; subst v; exact Hw.
  - intros [Hg _]; apply assertion_iff_support_truthset; exact Hg.
Qed.

Theorem tautology_f_iff : forall f,
  tautology_f f <-> support ignorant f.
Proof. intros f; unfold tautology_f, tautology_p; tauto. Qed.

(* T33.  Assertions = truth-conditional sentences: CGR18 Fact 4.16
   p. 71; C16 Prop 2.2.8. *)
Theorem assertion_iff_tc : forall f,
  assertion f <-> truth_conditional f.
Proof.
  intros f; split.
  - intros Ha s; split.
    + intros Hs w Hw.
      apply singleton_collapse.
      apply (persistence f s (single w)); [exact Hs |].
      intros v Hv; unfold single in Hv; subst v; exact Hw.
    + intros H.
      apply (persistence f (truthset f) s).
      * apply assertion_iff_support_truthset; exact Ha.
      * intros w Hw; exact (H w Hw).
  - intros Htc.
    apply assertion_iff_support_truthset.
    apply Htc; intros w Hw; exact Hw.
Qed.

(* T34.  !phi is an assertion with the same informative content; ?phi is
   a question: CGR18 Facts 4.17(3), 4.18(1) pp. 71-72; CR11 Props
   2.12(2), 2.18(1); R13 pp. 95-96. *)
Theorem bang_assertion : forall f, assertion (Bang f).
Proof.
  intros f; apply assertion_iff_support_truthset.
  apply (bang_pointwise f (truthset (Bang f))).
  intros w Hw; unfold truthset in Hw.
  rewrite ctruth_bang in Hw; exact Hw.
Qed.

Theorem bang_info_f : forall f, seq (info_f (Bang f)) (info_f f).
Proof.
  intros f w; split; intros H.
  - apply (info_eq_truthset f w).
    pose proof (proj1 (info_eq_truthset (Bang f) w) H) as Ht.
    unfold truthset in *; rewrite ctruth_bang in Ht; exact Ht.
  - apply (info_eq_truthset (Bang f) w).
    unfold truthset; rewrite ctruth_bang.
    exact (proj1 (info_eq_truthset f w) H).
Qed.

Theorem quest_question : forall f, question (Quest f).
Proof.
  intros f; apply question_iff_taut.
  intros w; apply ctruth_quest.
Qed.

(* T35.  Division at sentence level, phi == !phi /\ ?phi — CR11's own
   constructive proof (s |= ~phi and s |= ~~phi force s empty):
   CGR18 Fact 4.13 p. 65; CR11 Prop 2.25 p. 8; R13 Fact 14. *)
Theorem division_f : forall f,
  equiv f (FAnd (Bang f) (Quest f)).
Proof.
  intros f s.
  change (support s f <-> support s (FAnd (Bang f) (Quest f))).
  rewrite support_and; split.
  - intros Hs; split.
    + apply (bang_pointwise f s); intros w Hw.
      apply singleton_collapse.
      apply (persistence f s (single w)); [exact Hs |].
      intros v Hv; unfold single in Hv; subst v; exact Hw.
    + left; exact Hs.
  - intros [Hb [Hs | Hn]]; [exact Hs |].
    apply empty_state; intros w Hw.
    pose proof (proj1 (bang_pointwise f s) Hb w Hw) as Ht.
    pose proof (proj1 (neg_pointwise f s) Hn w Hw) as Hf.
    rewrite Ht in Hf; discriminate Hf.
Qed.

(* T36.  Question and assertion characterisations: CR11 Props 2.23(3-4),
   2.24(4), pp. 7-8; R13 Fact 13 p. 97. *)
Theorem question_iff_contradiction_neg : forall f,
  question f <-> contradiction (Neg f).
Proof.
  intros f; split.
  - intros Hq s Hn w Hw.
    pose proof (proj1 (neg_pointwise f s) Hn w Hw) as Hf.
    rewrite (proj1 (question_iff_taut f) Hq w) in Hf; discriminate Hf.
  - intros Hc; apply question_iff_taut; intros w.
    destruct (ctruth w f) eqn:E; [reflexivity | exfalso].
    assert (Hn : support (single w) (Neg f)).
    { apply (neg_pointwise f (single w)).
      intros v Hv; unfold single in Hv; subst v; exact E. }
    exact (Hc (single w) Hn w eq_refl).
Qed.

Theorem question_iff_equiv_quest : forall f,
  question f <-> equiv f (Quest f).
Proof.
  intros f; split.
  - intros Hq s; split.
    + intros Hs; left; exact Hs.
    + intros [Hs | Hn]; [exact Hs |].
      apply empty_state; intros w Hw.
      pose proof (proj1 (neg_pointwise f s) Hn w Hw) as Hf.
      rewrite (proj1 (question_iff_taut f) Hq w) in Hf; discriminate Hf.
  - intros He; apply question_iff_taut; intros w.
    apply singleton_collapse.
    apply (proj2 (He (single w))).
    destruct (singleton_decides f w) as [Hf | Hn]; [left; exact Hf | right; exact Hn].
Qed.

Theorem assertion_iff_equiv_bang : forall f,
  assertion f <-> equiv f (Bang f).
Proof.
  intros f; split.
  - intros Ha s; split.
    + intros Hs; apply (bang_pointwise f s).
      exact (proj1 (proj1 (assertion_iff_tc f) Ha s) Hs).
    + intros Hb.
      apply (proj1 (assertion_iff_tc f) Ha s).
      exact (proj1 (bang_pointwise f s) Hb).
  - intros He.
    apply assertion_iff_support_truthset.
    apply (proj2 (He (truthset f))).
    apply (bang_pointwise f (truthset f)).
    intros w Hw; exact Hw.
Qed.

Theorem bang_idem_f : forall f, equiv (Bang (Bang f)) (Bang f).
Proof.
  intros f s.
  rewrite (bang_pointwise (Bang f) s), (bang_pointwise f s).
  split; intros H w Hw; pose proof (H w Hw) as Hc.
  - rewrite ctruth_bang in Hc; exact Hc.
  - rewrite ctruth_bang; exact Hc.
Qed.

Theorem quest_idem_f : forall f, equiv (Quest (Quest f)) (Quest f).
Proof.
  intros f s; split.
  - intros [Hq | Hn]; [exact Hq |].
    apply empty_state; intros w Hw.
    pose proof (proj1 (neg_pointwise (Quest f) s) Hn w Hw) as Hc.
    rewrite ctruth_quest in Hc; discriminate Hc.
  - intros Hq; left; exact Hq.
Qed.

(* T37.  Syntactic sufficient conditions for assertion-hood, via
   truth-conditionality: CGR18 Fact 4.17(1-5) p. 71; CR11 Prop 2.19
   pp. 6-7; C16 Props 2.3.6, 2.3.9. *)
Lemma atom_tc : forall p, truth_conditional (FAtom p).
Proof. intros p s; rewrite support_atom; simpl; tauto. Qed.

Lemma bot_tc : truth_conditional FBot.
Proof.
  intros s; rewrite support_bot; split.
  - intros He w Hw; destruct (He w Hw).
  - intros H w Hw; pose proof (H w Hw) as Hc; simpl in Hc; discriminate Hc.
Qed.

Lemma bang_tc : forall f, truth_conditional (Bang f).
Proof.
  intros f s; rewrite (bang_pointwise f s); split;
    intros H w Hw; pose proof (H w Hw) as Hc.
  - unfold truthset; rewrite ctruth_bang; exact Hc.
  - rewrite ctruth_bang in Hc; exact Hc.
Qed.

Lemma and_tc : forall f g,
  truth_conditional f -> truth_conditional g ->
  truth_conditional (FAnd f g).
Proof.
  intros f g Hf Hg s; rewrite support_and; split.
  - intros [H1 H2] w Hw; simpl.
    rewrite (proj1 (Hf s) H1 w Hw), (proj1 (Hg s) H2 w Hw); reflexivity.
  - intros H; split.
    + apply (Hg s) || apply (Hf s); intros w Hw;
        pose proof (H w Hw) as Hc; simpl in Hc;
        apply andb_true_iff in Hc; tauto.
    + apply (Hg s); intros w Hw;
        pose proof (H w Hw) as Hc; simpl in Hc;
        apply andb_true_iff in Hc; tauto.
Qed.

Lemma imp_tc : forall f g,
  truth_conditional g -> truth_conditional (FImp f g).
Proof.
  intros f g Hg s; rewrite support_imp; split.
  - intros H w Hw; simpl.
    destruct (ctruth w f) eqn:Ef; simpl; [| reflexivity].
    apply singleton_collapse.
    apply H.
    + intros v Hv; unfold single in Hv; subst v; exact Hw.
    + apply singleton_collapse; exact Ef.
  - intros H t Hts Hf.
    apply (Hg t); intros w Hw.
    assert (Hcf : ctruth w f = true).
    { apply singleton_collapse.
      apply (persistence f t (single w)); [exact Hf |].
      intros v Hv; unfold single in Hv; subst v; exact Hw. }
    pose proof (H w (Hts w Hw)) as Hc; simpl in Hc.
    rewrite Hcf in Hc; simpl in Hc; exact Hc.
Qed.

Theorem noninq_sufficient :
  (forall p, assertion (FAtom p)) /\
  assertion FBot /\
  (forall f, assertion (Neg f)) /\
  (forall f, assertion (Bang f)) /\
  (forall f g, assertion f -> assertion g -> assertion (FAnd f g)) /\
  (forall f g, assertion g -> assertion (FImp f g)).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - intros p; apply assertion_iff_tc, atom_tc.
  - apply assertion_iff_tc, bot_tc.
  - intros f; apply assertion_iff_tc, neg_tc.
  - intros f; apply bang_assertion.
  - intros f g Hf Hg; apply assertion_iff_tc, and_tc;
      apply assertion_iff_tc; assumption.
  - intros f g Hg; apply assertion_iff_tc, imp_tc;
      apply assertion_iff_tc; exact Hg.
Qed.

(* T38.  Syntactic sufficient conditions for question-hood: CGR18
   Fact 4.18(1-3) p. 72; CR11 Prop 2.18 p. 6. *)
Theorem noninf_sufficient :
  (forall f, question (Quest f)) /\
  (forall f g, question f -> question g -> question (FAnd f g)) /\
  (forall f g, question g -> question (FOr f g)) /\
  (forall f g, question g -> question (FImp f g)).
Proof.
  repeat split.
  - exact quest_question.
  - intros f g Hf Hg; apply question_iff_taut; intros w; simpl.
    rewrite (proj1 (question_iff_taut f) Hf w),
            (proj1 (question_iff_taut g) Hg w); reflexivity.
  - intros f g Hg; apply question_iff_taut; intros w; simpl.
    rewrite (proj1 (question_iff_taut g) Hg w).
    destruct (ctruth w f); reflexivity.
  - intros f g Hg; apply question_iff_taut; intros w; simpl.
    rewrite (proj1 (question_iff_taut g) Hg w).
    destruct (ctruth w f); reflexivity.
Qed.

(* T39.  The or-free fragment is truth-conditional: CR11 Cor 2.20 p. 7;
   CGR18 Fact 4.19 p. 72; R13 Fact 10 p. 93; C16 Prop 2.1.8 p. 49. *)
Theorem orfree_tc : forall f,
  orfree Atom f -> truth_conditional f.
Proof.
  intros f H; induction H.
  - apply atom_tc.
  - apply bot_tc.
  - apply and_tc; assumption.
  - apply imp_tc; assumption.
Qed.

Corollary orfree_assertion : forall f,
  orfree Atom f -> assertion f.
Proof. intros f H; apply assertion_iff_tc, orfree_tc, H. Qed.

(* T40.  [~phi] = {|~phi|} and [!phi] = {|phi|} in CR11's maximal-state
   sense: CR11 Prop 2.12 p. 5. *)
Lemma seq_trans : forall (s t u : state W),
  seq s t -> seq t u -> seq s u.
Proof. intros s t u H1 H2 w; rewrite (H1 w); apply H2. Qed.

Theorem neg_alt : forall f s,
  alt_f (Neg f) s <-> seq s (truthset (Neg f)).
Proof.
  intros f s; unfold alt_f.
  assert (Hni : noninquisitive (sem (Neg f))).
  { apply (assertion_iff_tc (Neg f)), neg_tc. }
  rewrite (noninq_alt W (sem (Neg f)) s (sem_is_prop (Neg f)) Hni).
  split; intros H.
  - exact (seq_trans _ _ _ H (info_eq_truthset (Neg f))).
  - exact (seq_trans _ _ _ H (seq_sym _ _ (info_eq_truthset (Neg f)))).
Qed.

Theorem bang_alt : forall f s,
  alt_f (Bang f) s <-> seq s (truthset f).
Proof.
  intros f s; unfold alt_f.
  assert (Hni : noninquisitive (sem (Bang f))) by (apply bang_assertion).
  rewrite (noninq_alt W (sem (Bang f)) s (sem_is_prop (Bang f)) Hni).
  assert (Hseq : seq (info (sem (Bang f))) (truthset f)).
  { apply seq_trans with (truthset (Bang f)).
    - exact (info_eq_truthset (Bang f)).
    - intros w; unfold truthset; rewrite ctruth_bang; tauto. }
  split; intros H.
  - exact (seq_trans _ _ _ H Hseq).
  - exact (seq_trans _ _ _ H (seq_sym _ _ Hseq)).
Qed.

(* T41.  Alternatives are maximal supporting states; two incomparable
   alternatives make a sentence inquisitive: CGR18 Def 4.5; CR11
   Def 2.13. *)
Theorem alt_f_max : forall f a,
  alt_f f a ->
  support a f /\ forall t, support t f -> sub a t -> sub t a.
Proof. intros f a [Ha Hmax]; split; assumption. Qed.

Theorem two_alts_inquisitive_f : forall f a b,
  alt_f f a -> alt_f f b -> ~ sub a b -> inquisitive_f f.
Proof.
  intros f a b Ha Hb Hab.
  exact (two_alts_inquisitive W (sem f) a b (sem_is_prop f) Ha Hb Hab).
Qed.

(* ========================================================================== *)
(*  Part 8 — Entailment and validity (per model)                              *)
(* ========================================================================== *)

(* D28.  Contexts are predicates on formulas (no List.In bookkeeping):
   CGR18 Def 4.6 p. 62; CR11 Defs 3.1, 3.5 pp. 9-10; C16 SS2.5. *)
Definition entails (Theta : form Atom -> Prop) (f : form Atom) : Prop :=
  forall s, (forall g, Theta g -> support s g) -> support s f.
Definition entails1 (f g : form Atom) : Prop :=
  forall s, support s f -> support s g.
Definition valid_in (f : form Atom) : Prop := forall s, support s f.

(* T42.  Entailment IS inclusion of propositions: CGR18 Def 4.6,
   Fact 2.23; CR11 p. 9. *)
Theorem entails_iff_ple : forall f g,
  entails1 f g <-> ple (sem f) (sem g).
Proof. intros f g; split; intros H s Hs; exact (H s Hs). Qed.

Theorem equiv_iff : forall f g,
  equiv f g <-> entails1 f g /\ entails1 g f.
Proof.
  intros f g; split.
  - intros H; split; intros s Hs; apply (H s); exact Hs.
  - intros [H1 H2] s; split; [apply H1 | apply H2].
Qed.

Lemma entails1_refl : forall f, entails1 f f.
Proof. intros f s Hs; exact Hs. Qed.

Lemma entails1_trans : forall f g h,
  entails1 f g -> entails1 g h -> entails1 f h.
Proof. intros f g h H1 H2 s Hs; apply H2, H1, Hs. Qed.

(* T43.  Validity is support at the ignorant state: CR11 Prop 3.6
   p. 10. *)
Theorem valid_iff_ignorant : forall f,
  valid_in f <-> support ignorant f.
Proof.
  intros f; split.
  - intros H; exact (H ignorant).
  - intros H s.
    apply (persistence f ignorant s); [exact H | intros w _; exact I].
Qed.

(* T44.  Validity = classical tautology + assertion; hence InqL <= CPL:
   CR11 Prop 3.7 p. 10, §3.3 p. 14. *)
Theorem valid_iff_taut_assertion : forall f,
  valid_in f <-> (forall w, ctruth w f = true) /\ assertion f.
Proof.
  intros f; split.
  - intros H; split.
    + intros w; apply singleton_collapse; exact (H (single w)).
    + apply assertion_iff_support_truthset; exact (H (truthset f)).
  - intros [Htaut Ha] s.
    apply (proj1 (assertion_iff_tc f) Ha s).
    intros w _; exact (Htaut w).
Qed.

Corollary valid_classical : forall f,
  valid_in f -> forall w, ctruth w f = true.
Proof.
  intros f H w; apply singleton_collapse; exact (H (single w)).
Qed.

(* T45.  The disjunction property, per model (CR11's proof through T43
   verbatim): CR11 Prop 3.9 p. 10. *)
Theorem disjunction_property_in : forall f g,
  valid_in (FOr f g) -> valid_in f \/ valid_in g.
Proof.
  intros f g H.
  destruct (H ignorant) as [Hf | Hg].
  - left; apply valid_iff_ignorant; exact Hf.
  - right; apply valid_iff_ignorant; exact Hg.
Qed.

(* T46.  Deduction theorem: CR11 Prop 3.10 p. 11; C16 Prop 2.5.16
   p. 65. *)
Theorem deduction_theorem : forall Theta f h,
  entails (fun g => Theta g \/ g = f) h <-> entails Theta (FImp f h).
Proof.
  intros Theta f h; split.
  - intros H s HT; rewrite support_imp; intros t Hts Hf.
    apply H; intros g [Hg | Hg].
    + apply (persistence g s t); [exact (HT g Hg) | exact Hts].
    + subst g; exact Hf.
  - intros H s Hall.
    assert (Himp : support s (FImp f h)).
    { apply H; intros g Hg; exact (Hall g (or_introl Hg)). }
    exact (Himp s (sub_refl s) (Hall f (or_intror eq_refl))).
Qed.

(* Single-premise form. *)
Corollary deduction_theorem1 : forall f h,
  entails1 f h <-> valid_in (FImp f h).
Proof.
  intros f h; split.
  - intros H s; rewrite support_imp; intros t Hts Hf; exact (H t Hf).
  - intros H s Hf; exact (H s s (sub_refl s) Hf).
Qed.

(* T47.  Support is closed under modus ponens: CR11 Thm 5.5 proof
   p. 22. *)
Theorem mp_closed : forall f g s,
  support s (FImp f g) -> support s f -> support s g.
Proof. intros f g s Himp Hf; exact (Himp s (sub_refl s) Hf). Qed.

(* T48.  Entailment into an assertion is classical: CR11 Prop 3.2 p. 9;
   C16 Prop 2.5.1. *)
Theorem entails_assertion_classical : forall f g,
  assertion g ->
  (entails1 f g <-> forall w, ctruth w f = true -> ctruth w g = true).
Proof.
  intros f g Hg; split.
  - intros H w Hf.
    apply singleton_collapse, H, singleton_collapse; exact Hf.
  - intros H s Hs.
    apply (proj1 (assertion_iff_tc g) Hg s).
    intros w Hw; apply H.
    apply singleton_collapse.
    apply (persistence f s (single w)); [exact Hs |].
    intros v Hv; unfold single in Hv; subst v; exact Hw.
Qed.

(* T49.  !phi is the strongest assertion entailed by phi: CR11 Prop 3.3
   pp. 9-10. *)
Theorem entails_bang : forall f, entails1 f (Bang f).
Proof.
  intros f s Hs; apply (bang_pointwise f s).
  intros w Hw; apply singleton_collapse.
  apply (persistence f s (single w)); [exact Hs |].
  intros v Hv; unfold single in Hv; subst v; exact Hw.
Qed.

Theorem bang_strongest_assertion : forall f g,
  assertion g -> (entails1 f g <-> entails1 (Bang f) g).
Proof.
  intros f g Hg; split.
  - intros H.
    apply (entails_assertion_classical (Bang f) g Hg).
    intros w Hw; rewrite ctruth_bang in Hw.
    exact (proj1 (entails_assertion_classical f g Hg) H w Hw).
  - intros H; exact (entails1_trans f (Bang f) g (entails_bang f) H).
Qed.

(* T50.  Questions entail only questions: CR11 Prop 3.4 p. 10. *)
Theorem question_entails_question : forall f g,
  question f -> entails1 f g -> question g.
Proof.
  intros f g Hq H; apply question_iff_taut; intros w.
  apply singleton_collapse, H, singleton_collapse.
  exact (proj1 (question_iff_taut f) Hq w).
Qed.

(* T51.  Double negation elimination is valid exactly for the
   truth-conditional sentences: C16 Prop 2.5.17 p. 65; CGR18 p. 52. *)
Theorem dne_valid_iff_tc : forall f,
  valid_in (FImp (Bang f) f) <-> truth_conditional f.
Proof.
  intros f; split.
  - intros H s; split.
    + intros Hs w Hw.
      apply singleton_collapse.
      apply (persistence f s (single w)); [exact Hs |].
      intros v Hv; unfold single in Hv; subst v; exact Hw.
    + intros Hc.
      apply (H s s (sub_refl s)).
      apply (bang_pointwise f s); exact Hc.
  - intros Htc s; rewrite support_imp; intros t Hts Hb.
    apply (Htc t).
    exact (proj1 (bang_pointwise f t) Hb).
Qed.

(* T52.  The LEM characterisation: ?phi is valid iff phi is valid or
   phi is a classical contradiction (packaging of CR11 §3.3 p. 14). *)
Theorem lem_valid_iff : forall f,
  valid_in (Quest f) <->
  support ignorant f \/ forall w, ctruth w f = false.
Proof.
  intros f; split.
  - intros H; destruct (H ignorant) as [Hf | Hn].
    + left; exact Hf.
    + right; intros w.
      exact (proj1 (neg_pointwise f ignorant) Hn w I).
  - intros [Hf | Hn]; apply valid_iff_ignorant.
    + left; exact Hf.
    + right; apply (neg_pointwise f ignorant).
      intros w _; exact (Hn w).
Qed.

Corollary lem_tc : forall f,
  truth_conditional f -> valid_in (Quest f) ->
  (forall w, ctruth w f = true) \/ (forall w, ctruth w f = false).
Proof.
  intros f Htc H.
  destruct (proj1 (lem_valid_iff f) H) as [Hf | Hn].
  - left; intros w; exact (proj1 (Htc ignorant) Hf w I).
  - right; exact Hn.
Qed.

(* ========================================================================== *)
(*  Part 9 — Axiomatisation and soundness (per model)                         *)
(* ========================================================================== *)

(* D29.  KP^n: the nine IPL schemes + Kreisel-Putnam + ATOMIC double
   negation (quantifying over p : Atom only — over formulas soundness
   would be FALSE, T56 / pitfall 15), with modus ponens as the only
   rule: CR11 App. A.1, A.3, A.5 pp. 31-32, p. 16, Cor 3.35 p. 18;
   R13 Thm 1 p. 91. *)
Inductive axiom : form Atom -> Prop :=
| ax1 : forall f g, axiom (FImp f (FImp g f))
| ax2 : forall f g h,
    axiom (FImp (FImp f (FImp g h)) (FImp (FImp f g) (FImp f h)))
| ax3 : forall f g, axiom (FImp f (FOr f g))
| ax4 : forall f g, axiom (FImp g (FOr f g))
| ax5 : forall f g h,
    axiom (FImp (FImp f h) (FImp (FImp g h) (FImp (FOr f g) h)))
| ax6 : forall f g, axiom (FImp (FAnd f g) f)
| ax7 : forall f g, axiom (FImp (FAnd f g) g)
| ax8 : forall f g, axiom (FImp f (FImp g (FAnd f g)))
| ax9 : forall f, axiom (FImp FBot f)
| ax_KP : forall f g h,
    axiom (FImp (FImp (Neg f) (FOr g h))
                (FOr (FImp (Neg f) g) (FImp (Neg f) h)))
| ax_DNatom : forall p : Atom, axiom (FImp (Bang (FAtom p)) (FAtom p)).

Inductive deriv (Theta : form Atom -> Prop) : form Atom -> Prop :=
| d_hyp : forall f, Theta f -> deriv Theta f
| d_ax  : forall f, axiom f -> deriv Theta f
| d_mp  : forall f g,
    deriv Theta (FImp f g) -> deriv Theta f -> deriv Theta g.

(* Introduction form for implication goals (support is frozen for simpl,
   so goals cannot be intro-ed through directly). *)
Lemma imp_intro : forall f g s,
  (forall t, sub t s -> support t f -> support t g) ->
  support s (FImp f g).
Proof. intros f g s H; rewrite support_imp; exact H. Qed.

(* T59.  The nine IPL schemes are valid — explicit sub_trans/persistence
   bookkeeping, no firstorder (design Block H): CR11 App. A.1 p. 32;
   R13 p. 91; C16 Prop 2.5.20. *)
Lemma valid_ax1 : forall f g, valid_in (FImp f (FImp g f)).
Proof.
  intros f g s; apply imp_intro; intros t Hts Hf.
  apply imp_intro; intros u Hut Hg.
  exact (persistence f t u Hf Hut).
Qed.

Lemma valid_ax2 : forall f g h,
  valid_in (FImp (FImp f (FImp g h)) (FImp (FImp f g) (FImp f h))).
Proof.
  intros f g h s; apply imp_intro; intros t Hts H1.
  apply imp_intro; intros u Hut H2.
  apply imp_intro; intros v Hvu Hf.
  pose proof (H1 v (sub_trans _ _ _ Hvu Hut) Hf) as Hgh.
  pose proof (H2 v Hvu Hf) as Hg.
  exact (Hgh v (sub_refl v) Hg).
Qed.

Lemma valid_ax3 : forall f g, valid_in (FImp f (FOr f g)).
Proof.
  intros f g s; apply imp_intro; intros t _ Hf; left; exact Hf.
Qed.

Lemma valid_ax4 : forall f g, valid_in (FImp g (FOr f g)).
Proof.
  intros f g s; apply imp_intro; intros t _ Hg; right; exact Hg.
Qed.

Lemma valid_ax5 : forall f g h,
  valid_in (FImp (FImp f h) (FImp (FImp g h) (FImp (FOr f g) h))).
Proof.
  intros f g h s; apply imp_intro; intros t _ H1.
  apply imp_intro; intros u Hut H2.
  apply imp_intro; intros v Hvu Hor.
  destruct Hor as [Hf | Hg].
  - exact (H1 v (sub_trans _ _ _ Hvu Hut) Hf).
  - exact (H2 v Hvu Hg).
Qed.

Lemma valid_ax6 : forall f g, valid_in (FImp (FAnd f g) f).
Proof.
  intros f g s; apply imp_intro; intros t _ [Hf _]; exact Hf.
Qed.

Lemma valid_ax7 : forall f g, valid_in (FImp (FAnd f g) g).
Proof.
  intros f g s; apply imp_intro; intros t _ [_ Hg]; exact Hg.
Qed.

Lemma valid_ax8 : forall f g, valid_in (FImp f (FImp g (FAnd f g))).
Proof.
  intros f g s; apply imp_intro; intros t _ Hf.
  apply imp_intro; intros u Hut Hg.
  split; [exact (persistence f t u Hf Hut) | exact Hg].
Qed.

Lemma valid_ax9 : forall f, valid_in (FImp FBot f).
Proof.
  intros f s; apply imp_intro; intros t _ He.
  exact (empty_state f t He).
Qed.

(* T60.  Kreisel-Putnam is valid — through neg_antecedent (T29), the
   dissertation's Cor 2.5.11 proof, never unfolding five nested foralls
   (pitfall 13): CR11 App. A.3 p. 32, p. 18; R13 Thm 1; C16 Cor 2.5.11
   p. 63. *)
Theorem KP_valid : forall f g h,
  valid_in (FImp (FImp (Neg f) (FOr g h))
                 (FOr (FImp (Neg f) g) (FImp (Neg f) h))).
Proof.
  intros f g h s; apply imp_intro; intros t _ Hant.
  pose proof (proj1 (neg_antecedent f (FOr g h) t) Hant) as Hor.
  destruct Hor as [Hg | Hh].
  - left; apply (proj2 (neg_antecedent f g t)); exact Hg.
  - right; apply (proj2 (neg_antecedent f h t)); exact Hh.
Qed.

(* T61.  Atomic double negation is valid — HERE Booleanness of V does
   the classical work (ARTIFACT-v): CR11 App. A.5 p. 32. *)
Theorem atomic_DN_valid_in : forall p : Atom,
  valid_in (FImp (Bang (FAtom p)) (FAtom p)).
Proof.
  intros p s; apply imp_intro; intros t _ Hb.
  rewrite support_atom; intros w Hw.
  exact (proj1 (bang_pointwise (FAtom p) t) Hb w Hw).
Qed.

(* T62.  Soundness, per model: CR11 Thm 3.34 / Cor 3.35 soundness half
   p. 18, Thm 5.5 p. 22; R13 Thm 1 "=>" p. 91. *)
Theorem axiom_valid : forall f, axiom f -> valid_in f.
Proof.
  intros f Hax; destruct Hax.
  - apply valid_ax1.
  - apply valid_ax2.
  - apply valid_ax3.
  - apply valid_ax4.
  - apply valid_ax5.
  - apply valid_ax6.
  - apply valid_ax7.
  - apply valid_ax8.
  - apply valid_ax9.
  - apply KP_valid.
  - apply atomic_DN_valid_in.
Qed.

Theorem soundness_in : forall (Theta : form Atom -> Prop) f,
  deriv Theta f -> entails Theta f.
Proof.
  intros Theta f Hd;
    induction Hd as [f HT | f Hax | f g Hd1 IH1 Hd2 IH2];
    intros s Hall.
  - exact (Hall f HT).
  - exact (axiom_valid f Hax s).
  - exact (mp_closed _ _ s (IH1 s Hall) (IH2 s Hall)).
Qed.

End Semantics.

(* ========================================================================== *)
(*  Part 10 — Models and cross-model validity                                 *)
(* ========================================================================== *)

(* D30.  Models; the record lives in Type (pitfall 17) so that valid can
   quantify over it (a Prop by impredicativity): CR11 Defs 2.1-2.2 p. 3,
   Def 3.5 p. 10; C16 §2.5. *)
Record model (Atom : Type) : Type := mkModel {
  Wm : Type;
  Vm : Wm -> Atom -> bool
}.
Arguments Wm {Atom} _.
Arguments Vm {Atom} _.
Arguments mkModel {Atom} _ _.

Definition valid {Atom : Type} (f : form Atom) : Prop :=
  forall (M : model Atom) (s : state (Wm M)), support (Vm M) s f.

Definition ent {Atom : Type} (Theta : form Atom -> Prop)
               (f : form Atom) : Prop :=
  forall M : model Atom, entails (Vm M) Theta f.

(* The canonical model of CR11 Defs 2.1-2.2: worlds are sets of atoms
   (here: Boolean valuations), used to instantiate CR11 statements; not
   needed for any MUST proof. *)
Definition canonW (Atom : Type) : Type := Atom -> bool.
Definition canonV (Atom : Type) (w : canonW Atom) (p : Atom) : bool := w p.
Definition canon (Atom : Type) : model Atom :=
  mkModel (canonW Atom) (canonV Atom).

(* T62, cross-model half: CR11 Cor 3.35 (soundness direction). *)
Theorem soundness : forall (Atom : Type) (Theta : form Atom -> Prop) f,
  deriv Theta f -> ent Theta f.
Proof.
  intros Atom Theta f Hd M; exact (soundness_in (Vm M) Theta f Hd).
Qed.

Theorem soundness_valid : forall (Atom : Type) (f : form Atom),
  deriv (fun _ => False) f -> valid f.
Proof.
  intros Atom f Hd M s.
  apply (soundness Atom (fun _ => False) f Hd M).
  intros g Hg; destruct Hg.
Qed.

(* T58, first half / T61 cross-model: atomic DNE is valid in EVERY
   model over ANY atom type: CR11 Remark 3.8 p. 10; R13 Thm 1. *)
Theorem atomic_DNE_valid : forall (Atom : Type) (p : Atom),
  valid (FImp (Bang (FAtom p)) (FAtom p)).
Proof.
  intros Atom p M s; exact (atomic_DN_valid_in (Vm M) p s).
Qed.

(* ========================================================================== *)
(*  Part 11 — Countermodels                                                   *)
(* ========================================================================== *)

(* D31.  The two-world model of CR11 Ex 2.16 / CGR18 §4.4 and the
   four-world model of CR11 Fig. 1 / CGR18 Fig. 4.1; worlds of W4 are
   (value of p, value of q), i.e. 11, 10, 01, 00.  All proofs are by
   explicit substates and worlds (ARTIFACT-iii), destructing pairs of
   Booleans (pitfall 14). *)
Module Counter.

Definition p : form bool := FAtom true.
Definition q : form bool := FAtom false.

Definition W2 := bool.
Definition V2 (w : W2) (_ : bool) : bool := w.
Definition M2 : model bool := mkModel W2 V2.

Definition W4 := (bool * bool)%type.
Definition V4 (w : W4) (a : bool) : bool := if a then fst w else snd w.
Definition M4 : model bool := mkModel W4 V4.

(* The state {11,10,01} of W4 — NOT ignorant: world 00 falsifies
   ~~(p \/ q) (pitfall 14). *)
Definition s4 : state W4 := fun w => fst w = true \/ snd w = true.

(* T54.  LEM fails: p \/ ~p is not supported by the ignorant state of
   W2, hence not valid — "p or not p is in CPL but not in InqL":
   CR11 §3.3 p. 14, Ex 2.16; CGR18 §4.4 p. 67. *)
Theorem LEM_fails_2 : ~ support V2 ignorant (FOr p (Neg p)).
Proof.
  intros [Hp | Hn].
  - discriminate (Hp false I).
  - discriminate (proj1 (neg_pointwise V2 p ignorant) Hn true I).
Qed.

Theorem LEM_not_valid_in : ~ valid_in V2 (FOr p (Neg p)).
Proof. intros H; exact (LEM_fails_2 (H ignorant)). Qed.

Theorem LEM_not_valid : ~ valid (FOr p (Neg p)).
Proof. intros H; exact (LEM_fails_2 (H M2 ignorant)). Qed.

(* ?p is a genuine question and genuinely inquisitive in W2 (note
   Quest p IS FOr p (Neg p)): CR11 Ex 2.16; CGR18 p. 67. *)
Theorem quest_p_question : question V2 (Quest p).
Proof. apply quest_question. Qed.

Theorem quest_p_inquisitive : inquisitive_f V2 (Quest p).
Proof.
  intros Hni.
  apply LEM_fails_2.
  apply (support_seq V2 (Quest p) (info (sem V2 (Quest p))) ignorant);
    [| exact Hni].
  intros w; split; [intros _; exact I | intros _].
  apply (info_eq_truthset V2 (Quest p) w).
  unfold truthset; rewrite ctruth_quest; reflexivity.
Qed.

(* T55.  DNE fails for the question ?p: ~~?p -> ?p is invalid in W2
   ("~~mu -> mu is always invalid when mu is a question", C16 p. 66):
   CR11 Remark 3.8; CGR18 p. 52. *)
Theorem DNE_fails_quest_2 :
  ~ valid_in V2 (FImp (Bang (Quest p)) (Quest p)).
Proof.
  intros H.
  apply LEM_fails_2.
  apply (H ignorant ignorant (sub_refl _)).
  apply (bang_pointwise V2 (Quest p) ignorant).
  intros w _; exact (ctruth_quest V2 w p).
Qed.

(* T56.  DNE fails for the hybrid p \/ q in W4 — CR11 Remark 3.8
   verbatim; the witnessing state is {11,10,01}: CGR18 p. 67. *)
Theorem DNE_fails_or_4 :
  ~ valid_in V4 (FImp (Bang (FOr p q)) (FOr p q)).
Proof.
  intros H.
  assert (Hor : support V4 s4 (FOr p q)).
  { apply (H s4 s4 (sub_refl _)).
    apply (bang_pointwise V4 (FOr p q) s4).
    intros [a b] [Ha | Hb]; simpl.
    - destruct a; [reflexivity | discriminate Ha].
    - destruct b; [destruct a; reflexivity | discriminate Hb]. }
  destruct Hor as [Hp | Hq].
  - discriminate (Hp (false, true) (or_intror eq_refl)).
  - discriminate (Hq (true, false) (or_introl eq_refl)).
Qed.

(* T57.  p \/ q is hybrid in W4, with the two incomparable alternatives
   |p| and |q|: CR11 Exs 2.11, 2.17, Fig. 1(b); CGR18 §4.4(c),
   Fig. 4.1(c); R13 Fig. 3. *)
Theorem or_hybrid_4 : hybrid_f V4 (FOr p q).
Proof.
  split.
  - intros Hall.
    pose proof (proj1 (info_eq_truthset V4 (FOr p q) (false, false))
                      (Hall (false, false))) as Ht.
    unfold truthset in Ht; simpl in Ht; discriminate Ht.
  - intros Hni.
    assert (Hseq : seq (info (sem V4 (FOr p q))) s4).
    { intros [a b]; split.
      - intros Hi.
        pose proof (proj1 (info_eq_truthset V4 (FOr p q) (a, b)) Hi) as Ht.
        unfold truthset in Ht; simpl in Ht.
        destruct a; [left; reflexivity | right; exact Ht].
      - intros [Ha | Hb];
          apply (info_eq_truthset V4 (FOr p q) (a, b));
          unfold truthset; simpl.
        + destruct a; [reflexivity | discriminate Ha].
        + destruct b; [destruct a; reflexivity | discriminate Hb]. }
    assert (Hs4 : support V4 s4 (FOr p q)).
    { exact (support_seq V4 (FOr p q) _ _ Hseq Hni). }
    destruct Hs4 as [Hp | Hq].
    + discriminate (Hp (false, true) (or_intror eq_refl)).
    + discriminate (Hq (true, false) (or_introl eq_refl)).
Qed.

Theorem or_alts_4 :
  alt_f V4 (FOr p q) (truthset V4 p) /\
  alt_f V4 (FOr p q) (truthset V4 q) /\
  ~ sub (truthset V4 p) (truthset V4 q).
Proof.
  split; [| split].
  - split.
    + left; exact (fun w Hw => Hw).
    + intros t Ht Hsub; destruct Ht as [Hp' | Hq'].
      * intros w Hw; exact (Hp' w Hw).
      * exfalso.
        discriminate (Hq' (true, false) (Hsub (true, false) eq_refl)).
  - split.
    + right; exact (fun w Hw => Hw).
    + intros t Ht Hsub; destruct Ht as [Hp' | Hq'].
      * exfalso.
        discriminate (Hp' (false, true) (Hsub (false, true) eq_refl)).
      * intros w Hw; exact (Hq' w Hw).
  - intros H; discriminate (H (true, false) eq_refl).
Qed.

Corollary or_inquisitive_4 : inquisitive_f V4 (FOr p q).
Proof. exact (proj2 or_hybrid_4). Qed.

(* T58.  Atomic DNE is valid in every model, yet NOT closed under
   uniform substitution — the point of CR11 Remark 3.8 (pitfall 15):
   CR11 Remark 3.8 p. 10, p. 16; R13 Thm 1; C16 p. 67. *)
Theorem no_uniform_substitution :
  valid (FImp (Bang p) p) /\
  ~ valid (subst true (FOr p q) (FImp (Bang p) p)).
Proof.
  split.
  - exact (atomic_DNE_valid bool true).
  - intros H; apply DNE_fails_or_4; intros s; exact (H M4 s).
Qed.

(* Consistency of KP^n, via the inhabited model W2: CR11 Cor 3.35. *)
Theorem consistency : ~ deriv (fun _ : form bool => False) FBot.
Proof.
  intros Hd.
  exact (soundness_valid bool FBot Hd M2 ignorant true I).
Qed.

End Counter.

(* ========================================================================== *)
(*  Part 12 — Notations (ASCII only, pitfall 18) and assumption audit         *)
(* ========================================================================== *)

Declare Scope inq_scope.
Delimit Scope inq_scope with inq.

Notation "P '<<=' Q" := (ple P Q) (at level 70) : inq_scope.
Notation "P '===' Q" := (peq P Q) (at level 70) : inq_scope.
Notation "s '|=' f 'wrt' V" := (support V s f)
  (at level 70, f at next level) : inq_scope.
Notation "f '|--' g 'wrt' V" := (entails1 V f g)
  (at level 70, g at next level) : inq_scope.

(* Test-compile the notations (pitfall 18). *)
Section NotationTest.
Open Scope inq_scope.
Variables (W Atom : Type) (V : W -> Atom -> bool).
Let test1 := fun (s : state W) (f : form Atom) => s |= f wrt V.
Let test2 := fun (f g : form Atom) => f |-- g wrt V.
Let test3 := fun (P Q : iprop W) => P <<= Q.
Let test4 := fun (P Q : iprop W) => P === Q.
End NotationTest.

(* --------------------------------------------------------------------------
   ASSUMPTION AUDIT.  Output of the commands below under Coq 8.20.1
   (2026-09-05): every one of the thirteen theorems prints "Closed under
   the global context" — no axioms, no classical principles, no
   extensionality anywhere in the MUST development (ARTIFACT-v: the
   Boolean valuation carries all the classical content of the sources).
   -------------------------------------------------------------------------- *)
Print Assumptions sem_is_prop.
Print Assumptions singleton_collapse.
Print Assumptions info_eq_truthset.
Print Assumptions imp_adjunction.
Print Assumptions alg_eq_sem.
Print Assumptions sem_imp_is_rpc.
Print Assumptions division_p.
Print Assumptions division_f.
Print Assumptions orfree_tc.
Print Assumptions dne_valid_iff_tc.
Print Assumptions Counter.LEM_fails_2.
Print Assumptions Counter.DNE_fails_or_4.
Print Assumptions soundness.

(* --------------------------------------------------------------------------
   COMPLETENESS ROUTE (T70, not attempted — see header).  CR11 Thm 3.34 /
   Cor 3.35 / Thm 5.5; R13 Thm 1 "<="; C16 Thm 3.3.2.  The proof needs:
   (1) resolutions res : form -> list form (C16 Def 2.4.1) with the
       equivalence phi -||- \/ res(phi) DERIVABLE in KP^n — the KP axiom
       is used exactly to push resolutions under (Neg f -> .);
   (2) classical completeness of the or-free fragment for IPL + atomic
       DNE over the canonical model (Kalmar-style, several hundred
       lines of Lindenbaum bookkeeping);
   (3) the split: Theta |= phi iff Theta |= some resolution alpha of phi
       (cross-model disjunction property via disjoint unions, C16
       Props 2.5.5-2.5.6), then (2) lifts alpha, and (1) closes.
   A separate file if ever attempted.
   -------------------------------------------------------------------------- *)
