(* ========================================================================== *)
(*  Ranta_GQ.v — Constructive generalized quantifiers, Sundholm style         *)
(*  FORMAL-ATLAS / atlas/mtt_ranta                                            *)
(* ========================================================================== *)
(*
   SOURCES
     [S89] Sundholm, G. (1989). "Constructive Generalized Quantifiers",
       Synthese 79(1): 1-12.  (PDF: ProQuest scan, obtained 2026-09-06;
       cited by FORMULA NUMBER.)  The moves used here:
       - a generalized quantifier is a PROPOSITION-FORMING OPERATION
         given by nominal definition in Martin-Lof type theory, not a
         relation between subsets of a fixed universe (pp. 2-3, forms
         (6)-(7); real vs nominal definition discussion p. 3);
       - "Most A are phi" is read mathematically as "more than half"
         and REQUIRES the presupposition a : Finite(A) — the quantifier
         is meaningless without the counting structure (p. 7, (VIII));
       - its definition (23), pp. 7-8: there is k >= [p(a)/2]+1 and an
         injection f : M(k) -> A with phi at every image point, where
         p(a) is the cardinal carried by the finiteness proof-object.
         Part 4's most_wit is exactly this: the image of the injection
         is a duplicate-free witness list drawn from the enumeration,
         of strict-majority size (2*k > n  <->  k >= [n/2]+1 on nat),
         each element carried with its proof.
       - the donkey contrast (24)-(26), pp. 8-9: "most men who own a
         donkey beat it" must quantify over the Sigma-type of owner-
         proof pairs, NOT over men with a conditional scope, "since the
         latter can be true even though no man who owns a donkey beats
         it" (p. 8) — compiled below as sundholm_donkey_contrast.
     [BC81] Barwise & Cooper (1981), "Generalized Quantifiers and Natural
       Language", L&P 4 (PDF in papers/foundations/) — the set-theoretic
       contrast class: conservativity, monotonicity profiles, the
       non-first-order-definability of "most".
     [R95] Ranta (1995), Type-Theoretical Grammar (as in Ranta.v) —
       supplies the host idiom: every = Pi, some = Sigma (§2.18-2.21).
       R95 HAS NO PROPORTIONAL QUANTIFIERS; this file is an extension in
       Ranta's idiom, not a formalization of R95 text.
   Design note: this file makes explicit the hidden premise that the
   atlas verifier kept (correctly) refusing to smuggle in: over an
   ABSTRACT CN : Type, "most" is not statable — the vocabulary has no
   counting structure.  Here the premise is a Section Variable
   (dom : list A, the enumeration), so every theorem displays it.

   WHAT IS FORMALIZED
     Part 1  The counting layer over an enumerated CN: cnt by filter;
             most_c (strict majority), some_c, every_c, no_c, half_c.
     Part 2  The entailment square on one domain: every => most (nonempty
             domain), most => some, no => not-most, the contrariety
             most(B) & most(not-B) => False, and the threshold form
             most_c <-> cnt >= [n/2]+1 ([S89] (23)'s least possible
             majority, proved rather than asserted).
     Part 3  Conservativity (in [BC81]'s format, via a decidable-equality
             hypothesis), right upward monotonicity of most and some,
             and the positive half of the donkey contrast: restrictor-
             most entails conditional-most (converse refuted in Part 5).
     Part 4  Sundholm proof objects: most_wit, a Sigma whose witness is a
             majority list of instances each carried with its proof; the
             equivalence most_wit <-> most_c (pigeonhole via
             NoDup_incl_length; the extracted witness is literally
             filter p dom); the bridges to Ranta's quantifiers:
             every (Pi) => most_wit => some (Sigma).
     Part 5  Countermodels over a 3-element type: some without most;
             most fails left upward monotonicity while some obeys it;
             the every/some/no verdicts on a domain do NOT determine the
             most verdict (a separation, NOT an undefinability theorem);
             exactly-half is not right upward monotone.

   NOT FORMALIZED (and why)
     * Genuine undefinability of "most" from every/some/no ([BC81] C13,
       via Rescher): a metatheorem quantifying over all first-order
       definitions — research-grade model theory, out of scope.  Part 5's
       most_separates is the honest finite fragment of it.
     * "Most" over an abstract (non-enumerated) CN: NOT-STATABLE in the
       Part-1 sense — [S89] p. 7 makes the same point by demanding the
       presupposition a : Finite(A); recorded rather than axiomatized.
     * [S89]'s infinite-domain quantifiers — INF (17), COUNT (18),
       Uc (19) via the second number class, More(A,B) (20), At-least
       (21), Almost-all (22): all need injections from N (or sigma) and
       are meaningless on the finite enumeration layer used here.
       FIN (16) is the converse case: on an enumerated domain every
       predicate satisfies it, so it trivializes rather than fails.
     * The [S89] p. 9 choice between counting owner-PAIRS (the Sigma
       type; a man with two donkeys counts twice) and counting owners
       once via the squashed subset type {x : A | B x true} (Nordstrom
       et al. 1986): sundholm_donkey_contrast uses the pair counting he
       argues for; the squash-counting variant needs propositional
       truncation machinery foreign to this file.
     * Sugaring: extending Ranta.v's Part-5 tree grammar with w_most
       would touch the pinned fragment; deferred to a re-audit pass.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   The counting layer lives in Prop (nat comparisons),
                    the proof-object layer in Type; the two meet in
                    most_wit_counts / most_counts_wit.  Mixing follows
                    Ranta.v's own practice (Part 5 uses =, /\).
     [ARTIFACT-ii]  Decidable predicates (A -> bool) at the counting
                    layer: counting needs decisions, and this is what
                    makes every countermodel a vm-computable fact.  The
                    Type-level layer takes B : A -> Type, no decision.
     [ARTIFACT-iii] The enumeration is a bare list; NoDup enters only as
                    a per-theorem hypothesis where counting witnesses
                    must not double-count (the Part 4 equivalence).
     [ARTIFACT-iv]  Zero axioms, zero global Parameters; countermodels
                    are concrete Inductives.  All audited theorems close
                    under the global context.
*)

Require Import List Arith Lia.
Import ListNotations.
Require Import mtt_ranta.Ranta.

(* ========================================================================== *)
(*  Part 1 — The counting layer over an enumerated CN                         *)
(* ========================================================================== *)

Section SundholmGQ.

Variable A : CN.

(* ---- general list lemmas (over any list of A; no reliance on recent
   stdlib additions beyond filter_In / NoDup_incl_length / in_dec) ---- *)

Lemma length_pos : forall l : list A, l <> nil -> 0 < length l.
Proof. intros [|a l] H; [congruence | cbn; lia]. Qed.

Lemma in_length_pos : forall (l : list A) (x : A), In x l -> 0 < length l.
Proof. intros [|a l] x H; [destruct H | cbn; lia]. Qed.

Lemma length_pos_ex : forall l : list A, 0 < length l -> {x : A | In x l}.
Proof.
  intros [|a l] H.
  - exfalso; cbn in H; lia.
  - exists a; apply in_eq.
Qed.

Lemma filter_ext_in_local : forall (f g : A -> bool) (l : list A),
  (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intros f g l; induction l as [|a l IH]; intros H; cbn; [reflexivity|].
  rewrite (H a (or_introl eq_refl)).
  rewrite (IH (fun x Hx => H x (or_intror Hx))).
  reflexivity.
Qed.

Lemma NoDup_filter_local : forall (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros f l H; induction H as [|a l Hnin Hnd IH]; cbn; [constructor|].
  destruct (f a); [|exact IH].
  constructor; [|exact IH].
  intro Hin; apply Hnin.
  destruct (proj1 (filter_In _ _ _) Hin) as [Hl _]; exact Hl.
Qed.

Lemma cnt_split_general : forall (l : list A) (r : A -> bool),
  length (filter r l) + length (filter (fun x => negb (r x)) l) = length l.
Proof.
  induction l as [|a l IH]; intros r; cbn; [reflexivity|].
  destruct (r a); cbn; specialize (IH r); lia.
Qed.

Lemma cnt_mono_general : forall (l : list A) (r s : A -> bool),
  (forall x, In x l -> r x = true -> s x = true) ->
  length (filter r l) <= length (filter s l).
Proof.
  induction l as [|a l IH]; intros r s Hrs; cbn; [lia|].
  assert (IH' := IH r s (fun x Hx => Hrs x (or_intror Hx))).
  destruct (r a) eqn:Er.
  - rewrite (Hrs a (or_introl eq_refl) Er); cbn; lia.
  - destruct (s a); cbn; lia.
Qed.

Lemma filter_filter_and : forall (r s : A -> bool) (l : list A),
  filter s (filter r l) = filter (fun x => andb (r x) (s x)) l.
Proof.
  intros r s l; induction l as [|a l IH]; cbn; [reflexivity|].
  destruct (r a); cbn; [destruct (s a); cbn|]; rewrite IH; reflexivity.
Qed.

(* Counting the conditional scope "not-r or s" splits into the non-r part
   plus the r-and-s part — the arithmetic behind the donkey contrast. *)
Lemma cnt_cond_split : forall (r s : A -> bool) (l : list A),
  length (filter (fun x => orb (negb (r x)) (s x)) l)
  = length (filter (fun x => negb (r x)) l)
    + length (filter (fun x => andb (r x) (s x)) l).
Proof.
  intros r s l; induction l as [|a l IH]; cbn; [reflexivity|].
  destruct (r a); destruct (s a); cbn; lia.
Qed.

(* ---- the enumerated CN: Sundholm's extra structure, as a Variable ---- *)

Variable dom : list A.

Definition cnt (r : A -> bool) : nat := length (filter r dom).

(* Strict majority — "most A are B" as more-than-half of the enumeration. *)
Definition most_c  (r : A -> bool) : Prop := 2 * cnt r > length dom.
Definition some_c  (r : A -> bool) : Prop := cnt r > 0.
Definition every_c (r : A -> bool) : Prop := cnt r = length dom.
Definition no_c    (r : A -> bool) : Prop := cnt r = 0.
(* A non-monotone specimen for the Part-5 profile countermodel. *)
Definition half_c  (r : A -> bool) : Prop := 2 * cnt r = length dom.

Variables p q : A -> bool.

(* ========================================================================== *)
(*  Part 2 — The entailment square on one domain                              *)
(* ========================================================================== *)

(* GQ-1.  every => most needs a nonempty domain (over [], every_c holds
   vacuously and most_c is false — displayed, not hidden). *)
Theorem every_c_most : dom <> nil -> every_c p -> most_c p.
Proof.
  intros Hne; unfold every_c, most_c, cnt.
  assert (H := length_pos dom Hne); lia.
Qed.

(* GQ-2.  most => some, unconditionally (a majority in an empty domain is
   impossible, so the implication is vacuous there). *)
Theorem most_c_some : most_c p -> some_c p.
Proof. unfold most_c, some_c, cnt; lia. Qed.

(* GQ-3.  no => not-most. *)
Theorem no_c_not_most : no_c p -> ~ most_c p.
Proof. unfold no_c, most_c, cnt; lia. Qed.

(* GQ-3b.  The threshold form: strict majority is exactly [S89] (23)'s
   "k >= [p(a)/2] + 1" — the least possible majority.  This discharges
   the header's arithmetic claim as a theorem rather than a comment.
   (lia will not open Nat.div on a variable numerator by itself; feed it
   the division equation and the mod bound.) *)
Theorem most_c_threshold :
  most_c p <-> cnt p >= Nat.div (length dom) 2 + 1.
Proof.
  unfold most_c.
  pose proof (Nat.div_mod_eq (length dom) 2) as Hd.
  pose proof (Nat.mod_upper_bound (length dom) 2 ltac:(lia)) as Hm.
  lia.
Qed.

(* GQ-4.  Contrariety: "most A are B" and "most A are not-B" cannot both
   hold — the counting split cnt B + cnt (not-B) = |A| forbids two
   strict majorities.  ([BC81]'s square-of-opposition corner for
   proportional determiners, constructively.) *)
Theorem most_contrary : most_c p -> most_c (fun x => negb (p x)) -> False.
Proof.
  unfold most_c, cnt; intros H1 H2.
  assert (Hs := cnt_split_general dom p); lia.
Qed.

(* ========================================================================== *)
(*  Part 3 — Conservativity and monotonicity ([BC81]'s checklist)             *)
(* ========================================================================== *)

(* GQ-5.  Right upward monotonicity of most: enlarging the scope on the
   domain preserves a majority. *)
Theorem most_mono_right :
  (forall x, In x dom -> p x = true -> q x = true) ->
  most_c p -> most_c q.
Proof.
  intros Hpq; unfold most_c, cnt.
  assert (H := cnt_mono_general dom p q Hpq); lia.
Qed.

(* GQ-6.  Same for some (the contrast term for Part 5's left-argument
   asymmetry). *)
Theorem some_mono_right :
  (forall x, In x dom -> p x = true -> q x = true) ->
  some_c p -> some_c q.
Proof.
  intros Hpq; unfold some_c, cnt.
  assert (H := cnt_mono_general dom p q Hpq); lia.
Qed.

(* GQ-6b.  The positive half of [S89]'s donkey contrast (pp. 8-9): the
   Sigma-restrictor reading ("most of those who are r are s", counting
   over the separated subset filter r l) ENTAILS the conditional-scope
   reading ("most are: if r then s").  The converse fails — that is
   sundholm_donkey_contrast in Part 5, Sundholm's own argument. *)
Theorem sub_most_implies_cond : forall (l : list A) (r s : A -> bool),
  2 * length (filter s (filter r l)) > length (filter r l) ->
  2 * length (filter (fun x => orb (negb (r x)) (s x)) l) > length l.
Proof.
  intros l r s H.
  rewrite filter_filter_and in H.
  rewrite cnt_cond_split.
  pose proof (cnt_split_general l r) as Hs.
  lia.
Qed.

Section Conservativity.

(* Membership in the enumeration must be decidable to even STATE
   D(A)(B) <-> D(A)(A cap B) in [BC81]'s format; the hypothesis enters
   here, per-theorem, never globally. *)
Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

Definition memb (x : A) : bool := if in_dec eq_dec x dom then true else false.

Lemma memb_in : forall x, In x dom -> memb x = true.
Proof.
  intros x Hx; unfold memb.
  destruct (in_dec eq_dec x dom); [reflexivity | contradiction].
Qed.

Lemma filter_restrict : forall r : A -> bool,
  filter (fun x => andb (memb x) (r x)) dom = filter r dom.
Proof.
  intros r; apply filter_ext_in_local.
  intros x Hx; rewrite (memb_in x Hx); reflexivity.
Qed.

(* GQ-7.  Conservativity for all four counting quantifiers at once.  In
   the enumerated setting this is nearly definitional — counting already
   happens inside the restrictor — which is itself the type-theoretic
   explanation of WHY natural-language determiners are conservative:
   the CN supplies the domain of quantification ([R95] types-as-CNs,
   [BC81] C1). *)
Theorem gq_conservative : forall r : A -> bool,
  (most_c  (fun x => andb (memb x) (r x)) <-> most_c  r) /\
  (some_c  (fun x => andb (memb x) (r x)) <-> some_c  r) /\
  (every_c (fun x => andb (memb x) (r x)) <-> every_c r) /\
  (no_c    (fun x => andb (memb x) (r x)) <-> no_c    r).
Proof.
  intros r; unfold most_c, some_c, every_c, no_c, cnt.
  rewrite (filter_restrict r); tauto.
Qed.

End Conservativity.

(* ========================================================================== *)
(*  Part 4 — Sundholm proof objects and the bridge to Pi/Sigma                *)
(* ========================================================================== *)

(* The canonical proof object of "most A are B" — [S89] (23), pp. 7-8:
   "(exists k : N)(k >= [p(a)/2]+1 & (exists f : M(k) -> A)(f is an
   injection & (forall y : M(k)) phi(ap(f,y))))".  The image of
   Sundholm's injection from the canonical k-element set M(k) is here a
   duplicate-free witness list drawn from the enumeration (NoDup + incl
   = injectivity + range), of strict-majority size (on nat,
   2*k > n <-> k >= [n/2]+1), EACH ELEMENT CARRIED WITH ITS PROOF of B.
   A Sigma over lists rather than elements — a construction, not a
   cardinality side-condition. *)
Definition most_wit (B : A -> Type) : Type :=
  { w : list A &
      ((NoDup w * incl w dom) *
       ((2 * length w > length dom) * (forall x : A, In x w -> B x)))%type }.

(* GQ-8.  Soundness of the proof object: a majority witness list yields
   the counting fact.  The pigeonhole is NoDup_incl_length — the witness
   list injects into filter p dom. *)
Theorem most_wit_counts :
  most_wit (fun x => p x = true) -> most_c p.
Proof.
  intros [w [[Hw Hincl] [Hlen Hall]]].
  assert (Hsub : incl w (filter p dom)).
  { intros x Hx; apply (proj2 (filter_In _ _ _)).
    split; [exact (Hincl x Hx) | exact (Hall x Hx)]. }
  assert (Hle := NoDup_incl_length Hw Hsub).
  unfold most_c, cnt; lia.
Qed.

(* GQ-9.  Completeness: from the counting fact the canonical witness is
   COMPUTED — it is literally filter p dom.  NoDup dom is needed here
   (and only here): a duplicated enumeration would let the count exceed
   the distinct witnesses. *)
Theorem most_counts_wit :
  NoDup dom -> most_c p -> most_wit (fun x => p x = true).
Proof.
  intros Hnd Hm; exists (filter p dom); repeat split.
  - apply NoDup_filter_local; exact Hnd.
  - intros x Hx; destruct (proj1 (filter_In _ _ _) Hx) as [Hin _]; exact Hin.
  - exact Hm.
  - intros x Hx; destruct (proj1 (filter_In _ _ _) Hx) as [_ Hp]; exact Hp.
Qed.

(* GQ-10.  The bridge down to Ranta's Sigma: a majority witness yields an
   existential witness — most => some at the proof-object level,
   unconditionally, by taking the head of the witness list. *)
Theorem most_wit_some : forall B : A -> Type,
  most_wit B -> some A B.
Proof.
  intros B [w [[Hw Hincl] [Hlen Hall]]].
  destruct w as [|x w'].
  - exfalso; cbn in Hlen; lia.
  - exists x; apply Hall, in_eq.
Qed.

(* GQ-11.  The bridge down from Ranta's Pi: universal proof + nonempty
   NoDup enumeration give the majority witness — the whole domain. *)
Theorem every_most_wit : forall B : A -> Type,
  dom <> nil -> NoDup dom -> every A B -> most_wit B.
Proof.
  intros B Hne Hnd HB; exists dom; repeat split.
  - exact Hnd.
  - apply incl_refl.
  - assert (H := length_pos dom Hne); lia.
  - intros x _; exact (HB x).
Qed.

End SundholmGQ.

(* ========================================================================== *)
(*  Part 5 — Countermodels (concrete, computable)                             *)
(* ========================================================================== *)

Inductive three : Set := th1 | th2 | th3.
Definition dom3 : list three := [th1; th2; th3].
Definition p_one (x : three) : bool :=
  match x with th1 => true | _ => false end.
Definition p_two (x : three) : bool :=
  match x with th3 => false | _ => true end.

(* GQ-C1.  some does not give most: one witness out of three. *)
Theorem some_not_most :
  some_c three dom3 p_one /\ ~ most_c three dom3 p_one.
Proof.
  unfold some_c, most_c, cnt, dom3; cbn; split; lia.
Qed.

(* GQ-C2.  most is NOT left upward monotone: a majority in [th1] drowns
   in the larger domain.  (Contrast GQ-C3: some survives any extension.) *)
Theorem most_not_left_upward :
  incl [th1] dom3 /\
  most_c three [th1] p_one /\ ~ most_c three dom3 p_one.
Proof.
  repeat split.
  - intros x Hx; destruct Hx as [Hx|[]]; subst x; unfold dom3; apply in_eq.
  - unfold most_c, cnt; cbn; lia.
  - unfold most_c, cnt, dom3; cbn; lia.
Qed.

(* GQ-C3.  some IS left upward monotone — the profile that separates the
   Aristotelian corner from the proportional determiner. *)
Theorem some_left_upward : forall (A : CN) (l l' : list A) (r : A -> bool),
  incl l l' -> some_c A l r -> some_c A l' r.
Proof.
  intros A l l' r Hincl Hs; unfold some_c, cnt in *.
  destruct (length_pos_ex A (filter r l)) as [x Hx]; [lia|].
  destruct (proj1 (filter_In _ _ _) Hx) as [Hin Hr].
  assert (Hx' : In x (filter r l')).
  { apply (proj2 (filter_In _ _ _)); split; [exact (Hincl x Hin) | exact Hr]. }
  assert (H := in_length_pos A (filter r l') x Hx'); lia.
Qed.

(* GQ-C4.  THE SEPARATION: on the same domain, two predicates agree on
   the every/some/no verdicts and disagree on most.  So the Aristotelian
   verdicts do not determine the proportional one.  This is the honest
   finite fragment of [BC81]'s undefinability of "most" (C13) — the full
   metatheorem quantifies over all first-order definitions and is out of
   scope, as the header records. *)
Theorem most_separates :
  (some_c  three dom3 p_one <-> some_c  three dom3 p_two) /\
  (every_c three dom3 p_one <-> every_c three dom3 p_two) /\
  (no_c    three dom3 p_one <-> no_c    three dom3 p_two) /\
  most_c three dom3 p_two /\ ~ most_c three dom3 p_one.
Proof.
  unfold some_c, every_c, no_c, most_c, cnt, dom3; cbn.
  repeat split; intros; lia.
Qed.

(* GQ-C5.  exactly-half is not right upward monotone: growing the scope
   destroys it.  Monotonicity profiles are how [BC81] classify
   determiners; half sits outside every monotone class. *)
Theorem half_not_mono_right :
  (forall x : three, p_one x = true -> p_two x = true) /\
  half_c three [th1; th2] p_one /\ ~ half_c three [th1; th2] p_two.
Proof.
  split; [|split].
  - intros x H; destruct x; cbn in *; congruence.
  - unfold half_c, cnt; cbn; lia.
  - unfold half_c, cnt; cbn; lia.
Qed.

(* GQ-C6.  Sundholm's donkey contrast, compiled ([S89] (24)-(26),
   pp. 8-9).  "Most men who own a donkey beat it" must quantify over the
   Sigma-type of owner-proof pairs — Ranta.v's donkey_ctx, exactly — and
   NOT over men with the conditional scope "if he owns a donkey he beats
   it", "since the latter can be true even though no man who owns a
   donkey beats it" (p. 8).  Scenario: three men, one kind owner.  The
   conditional reading holds of a majority of men (the two non-owners,
   vacuously); the pair reading fails; and no owner beats his donkey. *)
Inductive man3 : Set := m1 | m2 | m3.
Inductive donkey1 : Set := d1.
Definition owns  (m : man3) (_ : donkey1) : bool :=
  match m with m1 => true | _ => false end.
Definition beats (_ : man3) (_ : donkey1) : bool := false.
Definition dom_men : list man3 := [m1; m2; m3].
(* What gets counted in the correct reading are owner-proof PAIRS
   ([S89] p. 9: "not elements of A ... but ordered pairs"). *)
Definition dom_owners : list (man3 * donkey1) := [(m1, d1)].
(* The wrong reading's scope: "if he owns a donkey, he beats it". *)
Definition cond_reading (m : man3) : bool :=
  orb (negb (owns m d1)) (beats m d1).

Theorem sundholm_donkey_contrast :
  most_c man3 dom_men cond_reading /\
  ~ most_c ((man3 * donkey1)%type) dom_owners (fun z => beats (fst z) (snd z)) /\
  (forall z, In z dom_owners -> beats (fst z) (snd z) = false).
Proof.
  split; [|split].
  - unfold most_c, cnt, dom_men; cbn; lia.
  - unfold most_c, cnt, dom_owners; cbn; lia.
  - intros z Hz; destruct Hz as [Hz|[]]; subst z; reflexivity.
Qed.

(* ========================================================================== *)
(*  Part 6 — Assumption audit                                                 *)
(* ========================================================================== *)
(* Expected under Coq 8.20.1: every theorem below prints "Closed under
   the global context" — zero axioms, zero Parameters (ARTIFACT-iv). *)
Print Assumptions every_c_most.
Print Assumptions most_c_some.
Print Assumptions no_c_not_most.
Print Assumptions most_c_threshold.
Print Assumptions sub_most_implies_cond.
Print Assumptions most_contrary.
Print Assumptions most_mono_right.
Print Assumptions some_mono_right.
Print Assumptions gq_conservative.
Print Assumptions most_wit_counts.
Print Assumptions most_counts_wit.
Print Assumptions most_wit_some.
Print Assumptions every_most_wit.
Print Assumptions some_not_most.
Print Assumptions most_not_left_upward.
Print Assumptions some_left_upward.
Print Assumptions most_separates.
Print Assumptions half_not_mono_right.
Print Assumptions sundholm_donkey_contrast.
