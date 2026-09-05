(* ========================================================================== *)
(*  RSA.v — the Rational Speech Act model in exact rational arithmetic        *)
(*  FORMAL-ATLAS / atlas/probabilistic                                        *)
(* ========================================================================== *)
(*
   SOURCES
     [GF16] Goodman, N. & Frank, M. (2016). Pragmatic language
       interpretation as probabilistic inference. TiCS 20(11):818-829.
       [eqs. (1)-(4), Box 1 eq. (II); the Figure-1 faces example]
     [FG12] Frank, M. & Goodman, N. (2012). Predicting pragmatic
       reasoning in language games. Science 336:998.  [eqs. (1)-(2);
       Supplement (S1)-(S4): softmax, surprisal - cost, uniform literal
       listener, the size principle]
     [B16]  Bergen, L., Levy, R. & Goodman, N. (2016). Pragmatic
       reasoning through semantic inference. S&P 9(20).  [§3.1
       eqs. (8)-(11) depth-n recursion (with the paper's own o = w
       collapse, p. 20:14); the p |-> p/(2p+1) table p. 20:16; §3.2
       symmetry; §4.1.1 Lemmas 1-2; §4.3 restrictions (i)-(ii);
       lexical uncertainty eqs. (26)-(29)]
     [LG17] Lassiter, D. & Goodman, N. (2017). Adjectival vagueness in a
       Bayesian model of interpretation. Synthese 194.  [§2.1 eqs.
       (3)-(6) probability axioms and conditioning; §2.3-2.5 eqs.
       (9)-(14); §3 eqs. (15)-(20) the cookies scalar example, alpha=4]
     [GL15] Goodman, N. & Lassiter, D. (2015). Probabilistic semantics
       and pragmatics. Handbook of Contemporary Semantic Theory.  [§3
       eqs. (5)-(6): the multiplicative form P(ut|val) ~ P(ut) *
       P_listener(val|ut)^alpha — the encoding adopted here, literally]
   Design document: formalizing_formal_semantics/atlas/designs/rsa.md.

   THE SOFTMAX ENCODING (the file's one substantive encoding move).
     The sources define S(u|w) ~ exp(alpha * (log L(w|u) - c(u))).  For
     L(w|u) > 0 this IS  L(w|u)^alpha * e^(-alpha c(u)); for L(w|u) = 0
     the sources set it to 0 (LG17 p. 12; B16 p. 20:15, "exp(alpha ln 0)
     = 0").  With alpha : nat and a POSITIVE WEIGHT costw u standing for
     the rational surrogate of e^(-alpha c(u)), the softmax is the exact
     rational identity
         S(u|w) ~ (L u w)^alpha * costw u
     which is literally GL15 eq. (5) with costw = P(ut), the "language
     prior".  Only ratios of weights matter.  The equivalence with the
     real-valued exp/log softmax is an encoding lemma ABOUT the reals
     and is deliberately not a Coq theorem (it would need Reals); where
     an example's weights are irrational (e^-4, e^-16), the module uses
     a rational surrogate and says so.
   SIGN NOTE.  GF16 Box 1 eq. (II) prints U = log P_Lit + cost(u); FG12
     (S2), B16 eqs. (3)/(9) and LG17 eq. (10) all subtract the cost.
     The file follows the minus convention and records the discrepancy.

   WHAT IS FORMALIZED
     Part 1  QSum: finite-sum algebra over Q (qsum, qpow, normalize with
             Qred, and their order/extensionality lemmas).
     Part 2  Dist: list-indexed distributions (IsDist).
     Part 3  The RSA tower over abstract finite W, U with a Boolean
             lexicon: L0, S_of, L_of, Ln, Sn, S1, L1; decidable
             definedness (consistent, expressible).
     Part 4  Literal listener: distribution iff consistency, exact
             failure mode, support, L0-as-conditioning (LG17 (4)/(9)),
             tautology, uniform-prior cardinality form (FG12 (S3)).
     Part 5  Speaker: distribution iff expressibility, support,
             truthfulness, the alpha = 0 degeneracy.
     Part 6  Pragmatic listener: distribution iff (witness form and the
             consistency form), support, Bayes/product/odds forms,
             proportionality determines the distribution.
     Part 7  Ordering: more specific utterances get weakly/strictly
             higher L0 and S1 (any positive prior; costs compared
             explicitly); the speaker-to-listener lifting lemma; the
             size principle (FG12 (2)/(S4)).
     Part 8  Invariance: semantic equivalence is invisible at every
             depth for every cost assignment (B16 §4.1.1 Lemmas 1-2,
             generalized), hence NO M-implicatures in base RSA;
             permutation well-definedness of the list encoding.
     Part 9  Depth n: support and distribution theorems at every level
             under B16's restrictions (i)-(ii).
     Part 10 Scalar implicature, exact: L1(w1|some) = 3/4 vs 1/4
             (alpha = 1), 17/18 vs 1/18 (alpha = 4), 7/8 vs 1/8
             (depth 3); the L0 non-derivation (both 1/2); and the
             preference at EVERY alpha > 0, symbolically (LG17 fn. 6).
     Part 11 Worked examples: GF16 faces; B16 two-world table
             L_n(all|some) = 1/4, 1/6, 1/8, 1/10; LG17 cookies at
             alpha = 4 (exact 1/6486 etc., with a fidelity note on the
             paper's printed ~.015).
     Part 12 Symmetry (B16 §3.2): flat costs cannot break w1/w2
             symmetry (1/2 = 1/2); size-weighted costs do (2/3 vs 1/3).
     Part 13 Assumption audit.

   NOT FORMALIZED (and why)
     * Reals, exp/log, continuous priors, MCMC (LG17 §4.4): the encoding
       lemma above is the boundary; everything here is exact Q.
     * B16 lexical uncertainty (eqs. (26)-(29), Figs. 5-6 Horn game) and
       the closed form L_n(all|some) = 1/(2n+2); LG17 threshold
       semantics on a degree grid: STRETCH in the design, dropped for
       budget this session (the design has full plans T36-T45).
     * B16's observation/world distinction (the paper itself collapses
       it, p. 20:14), speaker uncertainty and QUD relevance (GF16 Box 1
       (III)-(IV)), IBR/IQR equilibria, empirical fits.

   REPRESENTATION CHOICES AND ARTIFACT CLASSES
     [ARTIFACT-i]   None: the only recursion is Ln : nat -> ..., a
                    checked absence.
     [ARTIFACT-ii]  (a) The sources' delta/indicator L(u,w) in {0,1} is
                    bool with if (site: L0_raw).  (b) B16's (o,w) is
                    collapsed to w — the paper's own move.  (c) No
                    utterance syntax: the lexicon meaning : U -> W ->
                    bool IS the theory's interface (B16 eq. (1), GF16
                    [[u]], FG12's Boolean functions); word length enters
                    only through cost tables.
     [ARTIFACT-iii] (a) exp/log eliminated by the nat-exponent + weight
                    encoding (header).  (b) Qdiv is TOTAL (x/0 = 0): an
                    undefined RSA distribution is the zero function, so
                    every distribution theorem is an IFF against a
                    decidable condition, with a companion _undefined
                    theorem giving the exact failure mode.  (c) Qred
                    inside normalize is theory-invisible
                    (normalize_spec) and computation-essential.
                    (d) closed numeric claims are vm_compute on ==/<.
     [ARTIFACT-iv]  No finite types/sets/big operators/probability
                    monad in the stdlib: finite sets are lists with In,
                    Sigma is qsum, cardinality is length-of-filter,
                    IsDist is list-indexed; the spurious list order is
                    discharged by the permutation theorem (T25).
     [ARTIFACT-v]   Sources are classical and real-valued; here
                    meanings are bool, definedness is existsb, order on
                    Q is decidable.  Stronger-than-source hypotheses
                    are flagged where used: NoDup for the cardinality
                    form (T6, T20); coverage (all worlds expressible,
                    all alternatives consistent) for the depth-n
                    theorems (T26-T27) — B16's restrictions (i)-(ii)
                    made global.
     Zero axioms: every audited theorem closes under the global context.
*)

From Coq Require Import QArith Qreduction Lqa Lia List Bool Permutation.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================== *)
(*  Part 1 — QSum: finite sums, powers, normalization                         *)
(* ========================================================================== *)

Module QSum.

(* D1.  Sigma of every normalizer (FG12 eq. 1; LG17 (12), (14); B16
   (8)-(11)). *)
Definition qsum (l : list Q) : Q := fold_right Qplus 0 l.

(* D2.  p^alpha with a nat exponent (GF16 alpha; B16 lambda; LG17
   alpha; GL15 "power ... alpha").  Private: Qpower has a Z exponent
   and no base-monotonicity lemmas (pitfall 7). *)
Fixpoint qpow (q : Q) (n : nat) : Q :=
  match n with O => 1 | S m => q * qpow q m end.

(* D3.  The "proportional-to" of every source, made explicit; Qred is
   essential for computation and invisible to the theory
   (ARTIFACT-iii). *)
Definition normalize {A : Type} (f : A -> Q) (l : list A) (a : A) : Q :=
  Qred (f a / qsum (map f l)).

Lemma normalize_spec : forall (A : Type) (f : A -> Q) (l : list A) (a : A),
  normalize f l a == f a / qsum (map f l).
Proof. intros; apply Qred_correct. Qed.

Lemma ne_of_lt : forall x, 0 < x -> ~ x == 0.
Proof. intros x H He; lra. Qed.

(* ---- qsum algebra (T1) ---- *)

Lemma qsum_nonneg : forall l,
  (forall x, In x l -> 0 <= x) -> 0 <= qsum l.
Proof.
  induction l as [| a l IH]; simpl; intros H; [lra |].
  assert (Ha := H a (or_introl eq_refl)).
  assert (Hl : 0 <= qsum l) by (apply IH; intros x Hx; apply H; right; exact Hx).
  lra.
Qed.

Lemma qsum_pos_of_mem : forall l,
  (forall x, In x l -> 0 <= x) ->
  forall y, In y l -> 0 < y -> 0 < qsum l.
Proof.
  induction l as [| a l IH]; simpl; intros H y Hy Hpos; [destruct Hy |].
  destruct Hy as [-> | Hy].
  - assert (Hl : 0 <= qsum l) by (apply qsum_nonneg; intros x Hx; apply H; right; exact Hx).
    lra.
  - assert (Ha := H a (or_introl eq_refl)).
    assert (Hl : 0 < qsum l).
    { apply (IH (fun x Hx => H x (or_intror Hx)) y Hy Hpos). }
    lra.
Qed.

Lemma qsum_zero_iff : forall l,
  (forall x, In x l -> 0 <= x) ->
  (qsum l == 0 <-> forall x, In x l -> x == 0).
Proof.
  induction l as [| a l IH]; simpl; intros H; split.
  - intros _ x [].
  - intros _; reflexivity.
  - intros Hs x Hx.
    assert (Ha := H a (or_introl eq_refl)).
    assert (Hl : 0 <= qsum l) by (apply qsum_nonneg; intros z Hz; apply H; right; exact Hz).
    destruct Hx as [-> | Hx]; [lra |].
    apply (proj1 (IH (fun z Hz => H z (or_intror Hz)))); [lra | exact Hx].
  - intros Hall.
    assert (Ha := Hall a (or_introl eq_refl)).
    assert (Hl : qsum l == 0).
    { apply (proj2 (IH (fun z Hz => H z (or_intror Hz)))).
      intros x Hx; apply Hall; right; exact Hx. }
    lra.
Qed.

Lemma qsum_map_ext_in : forall (A : Type) (f g : A -> Q) (l : list A),
  (forall a, In a l -> f a == g a) ->
  qsum (map f l) == qsum (map g l).
Proof.
  intros A f g l; induction l as [| a l IH]; simpl; intros H; [reflexivity |].
  rewrite (H a (or_introl eq_refl)).
  rewrite (IH (fun z Hz => H z (or_intror Hz))); reflexivity.
Qed.

Lemma qsum_le_in : forall (A : Type) (f g : A -> Q) (l : list A),
  (forall a, In a l -> f a <= g a) ->
  qsum (map f l) <= qsum (map g l).
Proof.
  intros A f g l; induction l as [| a l IH]; simpl; intros H; [lra |].
  assert (Ha := H a (or_introl eq_refl)).
  assert (Hl := IH (fun z Hz => H z (or_intror Hz))).
  lra.
Qed.

Lemma qsum_le_lt_in : forall (A : Type) (f g : A -> Q) (l : list A) (a : A),
  (forall x, In x l -> f x <= g x) ->
  In a l -> f a < g a ->
  qsum (map f l) < qsum (map g l).
Proof.
  intros A f g l; induction l as [| b l IH]; simpl; intros a H Ha Hlt; [destruct Ha |].
  assert (Hb := H b (or_introl eq_refl)).
  destruct Ha as [-> | Ha].
  - assert (Hl : qsum (map f l) <= qsum (map g l))
      by (apply qsum_le_in; intros z Hz; apply H; right; exact Hz).
    lra.
  - assert (Hl : qsum (map f l) < qsum (map g l))
      by (apply (IH a (fun z Hz => H z (or_intror Hz)) Ha Hlt)).
    lra.
Qed.

Lemma qsum_plus : forall (A : Type) (f g : A -> Q) (l : list A),
  qsum (map (fun a => f a + g a) l) == qsum (map f l) + qsum (map g l).
Proof.
  intros A f g l; induction l as [| a l IH]; simpl; [lra |].
  rewrite IH; ring.
Qed.

Lemma qsum_scale : forall (A : Type) (c : Q) (f : A -> Q) (l : list A),
  qsum (map (fun a => c * f a) l) == c * qsum (map f l).
Proof.
  intros A c f l; induction l as [| a l IH]; simpl; [ring |].
  rewrite IH; ring.
Qed.

Lemma qsum_div : forall (A : Type) (c : Q) (f : A -> Q) (l : list A),
  qsum (map (fun a => f a / c) l) == qsum (map f l) / c.
Proof.
  intros A c f l.
  assert (H : qsum (map (fun a => f a / c) l) ==
              qsum (map (fun a => / c * f a) l)).
  { apply qsum_map_ext_in; intros a _; unfold Qdiv; ring. }
  rewrite H, (qsum_scale A (/ c) f l); unfold Qdiv; ring.
Qed.

Lemma qsum_zero_of : forall (A : Type) (f : A -> Q) (l : list A),
  (forall a, In a l -> f a == 0) ->
  qsum (map f l) == 0.
Proof.
  intros A f l; induction l as [| a l IH]; simpl; intros H; [reflexivity |].
  rewrite (H a (or_introl eq_refl)).
  rewrite (IH (fun z Hz => H z (or_intror Hz))); ring.
Qed.

Lemma qsum_app : forall l1 l2, qsum (l1 ++ l2) == qsum l1 + qsum l2.
Proof.
  induction l1 as [| a l1 IH]; simpl; intros l2; [lra |].
  rewrite IH; ring.
Qed.

Lemma qsum_perm : forall l l', Permutation l l' -> qsum l == qsum l'.
Proof.
  intros l l' H; induction H; simpl.
  - reflexivity.
  - rewrite IHPermutation; reflexivity.
  - ring.
  - rewrite IHPermutation1; exact IHPermutation2.
Qed.

Lemma qsum_indicator : forall (A : Type) (b : A -> bool) (p : Q) (l : list A),
  qsum (map (fun a => if b a then p else 0) l) ==
  p * inject_Z (Z.of_nat (length (filter b l))).
Proof.
  intros A b p l; induction l as [| a l IH]; simpl.
  - rewrite Qmult_0_r; reflexivity.
  - destruct (b a).
    + rewrite IH.
      change (length (a :: filter b l)) with (S (length (filter b l))).
      rewrite Nat2Z.inj_succ, <- Z.add_1_l, inject_Z_plus; ring.
    + rewrite IH; ring.
Qed.

(* ---- qpow (T2) ---- *)

Lemma qpow_nonneg : forall q n, 0 <= q -> 0 <= qpow q n.
Proof.
  intros q n H; induction n as [| m IH]; simpl; [lra |].
  apply Qmult_le_0_compat; assumption.
Qed.

Lemma qpow_pos : forall q n, 0 < q -> 0 < qpow q n.
Proof.
  intros q n H; induction n as [| m IH]; simpl; [lra |].
  apply Qmult_lt_0_compat; assumption.
Qed.

Lemma qpow_zero : forall n, (0 < n)%nat -> qpow 0 n == 0.
Proof.
  intros [| m] H; [lia | simpl; ring].
Qed.

Lemma qpow_one : forall n, qpow 1 n == 1.
Proof.
  induction n as [| m IH]; simpl; [reflexivity | rewrite IH; ring].
Qed.

Lemma qpow_mono : forall a b n, 0 <= a -> a <= b -> qpow a n <= qpow b n.
Proof.
  intros a b n Ha Hab; induction n as [| m IH]; simpl; [lra |].
  apply Qmult_le_compat_nonneg.
  - split; [exact Ha | exact Hab].
  - split; [apply qpow_nonneg; exact Ha | exact IH].
Qed.

Lemma qpow_strict : forall a b n,
  0 <= a -> a < b -> (0 < n)%nat -> qpow a n < qpow b n.
Proof.
  intros a b n Ha Hab Hn; induction n as [| m IH]; [lia |].
  destruct m as [| m'].
  - simpl; rewrite !Qmult_1_r; exact Hab.
  - assert (Hm : qpow a (S m') < qpow b (S m')) by (apply IH; lia).
    simpl in *.
    assert (Hb : 0 < b) by lra.
    assert (Hpb : 0 < b * qpow b m') by (apply Qmult_lt_0_compat; [lra | apply qpow_pos; lra]).
    assert (Hle : a * (a * qpow a m') <= a * (b * qpow b m')).
    { apply Qmult_le_compat_nonneg.
      - split; [exact Ha | apply Qle_refl].
      - split; [| lra].
        apply Qmult_le_0_compat; [exact Ha | apply qpow_nonneg; exact Ha]. }
    assert (Hlt : a * (b * qpow b m') < b * (b * qpow b m')).
    { apply Qmult_lt_compat_r; [exact Hpb | exact Hab]. }
    lra.
Qed.

Instance qpow_Proper : Proper (Qeq ==> eq ==> Qeq) qpow.
Proof.
  intros a b Hab n m <-; induction n as [| k IH]; simpl; [reflexivity |].
  rewrite IH, Hab; reflexivity.
Qed.

(* ---- normalize (T2 continued) ---- *)

Lemma Qdiv_pos : forall x y, 0 < x -> 0 < y -> 0 < x / y.
Proof.
  intros x y Hx Hy; unfold Qdiv.
  apply Qmult_lt_0_compat; [exact Hx | apply Qinv_lt_0_compat; exact Hy].
Qed.

Lemma Qdiv_nonneg : forall x y, 0 <= x -> 0 <= y -> 0 <= x / y.
Proof.
  intros x y Hx Hy; unfold Qdiv.
  apply Qmult_le_0_compat; [exact Hx | apply Qinv_le_0_compat; exact Hy].
Qed.

Lemma normalize_nonneg : forall (A : Type) (f : A -> Q) (l : list A) (a : A),
  0 <= f a -> (forall x, In x l -> 0 <= f x) ->
  0 <= normalize f l a.
Proof.
  intros A f l a Ha Hl; rewrite normalize_spec.
  apply Qdiv_nonneg; [exact Ha |].
  apply qsum_nonneg; intros x Hx.
  apply in_map_iff in Hx; destruct Hx as [b [<- Hb]]; exact (Hl b Hb).
Qed.

Lemma normalize_sum : forall (A : Type) (f : A -> Q) (l : list A),
  0 < qsum (map f l) ->
  qsum (map (normalize f l) l) == 1.
Proof.
  intros A f l Hpos.
  rewrite (qsum_map_ext_in A (normalize f l)
             (fun a => f a / qsum (map f l)) l
             (fun a _ => normalize_spec A f l a)).
  rewrite (qsum_div A (qsum (map f l)) f l).
  field; apply ne_of_lt; exact Hpos.
Qed.

Lemma Qinv_zero : / 0 == 0.
Proof. reflexivity. Qed.

Lemma normalize_zero : forall (A : Type) (f : A -> Q) (l : list A) (a : A),
  qsum (map f l) == 0 -> normalize f l a == 0.
Proof.
  intros A f l a Hs; rewrite normalize_spec, Hs.
  unfold Qdiv; rewrite Qinv_zero; ring.
Qed.

Lemma normalize_ext_in : forall (A : Type) (f g : A -> Q) (l : list A) (a : A),
  (forall x, In x l -> f x == g x) -> In a l ->
  normalize f l a == normalize g l a.
Proof.
  intros A f g l a Hfg Ha.
  rewrite !normalize_spec, (Hfg a Ha), (qsum_map_ext_in A f g l Hfg).
  reflexivity.
Qed.

Lemma normalize_perm : forall (A : Type) (f : A -> Q) (l l' : list A) (a : A),
  Permutation l l' -> normalize f l a == normalize f l' a.
Proof.
  intros A f l l' a Hp; rewrite !normalize_spec.
  rewrite (qsum_perm (map f l) (map f l') (Permutation_map f Hp)).
  reflexivity.
Qed.

(* Scale invariance: normalize is a ratio, so a common positive factor
   cancels (used by the semantic-equivalence induction). *)
Lemma normalize_scale : forall (A : Type) (k : Q) (f g : A -> Q) (l : list A) (a : A),
  ~ k == 0 ->
  (forall x, In x l -> f x == k * g x) -> In a l ->
  normalize f l a == normalize g l a.
Proof.
  intros A k f g l a Hk Hfg Ha.
  rewrite !normalize_spec, (Hfg a Ha).
  rewrite (qsum_map_ext_in A f (fun x => k * g x) l Hfg).
  rewrite (qsum_scale A k g l).
  destruct (Qeq_dec (qsum (map g l)) 0) as [Hz | Hnz].
  - rewrite Hz; unfold Qdiv; rewrite Qmult_0_r, Qinv_zero; ring.
  - field; split; assumption.
Qed.

End QSum.
Import QSum.

(* ========================================================================== *)
(*  Part 2 — Dist: list-indexed distributions                                 *)
(* ========================================================================== *)

Module Dist.

(* D4.  LG17 eq. (3a-b) on a finite list (ARTIFACT-iv: list-indexed). *)
Definition IsDist {A : Type} (f : A -> Q) (l : list A) : Prop :=
  (forall a, In a l -> 0 <= f a) /\ qsum (map f l) == 1.

End Dist.
Import Dist.

(* ========================================================================== *)
(*  Part 3 — The RSA tower                                                    *)
(* ========================================================================== *)

Section RSA.

(* D6-D15.  Abstract finite W, U with enumerations; Boolean lexicon;
   positive prior; positive cost WEIGHTS (the e^{-alpha c} surrogates,
   header); nat rationality alpha.  Argument convention: listeners are
   U -> W -> Q, speakers W -> U -> Q — the conditioning argument first,
   so (L u) and (S w) ARE the distributions. *)
Variables (W U : Type).
Variables (ws : list W) (us : list U).
Variable meaning : U -> W -> bool.
Variable prior : W -> Q.
Variable costw : U -> Q.
Variable alpha : nat.

Hypothesis prior_pos : forall w, In w ws -> 0 < prior w.
Hypothesis prior_sum1 : qsum (map prior ws) == 1.
Hypothesis costw_pos : forall u, In u us -> 0 < costw u.

(* Definedness, decidably (B16 restrictions (i)-(ii) at o = w). *)
Definition consistent (u : U) : bool := existsb (meaning u) ws.
Definition expressible (w : W) : bool := existsb (fun u => meaning u w) us.

Lemma consistent_iff : forall u,
  consistent u = true <-> exists w, In w ws /\ meaning u w = true.
Proof. intros u; unfold consistent; apply existsb_exists. Qed.

Lemma expressible_iff : forall w,
  expressible w = true <-> exists u, In u us /\ meaning u w = true.
Proof. intros w; unfold expressible; apply existsb_exists. Qed.

Lemma existsb_false_forall : forall (A : Type) (f : A -> bool) (l : list A),
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  intros A f l He x Hx; destruct (f x) eqn:E; [| reflexivity].
  assert (Ht : existsb f l = true) by (apply existsb_exists; exists x; auto).
  rewrite Ht in He; discriminate He.
Qed.

(* The tower (GF16 (1)-(4); B16 (8)-(11); LG17 (9)-(14); FG12 (S1)-(S4);
   GL15 (5)).  ARTIFACT-ii(a): the sources' indicator is bool + if. *)
Definition L0_raw (u : U) (w : W) : Q := if meaning u w then prior w else 0.
Definition L0 (u : U) : W -> Q := normalize (L0_raw u) ws.

Definition S_raw (L : U -> W -> Q) (w : W) (u : U) : Q :=
  Qred (qpow (L u w) alpha) * costw u.
Definition S_of (L : U -> W -> Q) (w : W) : U -> Q := normalize (S_raw L w) us.

Definition L_raw (S : W -> U -> Q) (u : U) (w : W) : Q := S w u * prior w.
Definition L_of (S : W -> U -> Q) (u : U) : W -> Q := normalize (L_raw S u) ws.

Fixpoint Ln (n : nat) : U -> W -> Q :=
  match n with O => L0 | S m => L_of (S_of (Ln m)) end.
Definition Sn (n : nat) : W -> U -> Q := S_of (Ln (Nat.pred n)).
Definition S1 : W -> U -> Q := S_of L0.
Definition L1 : U -> W -> Q := Ln 1.

(* LG17 P(A) (eq. 3); marginal likelihood (FG12 (1), LG17 (14)). *)
Definition Pset (A : W -> bool) : Q :=
  qsum (map (fun w => if A w then prior w else 0) ws).
Definition PS (u : U) : Q := qsum (map (fun w => S1 w u * prior w) ws).

(* Cardinality and specificity (FG12 |w|; B16 p. 20:13). *)
Definition card (u : U) : nat := length (filter (meaning u) ws).
Definition inv_card (u : U) : Q := 1 / inject_Z (Z.of_nat (card u)).
Definition subset_meaning (u1 u2 : U) : Prop :=
  forall w, In w ws -> meaning u1 w = true -> meaning u2 w = true.
Definition strict_subset_meaning (u1 u2 : U) : Prop :=
  subset_meaning u1 u2 /\
  exists w, In w ws /\ meaning u2 w = true /\ meaning u1 w = false.
Definition uniform_prior : Prop :=
  forall w w', In w ws -> In w' ws -> prior w == prior w'.
Definition flat_cost : Prop :=
  forall u u', In u us -> In u' us -> costw u == costw u'.
Definition sem_equiv (u u' : U) : Prop :=
  forall w, In w ws -> meaning u w = meaning u' w.

(* A numerator that vanishes kills the ratio (total division). *)
Lemma normalize_num_zero : forall (A : Type) (f : A -> Q) (l : list A) (a : A),
  f a == 0 -> normalize f l a == 0.
Proof.
  intros A f l a Ha; rewrite normalize_spec, Ha; unfold Qdiv; ring.
Qed.

(* ========================================================================== *)
(*  Part 4 — The literal listener (T3-T6): GF16 (4), B16 (8), LG17 (9)        *)
(* ========================================================================== *)

Lemma L0_raw_nonneg : forall u w, In w ws -> 0 <= L0_raw u w.
Proof.
  intros u w Hw; unfold L0_raw; destruct (meaning u w).
  - apply Qlt_le_weak, prior_pos, Hw.
  - lra.
Qed.

Lemma L0_norm_pos : forall u,
  consistent u = true -> 0 < qsum (map (L0_raw u) ws).
Proof.
  intros u Hc.
  destruct (proj1 (consistent_iff u) Hc) as [w0 [Hw0 Hm0]].
  apply qsum_pos_of_mem with (y := L0_raw u w0).
  - intros x Hx.
    destruct (proj1 (in_map_iff _ _ _) Hx) as [w [<- Hw]].
    apply L0_raw_nonneg; exact Hw.
  - apply in_map; exact Hw0.
  - unfold L0_raw; rewrite Hm0; apply prior_pos; exact Hw0.
Qed.

(* T3.  The literal listener is a distribution exactly when the
   utterance is consistent (B16 restriction (i)). *)
Theorem L0_dist_iff : forall u,
  IsDist (L0 u) ws <-> consistent u = true.
Proof.
  intros u; split.
  - intros [Hnn Hsum].
    destruct (consistent u) eqn:E; [reflexivity | exfalso].
    assert (Hall : forall w, In w ws -> L0_raw u w == 0).
    { intros w Hw; unfold L0_raw.
      destruct (meaning u w) eqn:Em; [| reflexivity].
      assert (Hc : consistent u = true)
        by (apply consistent_iff; exists w; auto).
      rewrite Hc in E; discriminate E. }
    assert (Hz : qsum (map (L0_raw u) ws) == 0)
      by (apply qsum_zero_of; exact Hall).
    assert (H0 : qsum (map (L0 u) ws) == 0).
    { apply qsum_zero_of; intros w _; apply normalize_zero; exact Hz. }
    lra.
  - intros Hc.
    assert (Hpos := L0_norm_pos u Hc).
    split.
    + intros w Hw; apply normalize_nonneg;
        [apply L0_raw_nonneg; exact Hw | intros x Hx; apply L0_raw_nonneg; exact Hx].
    + apply normalize_sum; exact Hpos.
Qed.

(* T4.  The exact failure mode, and the support. *)
Theorem L0_undefined : forall u,
  consistent u = false -> forall w, L0 u w == 0.
Proof.
  intros u Hc w.
  apply normalize_zero, qsum_zero_of.
  intros w' Hw'; unfold L0_raw.
  rewrite (existsb_false_forall _ _ _ Hc w' Hw'); reflexivity.
Qed.

Theorem L0_false : forall u w, meaning u w = false -> L0 u w == 0.
Proof.
  intros u w Hm; apply normalize_num_zero.
  unfold L0_raw; rewrite Hm; reflexivity.
Qed.

Theorem L0_support : forall u w,
  In w ws -> consistent u = true ->
  (0 < L0 u w <-> meaning u w = true).
Proof.
  intros u w Hw Hc; split.
  - intros Hpos; destruct (meaning u w) eqn:Em; [reflexivity |].
    assert (H0 := L0_false u w Em); lra.
  - intros Hm; unfold L0; rewrite normalize_spec.
    apply Qdiv_pos; [| exact (L0_norm_pos u Hc)].
    unfold L0_raw; rewrite Hm; apply prior_pos; exact Hw.
Qed.

(* T5.  L0 IS conditioning on the literal content (LG17 (4), (9);
   Bergen p. 20:15 "entirely according to the prior"). *)
Theorem L0_is_conditioning : forall u w,
  L0 u w == (if meaning u w then prior w else 0) / Pset (meaning u).
Proof. intros u w; exact (normalize_spec _ _ _ _). Qed.

Lemma Pset_pos_of_witness : forall (A : W -> bool) w,
  In w ws -> A w = true -> 0 < Pset A.
Proof.
  intros A w Hw HA; unfold Pset.
  apply qsum_pos_of_mem with (y := if A w then prior w else 0).
  - intros x Hx.
    destruct (proj1 (in_map_iff _ _ _) Hx) as [w' [<- Hw']].
    destruct (A w'); [apply Qlt_le_weak, prior_pos, Hw' | lra].
  - exact (in_map (fun w0 => if A w0 then prior w0 else 0) ws w Hw).
  - rewrite HA; apply prior_pos; exact Hw.
Qed.

Theorem L0_prior_only : forall u w,
  In w ws -> meaning u w = true ->
  L0 u w * Pset (meaning u) == prior w.
Proof.
  intros u w Hw Hm.
  assert (Hps := Pset_pos_of_witness (meaning u) w Hw Hm).
  rewrite (L0_is_conditioning u w), Hm.
  rewrite Qmult_comm; apply Qmult_div_r, ne_of_lt, Hps.
Qed.

Theorem Pset_true : Pset (fun _ => true) == 1.
Proof.
  unfold Pset.
  rewrite (qsum_map_ext_in _ _ prior ws (fun w _ => Qeq_refl (prior w))).
  exact prior_sum1.
Qed.

Theorem Pset_additive : forall (A B : W -> bool),
  (forall w, In w ws -> A w = true -> B w = false) ->
  Pset (fun w => A w || B w) == Pset A + Pset B.
Proof.
  intros A B Hdisj; unfold Pset.
  rewrite <- qsum_plus.
  apply qsum_map_ext_in; intros w Hw.
  destruct (A w) eqn:Ea; destruct (B w) eqn:Eb; simpl.
  - rewrite (Hdisj w Hw Ea) in Eb; discriminate Eb.
  - ring.
  - ring.
  - ring.
Qed.

Theorem L0_tautology : forall u,
  (forall w, In w ws -> meaning u w = true) ->
  forall w, In w ws -> L0 u w == prior w.
Proof.
  intros u Hall w Hw.
  assert (Hps : Pset (meaning u) == 1).
  { unfold Pset.
    rewrite (qsum_map_ext_in _ _ prior ws); [exact prior_sum1 |].
    intros w' Hw'; rewrite (Hall w' Hw'); reflexivity. }
  rewrite (L0_is_conditioning u w), (Hall w Hw), Hps.
  field.
Qed.

(* T6.  Under a uniform prior the literal listener is the inverse
   cardinality — FG12 (S3).  (NoDup is the flagged stronger-than-source
   hypothesis, ARTIFACT-v: it makes card count WORLDS, not list
   entries.) *)
Theorem L0_uniform_card : forall u w,
  uniform_prior -> NoDup ws -> In w ws -> meaning u w = true ->
  L0 u w == inv_card u.
Proof.
  intros u w Hu Hnd Hw Hm.
  assert (Hps : Pset (meaning u) ==
                prior w * inject_Z (Z.of_nat (card u))).
  { unfold Pset.
    rewrite (qsum_map_ext_in _ _
               (fun w' => if meaning u w' then prior w else 0) ws).
    - apply qsum_indicator.
    - intros w' Hw'; destruct (meaning u w') eqn:E;
        [apply Hu; assumption | reflexivity]. }
  assert (Hcard : (0 < card u)%nat).
  { unfold card.
    assert (Hin : In w (filter (meaning u) ws))
      by (apply filter_In; auto).
    destruct (filter (meaning u) ws); [destruct Hin | simpl; lia]. }
  assert (Hn : 0 < inject_Z (Z.of_nat (card u))).
  { unfold Qlt, inject_Z; simpl; lia. }
  assert (Hnz1 : ~ inject_Z (Z.of_nat (card u)) == 0)
    by (apply ne_of_lt; exact Hn).
  assert (Hnz2 : ~ prior w == 0)
    by (apply ne_of_lt, prior_pos, Hw).
  rewrite (L0_is_conditioning u w), Hm, Hps.
  unfold inv_card.
  field; split; assumption.
Qed.

(* ========================================================================== *)
(*  Part 5 — The speaker (T7-T9): GF16 (2)-(3)+Box 1, B16 (9)-(10),           *)
(*  LG17 (10)-(12), GL15 (5), FG12 (S1)-(S2)                                  *)
(* ========================================================================== *)

Lemma L0_nonneg : forall u w, In w ws -> 0 <= L0 u w.
Proof.
  intros u w Hw; apply normalize_nonneg;
    [apply L0_raw_nonneg; exact Hw | intros x Hx; apply L0_raw_nonneg; exact Hx].
Qed.

Lemma S_raw_nonneg_L0 : forall w u,
  In w ws -> In u us -> 0 <= S_raw L0 w u.
Proof.
  intros w u Hw Hu; unfold S_raw.
  rewrite Qred_correct.
  apply Qmult_le_0_compat.
  - apply qpow_nonneg, L0_nonneg, Hw.
  - apply Qlt_le_weak, costw_pos, Hu.
Qed.

Lemma S1_raw_true : forall w u,
  In w ws -> In u us -> meaning u w = true -> 0 < S_raw L0 w u.
Proof.
  intros w u Hw Hu Hm.
  assert (Hc : consistent u = true)
    by (apply consistent_iff; exists w; auto).
  unfold S_raw; rewrite Qred_correct.
  apply Qmult_lt_0_compat.
  - apply qpow_pos, (proj2 (L0_support u w Hw Hc)), Hm.
  - apply costw_pos, Hu.
Qed.

Lemma S1_raw_false : forall w u,
  (0 < alpha)%nat -> meaning u w = false -> S_raw L0 w u == 0.
Proof.
  intros w u Ha Hm; unfold S_raw.
  rewrite Qred_correct, (L0_false u w Hm), (qpow_zero alpha Ha); ring.
Qed.

Lemma S1_norm_pos : forall w,
  In w ws -> expressible w = true -> 0 < qsum (map (S_raw L0 w) us).
Proof.
  intros w Hw He.
  destruct (proj1 (expressible_iff w) He) as [u0 [Hu0 Hm0]].
  apply qsum_pos_of_mem with (y := S_raw L0 w u0).
  - intros x Hx.
    destruct (proj1 (in_map_iff _ _ _) Hx) as [u [<- Hu]].
    apply S_raw_nonneg_L0; assumption.
  - apply in_map; exact Hu0.
  - apply S1_raw_true; assumption.
Qed.

(* T7.  The speaker is a distribution exactly when the world is
   expressible (B16 restriction (ii) at o = w). *)
Theorem S1_dist_iff : forall w,
  (0 < alpha)%nat -> In w ws ->
  (IsDist (S1 w) us <-> expressible w = true).
Proof.
  intros w Ha Hw; split.
  - intros [Hnn Hsum].
    destruct (expressible w) eqn:E; [reflexivity | exfalso].
    assert (Hz : qsum (map (S_raw L0 w) us) == 0).
    { apply qsum_zero_of; intros u Hu.
      apply S1_raw_false; [exact Ha |].
      exact (existsb_false_forall _ _ _ E u Hu). }
    assert (H0 : qsum (map (S1 w) us) == 0).
    { apply qsum_zero_of; intros u _; apply normalize_zero; exact Hz. }
    lra.
  - intros He; split.
    + intros u Hu; apply normalize_nonneg;
        [apply S_raw_nonneg_L0; assumption |
         intros x Hx; apply S_raw_nonneg_L0; assumption].
    + apply normalize_sum, S1_norm_pos; assumption.
Qed.

(* T8.  Failure mode, support, truthfulness. *)
Theorem S1_undefined : forall w,
  (0 < alpha)%nat -> expressible w = false -> forall u, S1 w u == 0.
Proof.
  intros w Ha He u.
  apply normalize_zero, qsum_zero_of.
  intros u' Hu'; apply S1_raw_false; [exact Ha |].
  exact (existsb_false_forall _ _ _ He u' Hu').
Qed.

Theorem speaker_truthful : forall w u,
  (0 < alpha)%nat -> meaning u w = false -> S1 w u == 0.
Proof.
  intros w u Ha Hm; apply normalize_num_zero, S1_raw_false; assumption.
Qed.

Theorem S1_support : forall w u,
  (0 < alpha)%nat -> In w ws -> In u us -> expressible w = true ->
  (0 < S1 w u <-> meaning u w = true).
Proof.
  intros w u Ha Hw Hu He; split.
  - intros Hpos; destruct (meaning u w) eqn:Em; [reflexivity |].
    assert (H0 := speaker_truthful w u Ha Em); lra.
  - intros Hm; unfold S1, S_of; rewrite normalize_spec.
    apply Qdiv_pos; [apply S1_raw_true; assumption |].
    apply S1_norm_pos; assumption.
Qed.

(* T9.  alpha = 0 is total but degenerate: the speaker ignores truth and
   samples from the cost weights alone — the documented reason every
   truth-sensitive theorem carries (0 < alpha)%nat. *)
Theorem S1_alpha0 : forall w u,
  alpha = 0%nat -> In u us ->
  S1 w u == normalize costw us u.
Proof.
  intros w u Ha Hu; unfold S1, S_of.
  apply normalize_ext_in; [| exact Hu].
  intros u' Hu'; unfold S_raw; rewrite Ha.
  rewrite Qred_correct; simpl; ring.
Qed.

(* ========================================================================== *)
(*  Part 6 — The pragmatic listener (T10-T16): GF16 (1), B16 (11),            *)
(*  LG17 (13)-(14), FG12 (1)                                                  *)
(* ========================================================================== *)

Lemma S1_nonneg : forall w u, In w ws -> In u us -> 0 <= S1 w u.
Proof.
  intros w u Hw Hu; apply normalize_nonneg;
    [apply S_raw_nonneg_L0; assumption |
     intros x Hx; apply S_raw_nonneg_L0; assumption].
Qed.

Lemma L1_raw_nonneg : forall u w,
  In u us -> In w ws -> 0 <= L_raw S1 u w.
Proof.
  intros u w Hu Hw; unfold L_raw.
  apply Qmult_le_0_compat;
    [apply S1_nonneg; assumption | apply Qlt_le_weak, prior_pos, Hw].
Qed.

Lemma qsum_pos_exists : forall (A : Type) (f : A -> Q) (l : list A),
  (forall a, In a l -> 0 <= f a) ->
  0 < qsum (map f l) ->
  exists a, In a l /\ 0 < f a.
Proof.
  intros A f l; induction l as [| a l IH]; simpl; intros Hnn Hpos; [lra |].
  destruct (Qlt_le_dec 0 (f a)) as [Hlt | Hle].
  - exists a; auto.
  - assert (Hla : 0 <= f a) by (apply Hnn; auto).
    assert (Hrest : 0 < qsum (map f l)) by lra.
    destruct (IH (fun x Hx => Hnn x (or_intror Hx)) Hrest) as [b [Hb Hfb]].
    exists b; auto.
Qed.

(* T14.  The unconditional product rule (Bayes without division): the
   degenerate case is 0 == 0 because a vanishing normalizer kills every
   raw term on ws. *)
Theorem L1_product : forall u w,
  In u us -> In w ws ->
  L1 u w * PS u == S1 w u * prior w.
Proof.
  intros u w Hu Hw.
  assert (Hspec : L1 u w == (S1 w u * prior w) / PS u)
    by exact (normalize_spec _ _ _ _).
  destruct (Qeq_dec (PS u) 0) as [Hz | Hnz].
  - assert (Hnn : forall x, In x (map (fun w' => S1 w' u * prior w') ws) -> 0 <= x).
    { intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [w' [<- Hw']].
      exact (L1_raw_nonneg u w' Hu Hw'). }
    assert (Hraw : S1 w u * prior w == 0).
    { apply (proj1 (qsum_zero_iff _ Hnn) Hz).
      exact (in_map (fun w' => S1 w' u * prior w') ws w Hw). }
    rewrite Hz, Hraw; ring.
  - rewrite Hspec; field; exact Hnz.
Qed.

(* T13.  Bayes' rule (FG12 (1), LG17 (14)). *)
Theorem L1_bayes : forall u w,
  L1 u w == S1 w u * prior w / PS u.
Proof. intros u w; exact (normalize_spec _ _ _ _). Qed.

(* T10/PS.  Positivity of the marginal likelihood, with the exact
   witness condition. *)
Theorem PS_pos_iff : forall u,
  (0 < alpha)%nat -> In u us ->
  (0 < PS u <->
   exists w, In w ws /\ meaning u w = true /\ expressible w = true).
Proof.
  intros u Ha Hu; split.
  - intros Hpos.
    destruct (qsum_pos_exists _ (fun w => S1 w u * prior w) ws) as [w0 [Hw0 Hf]];
      [intros w Hw; exact (L1_raw_nonneg u w Hu Hw) | exact Hpos |].
    assert (Hprior := prior_pos w0 Hw0).
    assert (Hs1 : 0 < S1 w0 u) by nra.
    destruct (expressible w0) eqn:Ee.
    + exists w0; split; [exact Hw0 | split; [| exact Ee]].
      exact (proj1 (S1_support w0 u Ha Hw0 Hu Ee) Hs1).
    + assert (H0 := S1_undefined w0 Ha Ee u); lra.
  - intros [w0 [Hw0 [Hm He]]].
    apply qsum_pos_of_mem with (y := S1 w0 u * prior w0).
    + intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [w' [<- Hw']].
      exact (L1_raw_nonneg u w' Hu Hw').
    + exact (in_map (fun w' => S1 w' u * prior w') ws w0 Hw0).
    + apply Qmult_lt_0_compat.
      * exact (proj2 (S1_support w0 u Ha Hw0 Hu He) Hm).
      * exact (prior_pos w0 Hw0).
Qed.

(* T10.  The pragmatic listener is a distribution exactly when some
   listed world verifies u and is expressible. *)
Theorem L1_dist_iff : forall u,
  (0 < alpha)%nat -> In u us ->
  (IsDist (L1 u) ws <->
   exists w, In w ws /\ meaning u w = true /\ expressible w = true).
Proof.
  intros u Ha Hu; split.
  - intros [Hnn Hsum].
    destruct (existsb (fun w => meaning u w && expressible w) ws) eqn:E.
    + destruct (proj1 (existsb_exists _ _) E) as [w0 [Hw0 Hb]].
      destruct (proj1 (andb_true_iff _ _) Hb) as [Hm He].
      exists w0; auto.
    + exfalso.
      assert (Hall : forall w, In w ws -> L_raw S1 u w == 0).
      { intros w Hw.
        unfold L_raw.
        destruct (expressible w) eqn:Ee.
        - destruct (meaning u w) eqn:Em.
          + exfalso.
            assert (Ht : existsb
                       (fun w' => meaning u w' && expressible w') ws = true).
            { apply existsb_exists; exists w; split; [exact Hw |].
              rewrite Em, Ee; reflexivity. }
            rewrite Ht in E; discriminate E.
          + rewrite (speaker_truthful w u Ha Em); ring.
        - rewrite (S1_undefined w Ha Ee u); ring. }
      assert (H0 : qsum (map (L1 u) ws) == 0).
      { apply qsum_zero_of; intros w _.
        apply normalize_zero, qsum_zero_of; exact Hall. }
      lra.
  - intros Hex.
    assert (Hps : 0 < PS u) by (apply (PS_pos_iff u Ha Hu); exact Hex).
    split.
    + intros w Hw; apply normalize_nonneg;
        [exact (L1_raw_nonneg u w Hu Hw) |
         intros x Hx; exact (L1_raw_nonneg u x Hu Hx)].
    + apply normalize_sum; exact Hps.
Qed.

(* T10 corollary: among the alternatives, L1's definedness condition is
   exactly L0's (u itself makes its worlds expressible). *)
Corollary L1_dist_iff_alt : forall u,
  (0 < alpha)%nat -> In u us ->
  (IsDist (L1 u) ws <-> consistent u = true).
Proof.
  intros u Ha Hu; rewrite (L1_dist_iff u Ha Hu); split.
  - intros [w [Hw [Hm _]]]; apply consistent_iff; exists w; auto.
  - intros Hc.
    destruct (proj1 (consistent_iff u) Hc) as [w [Hw Hm]].
    exists w; split; [exact Hw | split; [exact Hm |]].
    apply expressible_iff; exists u; auto.
Qed.

(* T11-T12.  Failure mode, support, falsity. *)
Theorem L1_undefined : forall u,
  (0 < alpha)%nat -> consistent u = false -> forall w, L1 u w == 0.
Proof.
  intros u Ha Hc w.
  apply normalize_zero, qsum_zero_of.
  intros w' Hw'; unfold L_raw.
  rewrite (speaker_truthful w' u Ha
             (existsb_false_forall _ _ _ Hc w' Hw')); ring.
Qed.

Theorem listener_false : forall u w,
  (0 < alpha)%nat -> meaning u w = false -> L1 u w == 0.
Proof.
  intros u w Ha Hm; apply normalize_num_zero.
  unfold L_raw; rewrite (speaker_truthful w u Ha Hm); ring.
Qed.

Theorem L1_support : forall u w,
  (0 < alpha)%nat -> In u us -> consistent u = true -> In w ws ->
  (0 < L1 u w <-> meaning u w = true).
Proof.
  intros u w Ha Hu Hc Hw; split.
  - intros Hpos; destruct (meaning u w) eqn:Em; [reflexivity |].
    assert (H0 := listener_false u w Ha Em); lra.
  - intros Hm.
    assert (He : expressible w = true)
      by (apply expressible_iff; exists u; auto).
    assert (Hps : 0 < PS u).
    { apply (PS_pos_iff u Ha Hu); exists w; auto. }
    rewrite (L1_bayes u w).
    apply Qdiv_pos; [| exact Hps].
    apply Qmult_lt_0_compat.
    + exact (proj2 (S1_support w u Ha Hw Hu He) Hm).
    + exact (prior_pos w Hw).
Qed.

(* T15.  Proportionality determines the distribution — the implicit
   content of every "proportional-to" in the sources. *)
Theorem L1_propto : forall u,
  In u us -> 0 < PS u ->
  exists Z, 0 < Z /\
    forall w, In w ws -> L1 u w * Z == S1 w u * prior w.
Proof.
  intros u Hu Hps; exists (PS u); split; [exact Hps |].
  intros w Hw; exact (L1_product u w Hu Hw).
Qed.

Theorem L1_unique : forall u (q : W -> Q),
  In u us -> IsDist q ws ->
  (exists Z, 0 < Z /\ forall w, In w ws -> q w * Z == S1 w u * prior w) ->
  forall w, In w ws -> q w == L1 u w.
Proof.
  intros u q Hu [Hqnn Hqsum] [Z [HZ Heq]] w Hw.
  assert (HZps : Z == PS u).
  { assert (Hsz : qsum (map (fun w' => q w' * Z) ws) == PS u).
    { unfold PS; apply qsum_map_ext_in; intros w' Hw'; exact (Heq w' Hw'). }
    assert (Hscale : qsum (map (fun w' => q w' * Z) ws) == Z * qsum (map q ws)).
    { rewrite <- (qsum_scale _ Z q ws).
      apply qsum_map_ext_in; intros w' _; ring. }
    rewrite Hscale, Hqsum in Hsz; lra. }
  assert (Hq : q w == (S1 w u * prior w) / Z).
  { rewrite <- (Heq w Hw); field; apply ne_of_lt; exact HZ. }
  rewrite Hq, (L1_bayes u w), HZps; reflexivity.
Qed.

(* T16.  Posterior odds = likelihood ratio x prior odds, division-free. *)
Theorem L1_odds : forall u w w',
  In u us -> In w ws -> In w' ws ->
  L1 u w * (S1 w' u * prior w') == L1 u w' * (S1 w u * prior w).
Proof.
  intros u w w' Hu Hw Hw'.
  rewrite <- (L1_product u w' Hu Hw'), <- (L1_product u w Hu Hw); ring.
Qed.

(* ========================================================================== *)
(*  Part 7 — Ordering / informativeness (T17-T21): B16 §3, FG12 size          *)
(* ========================================================================== *)

Lemma qpow_1 : forall q, qpow q 1 == q.
Proof. intros q; simpl; ring. Qed.

Lemma Qinv_le_anti : forall a b, 0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab.
  destruct (proj1 (Qle_lteq a b) Hab) as [Hlt | Heq].
  - assert (Hb : 0 < b) by lra.
    apply Qlt_le_weak, (proj1 (Qinv_lt_contravar a b Ha Hb)), Hlt.
  - rewrite Heq; apply Qle_refl.
Qed.

(* T17.  A contextually more specific utterance gets a weakly higher
   literal posterior at its worlds — for ANY positive prior (B16
   p. 20:13; FG12 "smaller section of the context"). *)
Theorem L0_more_specific : forall u1 u2 w,
  subset_meaning u1 u2 -> In w ws -> meaning u1 w = true ->
  L0 u2 w <= L0 u1 w.
Proof.
  intros u1 u2 w Hsub Hw Hm1.
  assert (Hm2 : meaning u2 w = true) by (apply Hsub; assumption).
  assert (Hp1 : 0 < Pset (meaning u1))
    by (apply (Pset_pos_of_witness _ w); assumption).
  assert (Hle : Pset (meaning u1) <= Pset (meaning u2)).
  { unfold Pset; apply qsum_le_in; intros w' Hw'.
    destruct (meaning u1 w') eqn:E1.
    - rewrite (Hsub w' Hw' E1); apply Qle_refl.
    - destruct (meaning u2 w');
        [apply Qlt_le_weak, prior_pos, Hw' | apply Qle_refl]. }
  rewrite (L0_is_conditioning u1 w), (L0_is_conditioning u2 w), Hm1, Hm2.
  unfold Qdiv.
  apply (proj2 (Qmult_le_l _ _ (prior w) (prior_pos w Hw))).
  apply Qinv_le_anti; [exact Hp1 | exact Hle].
Qed.

Theorem L0_strictly_more_specific : forall u1 u2 w,
  strict_subset_meaning u1 u2 -> In w ws -> meaning u1 w = true ->
  L0 u2 w < L0 u1 w.
Proof.
  intros u1 u2 w [Hsub [w2 [Hw2 [Hm2t Hm1f]]]] Hw Hm1.
  assert (Hm2 : meaning u2 w = true) by (apply Hsub; assumption).
  assert (Hp1 : 0 < Pset (meaning u1))
    by (apply (Pset_pos_of_witness _ w); assumption).
  assert (Hlt : Pset (meaning u1) < Pset (meaning u2)).
  { unfold Pset.
    apply (qsum_le_lt_in _ _ _ ws w2).
    - intros w' Hw'; destruct (meaning u1 w') eqn:E1.
      + rewrite (Hsub w' Hw' E1); apply Qle_refl.
      + destruct (meaning u2 w');
          [apply Qlt_le_weak, prior_pos, Hw' | apply Qle_refl].
    - exact Hw2.
    - rewrite Hm1f, Hm2t; apply prior_pos; exact Hw2. }
  assert (Hp2 : 0 < Pset (meaning u2)) by lra.
  rewrite (L0_is_conditioning u1 w), (L0_is_conditioning u2 w), Hm1, Hm2.
  unfold Qdiv.
  apply (proj2 (Qmult_lt_l _ _ (prior w) (prior_pos w Hw))).
  apply (proj1 (Qinv_lt_contravar _ _ Hp1 Hp2)); exact Hlt.
Qed.

(* T18.  The speaker inherits the preference when the specific utterance
   is no more expensive (the general ordering lemma; flat costs are the
   special case). *)
Theorem S1_more_specific : forall u1 u2 w,
  (0 < alpha)%nat ->
  subset_meaning u1 u2 -> costw u2 <= costw u1 ->
  In u1 us -> In u2 us -> In w ws -> meaning u1 w = true ->
  S1 w u2 <= S1 w u1.
Proof.
  intros u1 u2 w Ha Hsub Hcost Hu1 Hu2 Hw Hm1.
  assert (Hraw : S_raw L0 w u2 <= S_raw L0 w u1).
  { unfold S_raw; rewrite !Qred_correct.
    apply Qmult_le_compat_nonneg.
    - split; [apply qpow_nonneg, L0_nonneg, Hw |].
      apply qpow_mono; [apply L0_nonneg, Hw |].
      apply L0_more_specific; assumption.
    - split; [apply Qlt_le_weak, costw_pos, Hu2 | exact Hcost]. }
  assert (Hnorm : 0 < qsum (map (S_raw L0 w) us)).
  { apply qsum_pos_of_mem with (y := S_raw L0 w u1).
    - intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [u' [<- Hu']].
      apply S_raw_nonneg_L0; assumption.
    - apply in_map; exact Hu1.
    - apply S1_raw_true; assumption. }
  unfold S1, S_of; rewrite !normalize_spec; unfold Qdiv.
  apply Qmult_le_compat_nonneg.
  - split; [apply S_raw_nonneg_L0; assumption | exact Hraw].
  - split; [apply Qinv_le_0_compat; lra | apply Qle_refl].
Qed.

Theorem S1_strictly_more_specific : forall u1 u2 w,
  (0 < alpha)%nat ->
  strict_subset_meaning u1 u2 -> costw u2 <= costw u1 ->
  In u1 us -> In u2 us -> In w ws -> meaning u1 w = true ->
  S1 w u2 < S1 w u1.
Proof.
  intros u1 u2 w Ha Hstrict Hcost Hu1 Hu2 Hw Hm1.
  assert (Hsub := proj1 Hstrict).
  assert (Hm2 : meaning u2 w = true) by (apply Hsub; assumption).
  assert (Hc : consistent u2 = true)
    by (apply consistent_iff; exists w; auto).
  assert (Hraw : S_raw L0 w u2 < S_raw L0 w u1).
  { unfold S_raw; rewrite !Qred_correct.
    assert (Hq : qpow (L0 u2 w) alpha < qpow (L0 u1 w) alpha).
    { apply qpow_strict; [apply L0_nonneg, Hw | | exact Ha].
      apply L0_strictly_more_specific; assumption. }
    assert (Hq1 : 0 < qpow (L0 u1 w) alpha).
    { apply qpow_pos.
      apply (proj2 (L0_support u1 w Hw
               (proj2 (consistent_iff u1)
                  (ex_intro _ w (conj Hw Hm1))))); exact Hm1. }
    assert (Hstep1 : qpow (L0 u2 w) alpha * costw u2 <=
                     qpow (L0 u2 w) alpha * costw u1).
    { apply Qmult_le_compat_nonneg.
      - split; [apply qpow_nonneg, L0_nonneg, Hw | apply Qle_refl].
      - split; [apply Qlt_le_weak, costw_pos, Hu2 | exact Hcost]. }
    assert (Hstep2 : qpow (L0 u2 w) alpha * costw u1 <
                     qpow (L0 u1 w) alpha * costw u1).
    { apply Qmult_lt_compat_r; [apply costw_pos, Hu1 | exact Hq]. }
    lra. }
  assert (Hnorm : 0 < qsum (map (S_raw L0 w) us)).
  { apply qsum_pos_of_mem with (y := S_raw L0 w u1).
    - intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [u' [<- Hu']].
      apply S_raw_nonneg_L0; assumption.
    - apply in_map; exact Hu1.
    - apply S1_raw_true; assumption. }
  unfold S1, S_of; rewrite !normalize_spec; unfold Qdiv.
  apply Qmult_lt_compat_r; [apply Qinv_lt_0_compat; exact Hnorm | exact Hraw].
Qed.

(* T19.  The speaker-to-listener lifting lemma — the mechanism of
   LG17 (17)-(20). *)
Theorem L1_order_from_S1 : forall u w w',
  In w ws -> In w' ws -> prior w == prior w' ->
  S1 w' u < S1 w u -> 0 < PS u ->
  L1 u w' < L1 u w.
Proof.
  intros u w w' Hw Hw' Hprior Hs Hps.
  rewrite (L1_bayes u w), (L1_bayes u w'); unfold Qdiv.
  apply Qmult_lt_compat_r; [apply Qinv_lt_0_compat; exact Hps |].
  rewrite Hprior.
  apply Qmult_lt_compat_r; [| exact Hs].
  rewrite <- Hprior; apply prior_pos; exact Hw.
Qed.

(* T20.  The size principle (FG12 (2)/(S4)): with uniform prior, flat
   cost and alpha = 1 the speaker samples inversely to the utterances'
   extension sizes. *)
Theorem size_principle : forall w u,
  uniform_prior -> flat_cost -> alpha = 1%nat -> NoDup ws ->
  In w ws -> In u us ->
  S1 w u ==
  (if meaning u w then inv_card u else 0) /
  qsum (map (fun u' => if meaning u' w then inv_card u' else 0) us).
Proof.
  intros w u Hup Hfc Ha Hnd Hw Hu.
  set (h := fun u' : U => if meaning u' w then inv_card u' else 0).
  assert (Hstep : forall u', In u' us ->
            S_raw L0 w u' == costw u * h u').
  { intros u' Hu'; unfold S_raw; rewrite Qred_correct, Ha, qpow_1.
    unfold h; destruct (meaning u' w) eqn:Em.
    - rewrite (L0_uniform_card u' w Hup Hnd Hw Em).
      rewrite (Hfc u' u Hu' Hu); ring.
    - rewrite (L0_false u' w Em); ring. }
  assert (Hn : S1 w u == normalize h us u).
  { unfold S1, S_of.
    apply (normalize_scale U (costw u) (S_raw L0 w) h us u);
      [apply ne_of_lt, costw_pos, Hu | exact Hstep | exact Hu]. }
  rewrite Hn; apply normalize_spec.
Qed.

(* ========================================================================== *)
(*  Part 8 — Semantic-equivalence invariance (T22-T24): B16 §4.1.1            *)
(* ========================================================================== *)

(* T22.  Bergen Lemma 1. *)
Theorem L0_sem_equiv : forall u u' w,
  sem_equiv u u' -> In w ws -> L0 u w == L0 u' w.
Proof.
  intros u u' w Hse Hw.
  apply (normalize_ext_in W (L0_raw u) (L0_raw u') ws w); [| exact Hw].
  intros w' Hw'; unfold L0_raw; rewrite (Hse w' Hw'); reflexivity.
Qed.

(* The one-step twist: equal listener values give cost-twisted speaker
   values (Bergen Lemma 2 with the cost factor of eq. (22)). *)
Lemma S_of_twist : forall (L : U -> W -> Q) (u u' : U) (w : W),
  L u w == L u' w ->
  S_of L w u * costw u' == S_of L w u' * costw u.
Proof.
  intros L u u' w HL; unfold S_of.
  rewrite !normalize_spec.
  set (S := qsum (map (S_raw L w) us)).
  assert (Hrc : S_raw L w u * costw u' == S_raw L w u' * costw u).
  { unfold S_raw; rewrite !Qred_correct, HL; ring. }
  unfold Qdiv.
  transitivity (S_raw L w u * costw u' * / S); [ring |].
  rewrite Hrc; ring.
Qed.

(* ... which the next listener cancels (the common factor is a cost
   ratio, and normalize is scale-invariant). *)
Lemma L_of_of_twist : forall (S : W -> U -> Q) (u u' : U),
  In u us -> In u' us ->
  (forall w, In w ws -> S w u * costw u' == S w u' * costw u) ->
  forall w, In w ws -> L_of S u w == L_of S u' w.
Proof.
  intros S u u' Hu Hu' Htw w Hw.
  assert (Hc' : ~ costw u' == 0) by (apply ne_of_lt, costw_pos, Hu').
  assert (Hkpos : 0 < costw u * / costw u').
  { apply Qmult_lt_0_compat;
      [apply costw_pos, Hu | apply Qinv_lt_0_compat, costw_pos, Hu']. }
  apply (normalize_scale W (costw u * / costw u')
           (L_raw S u) (L_raw S u') ws w);
    [apply ne_of_lt; exact Hkpos | | exact Hw].
  intros w' Hw'; unfold L_raw.
  assert (H1 : S w' u * costw u' * / costw u' ==
               S w' u' * costw u * / costw u')
    by (rewrite (Htw w' Hw'); reflexivity).
  assert (H2 : S w' u * costw u' * / costw u' == S w' u).
  { rewrite <- Qmult_assoc, Qmult_inv_r; [ring | exact Hc']. }
  rewrite <- H2, H1; ring.
Qed.

(* T23-T24.  Semantic equivalence is invisible at every depth for every
   cost assignment — hence base RSA derives NO M-implicatures
   (Bergen §4.1.1). *)
Theorem Ln_sem_equiv : forall u u',
  sem_equiv u u' -> In u us -> In u' us ->
  forall n w, In w ws -> Ln n u w == Ln n u' w.
Proof.
  intros u u' Hse Hu Hu'; induction n as [| m IH]; intros w Hw.
  - apply (normalize_ext_in W (L0_raw u) (L0_raw u') ws w); [| exact Hw].
    intros w' Hw'; unfold L0_raw; rewrite (Hse w' Hw'); reflexivity.
  - simpl.
    apply (L_of_of_twist (S_of (Ln m)) u u' Hu Hu'); [| exact Hw].
    intros w' Hw'; apply S_of_twist; exact (IH w' Hw').
Qed.

Theorem Sn_sem_equiv : forall u u',
  sem_equiv u u' -> In u us -> In u' us ->
  forall n w, In w ws ->
  Sn (S n) w u * costw u' == Sn (S n) w u' * costw u.
Proof.
  intros u u' Hse Hu Hu' n w Hw.
  apply S_of_twist.
  apply Ln_sem_equiv; assumption.
Qed.

Theorem no_M_implicature : forall u u',
  sem_equiv u u' -> In u us -> In u' us ->
  forall n w, In w ws -> Ln n u w == Ln n u' w.
Proof. exact Ln_sem_equiv. Qed.

(* ========================================================================== *)
(*  Part 9 — Depth n (T26-T27): B16 (8)-(11) "for integers n > 0"             *)
(* ========================================================================== *)

Lemma S_raw_nonneg_gen : forall (L : U -> W -> Q) w u,
  0 <= L u w -> In u us -> 0 <= S_raw L w u.
Proof.
  intros L w u HL Hu; unfold S_raw; rewrite Qred_correct.
  apply Qmult_le_0_compat;
    [apply qpow_nonneg; exact HL | apply Qlt_le_weak, costw_pos, Hu].
Qed.

Lemma S_raw_pos_gen : forall (L : U -> W -> Q) w u,
  0 < L u w -> In u us -> 0 < S_raw L w u.
Proof.
  intros L w u HL Hu; unfold S_raw; rewrite Qred_correct.
  apply Qmult_lt_0_compat;
    [apply qpow_pos; exact HL | apply costw_pos, Hu].
Qed.

Lemma S_raw_zero_gen : forall (L : U -> W -> Q) w u,
  (0 < alpha)%nat -> L u w == 0 -> S_raw L w u == 0.
Proof.
  intros L w u Ha HL; unfold S_raw.
  rewrite Qred_correct, HL, (qpow_zero alpha Ha); ring.
Qed.

Lemma S_of_support_gen : forall (L : U -> W -> Q),
  (0 < alpha)%nat ->
  (forall u w, In u us -> In w ws -> 0 <= L u w) ->
  (forall u w, In u us -> In w ws -> (0 < L u w <-> meaning u w = true)) ->
  forall w u, In w ws -> In u us -> expressible w = true ->
  (0 < S_of L w u <-> meaning u w = true).
Proof.
  intros L Ha Hnn Hsup w u Hw Hu He.
  assert (Hzero : forall u', In u' us -> meaning u' w = false ->
                  S_raw L w u' == 0).
  { intros u' Hu' Hm.
    apply S_raw_zero_gen; [exact Ha |].
    assert (Hn := Hnn u' w Hu' Hw).
    destruct (Qlt_le_dec 0 (L u' w)) as [Hlt | Hle].
    - rewrite (proj1 (Hsup u' w Hu' Hw) Hlt) in Hm; discriminate Hm.
    - lra. }
  assert (Hnorm : 0 < qsum (map (S_raw L w) us)).
  { destruct (proj1 (expressible_iff w) He) as [u0 [Hu0 Hm0]].
    apply qsum_pos_of_mem with (y := S_raw L w u0).
    - intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [u' [<- Hu']].
      apply S_raw_nonneg_gen; [exact (Hnn u' w Hu' Hw) | exact Hu'].
    - apply in_map; exact Hu0.
    - apply S_raw_pos_gen; [| exact Hu0].
      exact (proj2 (Hsup u0 w Hu0 Hw) Hm0). }
  split.
  - intros Hpos; destruct (meaning u w) eqn:Em; [reflexivity |].
    assert (H0 : S_of L w u == 0)
      by (apply normalize_num_zero, Hzero; assumption).
    lra.
  - intros Hm; unfold S_of; rewrite normalize_spec.
    apply Qdiv_pos; [| exact Hnorm].
    apply S_raw_pos_gen; [exact (proj2 (Hsup u w Hu Hw) Hm) | exact Hu].
Qed.

Lemma S_of_nonneg_gen : forall (L : U -> W -> Q),
  (forall u w, In u us -> In w ws -> 0 <= L u w) ->
  forall w u, In w ws -> In u us -> 0 <= S_of L w u.
Proof.
  intros L Hnn w u Hw Hu; apply normalize_nonneg.
  - apply S_raw_nonneg_gen; [exact (Hnn u w Hu Hw) | exact Hu].
  - intros x Hx; apply S_raw_nonneg_gen;
      [exact (Hnn x w Hx Hw) | exact Hx].
Qed.

Lemma L_of_support_gen : forall (S : W -> U -> Q),
  (forall w u, In w ws -> In u us -> 0 <= S w u) ->
  (forall w u, In w ws -> In u us -> (0 < S w u <-> meaning u w = true)) ->
  forall u w, In u us -> In w ws -> consistent u = true ->
  (0 < L_of S u w <-> meaning u w = true).
Proof.
  intros S Hnn Hsup u w Hu Hw Hc.
  assert (Hnorm : 0 < qsum (map (L_raw S u) ws)).
  { destruct (proj1 (consistent_iff u) Hc) as [w0 [Hw0 Hm0]].
    apply qsum_pos_of_mem with (y := L_raw S u w0).
    - intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [w' [<- Hw']].
      unfold L_raw; apply Qmult_le_0_compat;
        [exact (Hnn w' u Hw' Hu) | apply Qlt_le_weak, prior_pos, Hw'].
    - apply in_map; exact Hw0.
    - unfold L_raw; apply Qmult_lt_0_compat;
        [exact (proj2 (Hsup w0 u Hw0 Hu) Hm0) | apply prior_pos; exact Hw0]. }
  split.
  - intros Hpos; destruct (meaning u w) eqn:Em; [reflexivity |].
    assert (Hs0 : S w u == 0).
    { assert (Hn := Hnn w u Hw Hu).
      destruct (Qlt_le_dec 0 (S w u)) as [Hlt | Hle].
      - rewrite (proj1 (Hsup w u Hw Hu) Hlt) in Em; discriminate Em.
      - lra. }
    assert (H0 : L_of S u w == 0).
    { apply normalize_num_zero; unfold L_raw; rewrite Hs0; ring. }
    lra.
  - intros Hm; unfold L_of; rewrite normalize_spec.
    apply Qdiv_pos; [| exact Hnorm].
    unfold L_raw; apply Qmult_lt_0_compat;
      [exact (proj2 (Hsup w u Hw Hu) Hm) | apply prior_pos; exact Hw].
Qed.

Lemma L_of_nonneg_gen : forall (S : W -> U -> Q),
  (forall w u, In w ws -> In u us -> 0 <= S w u) ->
  forall u w, In u us -> In w ws -> 0 <= L_of S u w.
Proof.
  intros S Hnn u w Hu Hw; apply normalize_nonneg.
  - unfold L_raw; apply Qmult_le_0_compat;
      [exact (Hnn w u Hw Hu) | apply Qlt_le_weak, prior_pos, Hw].
  - intros x Hx; unfold L_raw; apply Qmult_le_0_compat;
      [exact (Hnn x u Hx Hu) | apply Qlt_le_weak, prior_pos, Hx].
Qed.

(* The depth invariant: support is exactly the denotation at EVERY
   level, under Bergen's restrictions made global (ARTIFACT-v). *)
Theorem Ln_invariant :
  (0 < alpha)%nat ->
  (forall u, In u us -> consistent u = true) ->
  (forall w, In w ws -> expressible w = true) ->
  forall n,
  (forall u w, In u us -> In w ws -> 0 <= Ln n u w) /\
  (forall u w, In u us -> In w ws -> (0 < Ln n u w <-> meaning u w = true)).
Proof.
  intros Ha Hcons Hexp; induction n as [| m [IHnn IHsup]].
  - split.
    + intros u w _ Hw; apply L0_nonneg, Hw.
    + intros u w Hu Hw; apply L0_support; [exact Hw | apply Hcons, Hu].
  - assert (Snn : forall w u, In w ws -> In u us ->
              0 <= S_of (Ln m) w u).
    { intros w u Hw Hu.
      apply (S_of_nonneg_gen (Ln m) IHnn w u Hw Hu). }
    assert (Ssup : forall w u, In w ws -> In u us ->
              (0 < S_of (Ln m) w u <-> meaning u w = true)).
    { intros w u Hw Hu.
      apply (S_of_support_gen (Ln m) Ha IHnn IHsup w u Hw Hu).
      apply Hexp, Hw. }
    split; simpl.
    + intros u w Hu Hw.
      apply (L_of_nonneg_gen (S_of (Ln m)) Snn u w Hu Hw).
    + intros u w Hu Hw.
      apply (L_of_support_gen (S_of (Ln m)) Snn Ssup u w Hu Hw).
      apply Hcons, Hu.
Qed.

(* T26.  The support theorem, extracted. *)
Theorem Ln_support :
  (0 < alpha)%nat ->
  (forall u, In u us -> consistent u = true) ->
  (forall w, In w ws -> expressible w = true) ->
  forall n u w, In u us -> In w ws ->
  (0 < Ln n u w <-> meaning u w = true).
Proof.
  intros Ha Hcons Hexp n u w Hu Hw.
  exact (proj2 (Ln_invariant Ha Hcons Hexp n) u w Hu Hw).
Qed.

(* T27.  Distributions at every depth — the conditions are the depth-1
   ones, globalized. *)
Theorem Ln_dist :
  (0 < alpha)%nat ->
  (forall u, In u us -> consistent u = true) ->
  (forall w, In w ws -> expressible w = true) ->
  forall n u, In u us -> IsDist (Ln n u) ws.
Proof.
  intros Ha Hcons Hexp n u Hu.
  destruct n as [| m].
  - apply L0_dist_iff, Hcons, Hu.
  - destruct (Ln_invariant Ha Hcons Hexp m) as [IHnn IHsup].
    assert (Snn : forall w u', In w ws -> In u' us ->
              0 <= S_of (Ln m) w u')
      by (intros; apply S_of_nonneg_gen; assumption).
    assert (Ssup : forall w u', In w ws -> In u' us ->
              (0 < S_of (Ln m) w u' <-> meaning u' w = true)).
    { intros w u' Hw Hu'.
      apply (S_of_support_gen (Ln m) Ha IHnn IHsup w u' Hw Hu').
      apply Hexp, Hw. }
    split; simpl.
    + intros w Hw.
      apply (L_of_nonneg_gen (S_of (Ln m)) Snn u w Hu Hw).
    + apply normalize_sum.
      destruct (proj1 (consistent_iff u) (Hcons u Hu)) as [w0 [Hw0 Hm0]].
      apply qsum_pos_of_mem with (y := L_raw (S_of (Ln m)) u w0).
      * intros x Hx.
        destruct (proj1 (in_map_iff _ _ _) Hx) as [w' [<- Hw']].
        unfold L_raw; apply Qmult_le_0_compat;
          [exact (Snn w' u Hw' Hu) | apply Qlt_le_weak, prior_pos, Hw'].
      * apply in_map; exact Hw0.
      * unfold L_raw; apply Qmult_lt_0_compat;
          [exact (proj2 (Ssup w0 u Hw0 Hu) Hm0) |
           apply prior_pos; exact Hw0].
Qed.

Theorem Sn_dist :
  (0 < alpha)%nat ->
  (forall u, In u us -> consistent u = true) ->
  (forall w, In w ws -> expressible w = true) ->
  forall n w, In w ws -> IsDist (Sn (S n) w) us.
Proof.
  intros Ha Hcons Hexp n w Hw.
  destruct (Ln_invariant Ha Hcons Hexp n) as [IHnn IHsup].
  split.
  - intros u Hu.
    apply (S_of_nonneg_gen (Ln n) IHnn w u Hw Hu).
  - apply normalize_sum.
    destruct (proj1 (expressible_iff w) (Hexp w Hw)) as [u0 [Hu0 Hm0]].
    apply qsum_pos_of_mem with (y := S_raw (Ln n) w u0).
    + intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [u' [<- Hu']].
      apply S_raw_nonneg_gen; [exact (IHnn u' w Hu' Hw) | exact Hu'].
    + apply in_map; exact Hu0.
    + apply S_raw_pos_gen; [| exact Hu0].
      exact (proj2 (IHsup u0 w Hu0 Hw) Hm0).
Qed.

End RSA.

(* ========================================================================== *)
(*  Part 9b — Permutation well-definedness (T25): the list order is           *)
(*  spurious structure (ARTIFACT-iv)                                          *)
(* ========================================================================== *)

Lemma normalize_ext : forall (A : Type) (f g : A -> Q) (l : list A) (a : A),
  (forall x, f x == g x) ->
  normalize f l a == normalize g l a.
Proof.
  intros A f g l a H.
  rewrite !normalize_spec, (H a).
  rewrite (qsum_map_ext_in A f g l (fun x _ => H x)); reflexivity.
Qed.

Section Perm.

Variables (W U : Type).
Variables (ws ws' : list W) (us us' : list U).
Variable meaning : U -> W -> bool.
Variable prior : W -> Q.
Variable costw : U -> Q.
Variable alpha : nat.
Hypothesis Hws : Permutation ws ws'.
Hypothesis Hus : Permutation us us'.

Lemma S_of_perm_ext : forall (L L' : U -> W -> Q),
  (forall u w, L u w == L' u w) ->
  forall w u,
  S_of W U us costw alpha L w u == S_of W U us' costw alpha L' w u.
Proof.
  intros L L' HL w u; unfold S_of, S_raw.
  transitivity
    (normalize (fun u0 => Qred (qpow (L' u0 w) alpha) * costw u0) us u).
  - apply normalize_ext; intros u0.
    rewrite !Qred_correct, (HL u0 w); reflexivity.
  - apply normalize_perm; exact Hus.
Qed.

(* T25.  The whole tower is invariant under permuting the enumerations —
   the sources' SETS are faithfully represented by lists. *)
Theorem Ln_perm_invariant : forall n u w,
  Ln W U ws us meaning prior costw alpha n u w ==
  Ln W U ws' us' meaning prior costw alpha n u w.
Proof.
  induction n as [| m IH]; intros u w; simpl.
  - unfold L0; apply normalize_perm; exact Hws.
  - unfold L_of, L_raw.
    transitivity
      (normalize (fun w0 =>
         S_of W U us' costw alpha
           (Ln W U ws' us' meaning prior costw alpha m) w0 u * prior w0)
         ws w).
    + apply normalize_ext; intros w0.
      rewrite (S_of_perm_ext _ _ (fun u' w' => IH u' w') w0 u); reflexivity.
    + apply normalize_perm; exact Hws.
Qed.

End Perm.

(* ========================================================================== *)
(*  Part 10 — Scalar implicature, exact (T21, T28-T31): LG17 §3, GL15         *)
(*  §3.1, B16 §3.1                                                            *)
(* ========================================================================== *)

Module ScalarImplicature.

Inductive W3 := w0 | w1 | w2.       (* 0 / 1 / 2 objects have the property *)
Inductive U3 := usome | uall | unone.

Definition ws3 : list W3 := [w0; w1; w2].
Definition us3 : list U3 := [usome; uall; unone].
Definition meaning3 (u : U3) (w : W3) : bool :=
  match u, w with
  | usome, w1 | usome, w2 => true
  | uall, w2 => true
  | unone, w0 => true
  | _, _ => false
  end.
Definition prior3 (_ : W3) : Q := 1 # 3.
Definition costw3 (_ : U3) : Q := 1.

Definition L0e := L0 W3 U3 ws3 meaning3 prior3.
Definition S1a (a : nat) := S1 W3 U3 ws3 us3 meaning3 prior3 costw3 a.
Definition L1a (a : nat) := L1 W3 U3 ws3 us3 meaning3 prior3 costw3 a.
Definition Lna (n : nat) := Ln W3 U3 ws3 us3 meaning3 prior3 costw3 1 n.

(* T28.  The exact pragmatic posterior at alpha = 1. *)
Theorem scalar_L1_values :
  L1a 1 usome w1 == 3 # 4 /\ L1a 1 usome w2 == 1 # 4 /\ L1a 1 usome w0 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem scalar_implicature : L1a 1 usome w2 < L1a 1 usome w1.
Proof. vm_compute; reflexivity. Qed.

(* T29.  The literal listener does NOT derive it. *)
Theorem scalar_L0_values : L0e usome w1 == 1 # 2 /\ L0e usome w2 == 1 # 2.
Proof. split; vm_compute; reflexivity. Qed.

Theorem scalar_L0_fails : L0e usome w1 == L0e usome w2.
Proof. vm_compute; reflexivity. Qed.

(* T30.  Sharper with rationality and with depth. *)
Theorem scalar_alpha4 :
  L1a 4 usome w1 == 17 # 18 /\ L1a 4 usome w2 == 1 # 18.
Proof. split; vm_compute; reflexivity. Qed.

Theorem scalar_depth3 :
  Lna 3 usome w1 == 7 # 8 /\ Lna 3 usome w2 == 1 # 8.
Proof. split; vm_compute; reflexivity. Qed.

(* T21.  The speaker prefers the informative alternative (LG17 p. 13). *)
Theorem S1_prefers_informative :
  S1a 1 w2 uall == 2 # 3 /\ S1a 1 w2 usome == 1 # 3.
Proof. split; vm_compute; reflexivity. Qed.

(* T31.  The implicature at EVERY rationality alpha > 0 (LG17 fn. 6:
   the preference "does not depend on this parameter") — symbolic. *)
Theorem scalar_implicature_any_alpha : forall a,
  (0 < a)%nat -> L1a a usome w2 < L1a a usome w1.
Proof.
  intros a Ha.
  assert (Hqpos : 0 < qpow (1 # 2) a) by (apply qpow_pos; lra).
  assert (HL0s1 : L0e usome w1 == 1 # 2) by (vm_compute; reflexivity).
  assert (HL0s2 : L0e usome w2 == 1 # 2) by (vm_compute; reflexivity).
  assert (HL0a1 : L0e uall w1 == 0) by (vm_compute; reflexivity).
  assert (HL0a2 : L0e uall w2 == 1) by (vm_compute; reflexivity).
  assert (HL0n1 : L0e unone w1 == 0) by (vm_compute; reflexivity).
  assert (HL0n2 : L0e unone w2 == 0) by (vm_compute; reflexivity).
  assert (Hraw : forall u w,
    S_raw W3 U3 costw3 a L0e w u == qpow (L0e u w) a).
  { intros u w; unfold S_raw; rewrite Qred_correct; unfold costw3; ring. }
  assert (HS1w1 : S1a a w1 usome == 1).
  { assert (Hspec : S1a a w1 usome ==
      S_raw W3 U3 costw3 a L0e w1 usome /
      qsum (map (S_raw W3 U3 costw3 a L0e w1) us3))
      by exact (normalize_spec _ _ _ _).
    rewrite Hspec; unfold us3; simpl map; unfold qsum; simpl fold_right.
    rewrite !Hraw, HL0s1, HL0a1, HL0n1, (qpow_zero a Ha).
    field; apply ne_of_lt; lra. }
  assert (HS1w2 : S1a a w2 usome ==
                  qpow (1 # 2) a / (qpow (1 # 2) a + 1)).
  { assert (Hspec : S1a a w2 usome ==
      S_raw W3 U3 costw3 a L0e w2 usome /
      qsum (map (S_raw W3 U3 costw3 a L0e w2) us3))
      by exact (normalize_spec _ _ _ _).
    rewrite Hspec; unfold us3; simpl map; unfold qsum; simpl fold_right.
    rewrite !Hraw, HL0s2, HL0a2, HL0n2, (qpow_zero a Ha), qpow_one.
    setoid_replace (qpow (1 # 2) a + (1 + (0 + 0)))
      with (qpow (1 # 2) a + 1) by ring.
    reflexivity. }
  assert (HSlt : S1a a w2 usome < S1a a w1 usome).
  { rewrite HS1w1, HS1w2.
    assert (Hinv : 0 < / (qpow (1 # 2) a + 1))
      by (apply Qinv_lt_0_compat; lra).
    unfold Qdiv.
    assert (Hstep : qpow (1 # 2) a * / (qpow (1 # 2) a + 1) <
                    (qpow (1 # 2) a + 1) * / (qpow (1 # 2) a + 1)).
    { apply Qmult_lt_compat_r; [exact Hinv | lra]. }
    rewrite Qmult_inv_r in Hstep; [lra | apply ne_of_lt; lra]. }
  assert (Hps : 0 < PS W3 U3 ws3 us3 meaning3 prior3 costw3 a usome).
  { unfold PS.
    apply qsum_pos_of_mem with (y := S1a a w1 usome * prior3 w1).
    - intros x Hx.
      destruct (proj1 (in_map_iff _ _ _) Hx) as [w' [<- Hw']].
      apply Qmult_le_0_compat.
      + apply S1_nonneg.
        * intros w'' _; unfold prior3; lra.
        * intros u'' _; unfold costw3; lra.
        * exact Hw'.
        * simpl; auto.
      + unfold prior3; lra.
    - exact (in_map (fun w => S1a a w usome * prior3 w) ws3 w1
               (or_intror (or_introl eq_refl))).
    - rewrite HS1w1; unfold prior3; lra. }
  apply L1_order_from_S1 with (w := w1) (w' := w2).
  - intros w'' _; unfold prior3; lra.
  - simpl; auto.
  - simpl; auto.
  - reflexivity.
  - exact HSlt.
  - exact Hps.
Qed.

End ScalarImplicature.

(* ========================================================================== *)
(*  Part 11 — Worked examples (T32-T34)                                       *)
(* ========================================================================== *)

(* GF16 Figure 1: three faces (with-Hat-and-Glasses, with-Glasses, None),
   two utterances. *)
Module Faces.

Inductive WF := HG | G | N.
Inductive UF := glasses | hat.
Definition wsF : list WF := [HG; G; N].
Definition usF : list UF := [glasses; hat].
Definition meaningF (u : UF) (w : WF) : bool :=
  match u, w with
  | glasses, HG | glasses, G => true
  | hat, HG => true
  | _, _ => false
  end.
Definition priorF (_ : WF) : Q := 1 # 3.
Definition costwF (_ : UF) : Q := 1.
Definition L0F := L0 WF UF wsF meaningF priorF.
Definition L1F := L1 WF UF wsF usF meaningF priorF costwF 1.

(* T32.  "hat" pins HG; "glasses" is literally ambiguous; the pragmatic
   listener shifts "glasses" to the face for which no better utterance
   exists (GF16 p. 820). *)
Theorem faces_hat : L0F hat HG == 1.
Proof. vm_compute; reflexivity. Qed.

Theorem faces_L0_ambiguous : L0F glasses G == L0F glasses HG.
Proof. vm_compute; reflexivity. Qed.

Theorem faces_implicature : L1F glasses HG < L1F glasses G.
Proof. vm_compute; reflexivity. Qed.

End Faces.

(* B16 §3.1: two worlds, two utterances; the implicature strengthens
   with depth exactly as the p |-> p/(2p+1) table (p. 20:16). *)
Module BergenTwoWorlds.

Inductive WB := wall | wsna.          (* forall / exists-not-forall *)
Inductive UB := bsome | ball.
Definition wsB : list WB := [wall; wsna].
Definition usB : list UB := [bsome; ball].
Definition meaningB (u : UB) (w : WB) : bool :=
  match u, w with
  | bsome, _ => true
  | ball, wall => true
  | _, _ => false
  end.
Definition priorB (_ : WB) : Q := 1 # 2.
Definition costwB (_ : UB) : Q := 1.
Definition LnB := Ln WB UB wsB usB meaningB priorB costwB 1.

(* T33.  The table: L_n(all | some) = 1/4, 1/6, 1/8, 1/10. *)
Theorem bergen_table :
  LnB 1 bsome wall == 1 # 4 /\
  LnB 2 bsome wall == 1 # 6 /\
  LnB 3 bsome wall == 1 # 8 /\
  LnB 4 bsome wall == 1 # 10.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem bergen_all_truthful :
  LnB 1 ball wsna == 0 /\ LnB 4 ball wsna == 0.
Proof. split; vm_compute; reflexivity. Qed.

End BergenTwoWorlds.

(* LG17 §3 eqs. (15)-(20): seven worlds (0-6 cookies eaten), alpha = 4,
   constant cost C(u) = 4 (so costw = 1). *)
Module Cookies.

Inductive WC := n0 | n1 | n2 | n3 | n4 | n5 | n6.
Inductive UC := NONE | SOME | ALL.
Definition wsC : list WC := [n0; n1; n2; n3; n4; n5; n6].
Definition usC : list UC := [NONE; SOME; ALL].
Definition meaningC (u : UC) (w : WC) : bool :=
  match u, w with
  | NONE, n0 => true
  | SOME, n0 => false
  | SOME, _ => true
  | ALL, n6 => true
  | _, _ => false
  end.
Definition priorC (w : WC) : Q :=
  match w with n0 => 94 # 100 | _ => 1 # 100 end.
Definition costwC (_ : UC) : Q := 1.
Definition L0C := L0 WC UC wsC meaningC priorC.
Definition S1C := S1 WC UC wsC usC meaningC priorC costwC 4.
Definition L1C := L1 WC UC wsC usC meaningC priorC costwC 4.

(* T34.  The exact values.  FIDELITY NOTE: LG17 eq. (20) prints
   L1(6|SOME) ~ .015, but the paper's own displayed formula evaluates to
   ~ .0002 and the exact value is 1/6486 ~ .00015; the qualitative claim
   (ALL-worlds are suppressed under SOME) holds — the printed figure is
   recorded as a slip, not silently corrected. *)
Theorem cookies_values :
  L1C SOME n0 == 0 /\
  S1C n6 SOME == 1 # 1297 /\
  L1C SOME n6 == 1 # 6486 /\
  L1C SOME n1 == 1297 # 6486.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem cookies_suppression : L1C SOME n6 < L0C SOME n6.
Proof. vm_compute; reflexivity. Qed.

Theorem cookies_L0_value : L0C SOME n6 == 1 # 6.
Proof. vm_compute; reflexivity. Qed.

End Cookies.

(* ========================================================================== *)
(*  Part 12 — The symmetry problem (T35): B16 §3.2                            *)
(* ========================================================================== *)

Module Symmetry.

Import ScalarImplicature (W3, w0, w1, w2).

Inductive U4 := s4 | a4 | n4 | sbna4.   (* some / all / none / some-but-not-all *)
Definition ws4 : list W3 := [w0; w1; w2].
Definition us4 : list U4 := [s4; a4; n4; sbna4].
Definition meaning4 (u : U4) (w : W3) : bool :=
  match u, w with
  | s4, w1 | s4, w2 => true
  | a4, w2 => true
  | n4, w0 => true
  | sbna4, w1 => true
  | _, _ => false
  end.
Definition prior4 (_ : W3) : Q := 1 # 3.
Definition size4 (u : U4) : nat :=
  match u with s4 => 1 | a4 => 1 | n4 => 2 | sbna4 => 3 end.
Definition cost_flat (_ : U4) : Q := 1.
Definition cost_size (u : U4) : Q := qpow (1 # 2) (size4 u).

Definition L1flat := L1 W3 U4 ws4 us4 meaning4 prior4 cost_flat 1.
Definition L1size := L1 W3 U4 ws4 us4 meaning4 prior4 cost_size 1.

(* T35.  With "some but not all" among the alternatives and flat costs,
   the implicature is neutralized (the symmetry problem); size-weighted
   costs restore it (B16 §3.2). *)
Theorem symmetry_neutral :
  L1flat s4 w1 == 1 # 2 /\ L1flat s4 w2 == 1 # 2.
Proof. split; vm_compute; reflexivity. Qed.

Theorem symmetry_broken :
  L1size s4 w1 == 2 # 3 /\ L1size s4 w2 == 1 # 3.
Proof. split; vm_compute; reflexivity. Qed.

End Symmetry.

(* ========================================================================== *)
(*  Part 13 — Assumption audit                                                *)
(* ========================================================================== *)
(* Output under Coq 8.20.1 (2026-09-05): every theorem below prints
   "Closed under the global context" — zero axioms, constructive,
   decidable order on Q throughout. *)
Print Assumptions L0_dist_iff.
Print Assumptions L0_is_conditioning.
Print Assumptions L0_uniform_card.
Print Assumptions S1_dist_iff.
Print Assumptions speaker_truthful.
Print Assumptions S1_alpha0.
Print Assumptions L1_dist_iff.
Print Assumptions L1_bayes.
Print Assumptions L1_product.
Print Assumptions L1_unique.
Print Assumptions L0_strictly_more_specific.
Print Assumptions S1_more_specific.
Print Assumptions size_principle.
Print Assumptions Ln_sem_equiv.
Print Assumptions no_M_implicature.
Print Assumptions Ln_support.
Print Assumptions Ln_dist.
Print Assumptions Ln_perm_invariant.
Print Assumptions ScalarImplicature.scalar_implicature.
Print Assumptions ScalarImplicature.scalar_implicature_any_alpha.
Print Assumptions BergenTwoWorlds.bergen_table.
Print Assumptions Cookies.cookies_values.
Print Assumptions Symmetry.symmetry_broken.
