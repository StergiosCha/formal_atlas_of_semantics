(* ========================================================================== *)
(*  Pragmatic_Anaphora.v — a finite fragment of Bayesian pragmatics for       *)
(*  pronoun resolution                                                        *)
(*  FORMAL-ATLAS / atlas/probabilistic                                        *)
(* ========================================================================== *)
(*
   SOURCE [GBC21]: Grove, Bernardy and Chatzikyriakidis 2021, Proc. 1st and
   2nd Workshops on Natural Logic Meets Machine Learning (NALOMA),
   pp. 60-70 (ACL Anthology 2021.naloma-1.8).  Read: sec. 2.3 pp. 61-62
   (the model), sec. 3 p. 63 (anaphora), secs. 4-5 pp. 63-64 (the two
   examples and their priors).  Not read: secs. 2.1-2.2 in full (the
   monadic composition), the result tables, sec. 6.
     sec. 2.3  PL0(phi | u) = E_{theta,Gamma}[Gamma, phi, [[u]]theta |/- bot]
               PS1(u | phi) ~ (PL0(phi | u) / C(u))^alpha
               PL1(phi | u) ~ PS1(u | phi) * P(phi)
               P(phi) ~ E_Gamma[Gamma, phi |/- bot] * P(theta)
     sec. 2.3  Gamma "describes a world state"; sec. 4: a world state fixes
               each background formula or its negation
     sec. 3    theta maps anaphoric expressions to antecedents
     sec. 4    example (1): "Emacs is waiting for the command. It is
               prepared."; animacy priors 0.2 for things, 0.9 for persons;
               0.05 for the other background formulas; lexical entailments
               filter world states

   THE FRAGMENT (ours).  World states are a finite list with exact rational
   weights.  A world state is complete, so "Gamma together with phi does
   not entail a contradiction" is read as "phi is true at Gamma"; N1
   justifies this reading for Boolean formulas.  alpha = 1 and all costs
   are equal in the worked models.  The paper's own results use other
   values of alpha and cost and are not reproduced.

   N1  complete_state_consistency  non-contradiction with a complete world
                                   state is truth at it
   N2  PL0_bounds                  the literal listener is nonnegative and
                                   monotone in the proposition
   N3  PL0_is_RSA_literal          for an unambiguous utterance and a
                                   complete description of a world, PL0 is
                                   the literal listener of RSA.v before
                                   normalisation
   and two worked models of example (1). *)

From Coq Require Import List Bool QArith Arith.
Import ListNotations.
Require Import RSA.
Import QSum.
Require Import Bayesian_Semantics.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* N1.  Complete world states                                          *)
(* ------------------------------------------------------------------ *)

Inductive fml : Type :=
| FVar (n : nat) | FNot (f : fml) | FAnd (f g : fml) | FOr (f g : fml).

Fixpoint ev (v : nat -> bool) (f : fml) : bool :=
  match f with
  | FVar n => v n | FNot f => negb (ev v f)
  | FAnd f g => ev v f && ev v g | FOr f g => ev v f || ev v g
  end.

Fixpoint atoms (f : fml) : list nat :=
  match f with
  | FVar n => [n] | FNot f => atoms f
  | FAnd f g | FOr f g => atoms f ++ atoms g
  end.

(* v' satisfies the world state that fixes the variables in vars as v does. *)
Definition agree (vars : list nat) (v v' : nat -> bool) : Prop :=
  forall n, In n vars -> v' n = v n.

Lemma ev_coincide (f : fml) (v v' : nat -> bool) :
  (forall n, In n (atoms f) -> v' n = v n) -> ev v' f = ev v f.
Proof.
  induction f as [n|f IH|f IHf g IHg|f IHf g IHg]; simpl; intros H.
  - apply H. left. reflexivity.
  - rewrite (IH H). reflexivity.
  - rewrite IHf, IHg; [reflexivity| |]; intros n Hn; apply H; apply in_or_app; tauto.
  - rewrite IHf, IHg; [reflexivity| |]; intros n Hn; apply H; apply in_or_app; tauto.
Qed.

(* N1.  [GBC21] sec. 2.3, sec. 4.  If a world state decides every atom of
   phi, then "Gamma, phi does not entail a contradiction" (some valuation
   satisfies both) holds exactly when phi is true at the world state. *)
Theorem complete_state_consistency : forall (vars : list nat) (v : nat -> bool) (f : fml),
  (forall n, In n (atoms f) -> In n vars) ->
  ((exists v', agree vars v v' /\ ev v' f = true) <-> ev v f = true).
Proof.
  intros vars v f Hat. split.
  - intros (v' & Ha & He). rewrite <- He. symmetry.
    apply ev_coincide. intros n Hn. apply Ha. apply Hat. exact Hn.
  - intros He. exists v. split; [intros n _; reflexivity | exact He].
Qed.

(* ------------------------------------------------------------------ *)
(* N2, N3.  The literal listener                                       *)
(* ------------------------------------------------------------------ *)

Section Listener.
Variables W Theta U : Type.
Variable ws : list W.
Variable prior : W -> Q.
Variable thetas : list Theta.
Variable ptheta : Theta -> Q.
Variable meaning : U -> Theta -> W -> bool.

(* [GBC21] sec. 2.3: PL0(phi | u), the expected value over theta and the
   world state of "phi and [[u]]theta hold". *)
Definition PL0 (phi : W -> bool) (u : U) : Q :=
  qsum (map (fun th => ptheta th * mass prior ws (fun w => phi w && meaning u th w))
            thetas).

(* N2.  PL0 is nonnegative and grows with the proposition. *)
Theorem PL0_bounds : nonneg prior ws -> nonneg ptheta thetas ->
  forall (phi psi : W -> bool) (u : U),
    0 <= PL0 phi u /\
    ((forall w, In w ws -> phi w = true -> psi w = true) -> PL0 phi u <= PL0 psi u).
Proof.
  intros Hp Ht phi psi u. split.
  - unfold PL0. apply qsum_nonneg. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as (th & <- & Hth).
    apply Qmult_le_0_compat; [apply Ht; exact Hth | apply mass_nonneg; exact Hp].
  - intros H. unfold PL0. apply qsum_le_in. intros th Hth.
    rewrite (Qmult_comm (ptheta th)), (Qmult_comm (ptheta th)).
    apply Qmult_le_compat_r; [|apply Ht; exact Hth].
    apply mass_le; [exact Hp|]. intros w Hw E.
    apply andb_true_iff in E. destruct E as [E1 E2].
    apply andb_true_iff. split; [apply H; assumption | exact E2].
Qed.

Variable eqb : W -> W -> bool.
Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

Lemma mass_point (h : W -> bool) (w : W) : NoDup ws -> In w ws ->
  mass prior ws (fun v => eqb v w && h v) == (if h w then prior w else 0).
Proof.
  unfold mass. induction ws as [|a t IH]; intros Hnd Hin; [destruct Hin|].
  inversion Hnd as [|? ? Hna Hnt]; subst. simpl.
  destruct Hin as [->|Hin].
  - assert (E : eqb w w = true) by (apply eqb_spec; reflexivity). rewrite E. simpl.
    assert (Z : qsum (map (fun v => if eqb v w && h v then prior v else 0) t) == 0).
    { apply qsum_zero_of. intros v Hv.
      destruct (eqb v w) eqn:Ev; [|reflexivity].
      apply eqb_spec in Ev. subst v. contradiction. }
    rewrite Z. destruct (h w); ring.
  - assert (E : eqb a w = false).
    { destruct (eqb a w) eqn:Ea; [|reflexivity].
      apply eqb_spec in Ea. subst a. contradiction. }
    rewrite E. simpl. rewrite (IH Hnt Hin). ring.
Qed.

(* N3.  The bridge.  If u means the same under every theta, the weights of
   theta sum to 1, and phi is the complete description of one world w, then
   PL0 is the literal listener of RSA.v before normalisation: the prior of
   w if u is true there, and 0 otherwise.  With B5 of R3, normalising it
   over the worlds gives conditioning on the truth of u. *)
Theorem PL0_is_RSA_literal : forall (u : U) (m : W -> bool) (w : W),
  (forall th v, In th thetas -> meaning u th v = m v) ->
  qsum (map ptheta thetas) == 1 -> NoDup ws -> In w ws ->
  PL0 (fun v => eqb v w) u == (if m w then prior w else 0).
Proof.
  intros u m w Hm Hsum Hnd Hin. unfold PL0.
  transitivity (qsum (map (fun th => (if m w then prior w else 0) * ptheta th) thetas)).
  - apply qsum_map_ext_in. intros th Hth.
    assert (E : mass prior ws (fun v => eqb v w && meaning u th v) ==
                mass prior ws (fun v => eqb v w && m v)).
    { apply mass_ext. intros v _. rewrite (Hm th v Hth). reflexivity. }
    rewrite E, (mass_point m w Hnd Hin). ring.
  - rewrite qsum_scale, Hsum. ring.
Qed.

End Listener.

(* ------------------------------------------------------------------ *)
(* Worked models: example (1) of [GBC21] sec. 4                        *)
(* ------------------------------------------------------------------ *)

Module Emacs.

(* A world state fixes four background formulas: animate(emacs),
   animate(the command), prepared(emacs), prepared(the command). *)
Definition Wd := (bool * bool * bool * bool)%type.
Definition bools : list bool := [true; false].
Definition wsd : list Wd := list_prod (list_prod (list_prod bools bools) bools) bools.
Definition ae (w : Wd) := fst (fst (fst w)).
Definition ac (w : Wd) := snd (fst (fst w)).
Definition pe (w : Wd) := snd (fst w).
Definition pc (w : Wd) := snd w.

(* Independent priors, pa for each animacy formula and 0.05 for each
   "prepared" formula; the lexical entailment prepared(x) -> animate(x)
   filters world states; the first sentence has been accepted, so
   animate(emacs) holds (the subject of "waiting" is animate). *)
Definition bern (p : Q) (b : bool) : Q := if b then p else 1 - p.
Definition raw (pa : Q) (w : Wd) : Q :=
  if ae w && implb (pe w) (ae w) && implb (pc w) (ac w)
  then bern pa (ae w) * bern pa (ac w) * bern (1 # 20) (pe w) * bern (1 # 20) (pc w)
  else 0.
Definition pri (pa : Q) : Wd -> Q := normalize (raw pa) wsd.

(* theta = true resolves "it" to Emacs, false to the command.  The
   alternatives to the pronoun sentence name the antecedent. *)
Inductive utt := It | NameE | NameC.
Definition mng (u : utt) (th : bool) (w : Wd) : bool :=
  match u with It => if th then pe w else pc w | NameE => pe w | NameC => pc w end.
Definition half (_ : bool) : Q := 1 # 2.

Definition l0 (pa : Q) := PL0 Wd bool utt wsd (pri pa) bools half mng.
(* alpha = 1 and equal costs: the speaker is PL0 normalised over the
   alternatives for the intended proposition. *)
Definition s1 (pa : Q) (phi : Wd -> bool) (alts : list utt) (u : utt) : Q :=
  l0 pa phi u / qsum (map (l0 pa phi) alts).
Definition pphi (pa : Q) (phi : Wd -> bool) : Q := mass (pri pa) wsd phi * (1 # 2).
(* PL1 of "it = Emacs" on hearing "It is prepared". *)
Definition l1_emacs (pa : Q) : Q :=
  let a := s1 pa pe [It; NameE] It * pphi pa pe in
  let b := s1 pa pc [It; NameC] It * pphi pa pc in
  a / (a + b).

(* With the paper's prior 0.2 for the animacy of things: the proposition
   about Emacs is more probable a priori and for the literal listener, and
   the pragmatic listener resolves "it" to Emacs with probability
   47336/57451, about 0.82. *)
Example emacs_preferred :
  mass (pri (1 # 5)) wsd pe == 1 # 20 /\ mass (pri (1 # 5)) wsd pc == 1 # 96 /\
  l0 (1 # 5) pc It < l0 (1 # 5) pe It /\
  l1_emacs (1 # 5) == 47336 # 57451 /\ 4 # 5 < l1_emacs (1 # 5).
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Separating case, after example (2): with the prior 0.9 that the paper
   gives to persons, animacy no longer discriminates, and the resolution is
   close to even: 315614/601949, about 0.52. *)
Example less_certain_with_animate_candidates :
  l1_emacs (9 # 10) == 315614 # 601949 /\
  1 # 2 < l1_emacs (9 # 10) /\ l1_emacs (9 # 10) < 11 # 20 /\
  l1_emacs (9 # 10) < l1_emacs (1 # 5).
Proof. repeat split; vm_compute; reflexivity. Qed.

End Emacs.

Print Assumptions complete_state_consistency.
Print Assumptions PL0_bounds.
Print Assumptions PL0_is_RSA_literal.
Print Assumptions Emacs.emacs_preferred.
Print Assumptions Emacs.less_certain_with_animate_candidates.
