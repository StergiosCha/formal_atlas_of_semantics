Require Import List Bool.
Import ListNotations.

(* ========================================================================== *)
(*  Semantic_Monads.v — monads in natural-language semantics: a fragment      *)
(*  FORMAL-ATLAS / atlas/model_theoretic (standard library only)              *)
(* ========================================================================== *)
(*
   SOURCES (read for this file)
     [Shan]  Shan, C. (2001/2002). Monads for natural language semantics.
             arXiv:cs/0205026v1, pp. 285-298.  Read in full.  Used: (24.1)-
             (24.3) and fn. 1 (monad, the three laws), §2.1 (24.4)-(24.13)
             (powerset monad, lifted application A_M and A'_M), §2.3 (24.16)-
             (24.18) (reader monad), §2.4 (24.19)-(24.22) (continuation monad,
             evaluation, "everyone"), fn. 6.
     [G&A]   Giorgolo, G. & Asudeh, A. (2014). Monads as a solution for
             generalized opacity.  Proc. EACL 2014 Workshop TTNLS, pp. 19-27.
             Read: §1-§3 (pp. 19-25).  Used: (9), (10) (unit and bind of their
             monad), Table 1 p. 23 (lexicon), (29)-(34) pp. 24-25, fn. 6 p. 23.
   SOURCE NOT AVAILABLE
     Charlow's dissertation (2014) was not available when this file was
     written.  Nothing in this file is taken from or attributed to it.

   WHAT IS FORMALIZED
     A monad is a type constructor with a unit and a bind [Shan (24.2)].
     Three of Shan's monads are given as instances of one record: the powerset
     monad (24.4), the reader monad (24.16) and the continuation monad (24.19).
     Shan's lifted application A_M (24.8) and A'_M (24.12) are defined ONCE,
     for an arbitrary monad, and then instantiated.
       T1  set_monad_laws      the three laws (24.3a-c) for the powerset monad
       T2  reader_monad_laws   the same for the reader monad
       T3  cont_monad_laws     the same for the continuation monad
       T4  lifted_application  A_M unfolds to (24.9), (24.17), (24.21)
                               (from the lemmas AM_set, AM_reader, AM_cont)
       T5  secondary_rule      A'_M f x = A_M f (unit x)  [Shan p. 290]
                               (from AM'_set, AM'_reader, AM'_cont)
       T6  reader_commutative  the reader monad is commutative [G&A fn. 6]
       T7  transparent_substitution
                               bind into a continuation respects co-reference
                               at the index of evaluation (ours)
       T8  opacity_readings    the truth conditions (33), (34), (30) of G&A
                               (from three lemmas, one per reading)
     These are the eight main theorems; the nine lemmas they are assembled
     from are audited too.
     Worked model (two individuals; four entities and three interpretation
     indices for G&A): Shan's m1 * k1, "John smokes", "everyone smokes",
     "everyone loves someone", G&A's sentences (2) and (3).
     Separating examples (negations on the model):
       S1  cont_not_commutative, scope_readings_differ
       S2  substitution_fails_under_love

   NOT FORMALIZED (and why)
     * Shan's pointed powerset monad (24.14)-(24.15): a pointed set carries a
       proof of membership, so its laws need either proof irrelevance or a
       quotient; left out.
     * Shan §3 (monad morphisms (24.25)-(24.30), the translations (24.31)-
       (24.39)), and shift/reset (24.23)-(24.24).
     * The state monad and the error monad: Shan only mentions them in fn. 6
       and gives no definition, so there is nothing to formalize from him.
     * G&A's sequent calculus (Fig. 1) and the enumeration of readings by
       proof search.  The readings (29), (31), (32) are entered as terms.
     * G&A's "believe" examples (1), (4), (5): the belief operator B is left
       unspecified in the source; only the "love"/"punch" examples are done.
     * Anything from Charlow (source not available, see above).

   REPRESENTATION CHOICES
     * The record Monad has no law fields.  The laws are stated pointwise for
       each instance: as "iff" at every element for sets-as-predicates, as
       equalities at every index for the reader monad, at every continuation
       for the continuation monad.  No function extensionality is used.
     * Sets are predicates A -> Prop, as in Shan's "M alpha = alpha -> t".
     * In the worked model the answer type of the continuation monad is bool
       and quantifiers range over a finite list, so that sentences compute.
     * Truth values in the G&A fragment are booleans.
*)

(* ========================================================================== *)
(*  1. Monads, lifted application                                             *)
(* ========================================================================== *)

(* A monad: a type constructor M with unit and bind.  [Shan (24.2), p. 286] *)
Record Monad : Type := mkMonad {
  M : Type -> Type;
  unit : forall A : Type, A -> M A;
  bind : forall A B : Type, M A -> (A -> M B) -> M B }.
Arguments unit _ {A} _.
Arguments bind _ {A B} _ _.

(* Lifted function application A_M: the function is evaluated first, then the
   argument.  [Shan (24.8), p. 287] *)
Definition AM (T : Monad) {A B : Type} (f : M T (A -> B)) (x : M T A) : M T B :=
  bind T f (fun a => bind T x (fun b => unit T (a b))).

(* The secondary rule A'_M: lifted in the function only.  [Shan (24.12), p. 288] *)
Definition AM' (T : Monad) {A B : Type} (f : M T (M T A -> B)) (x : M T A)
  : M T B :=
  bind T f (fun a => unit T (a x)).

(* ours: the mirror image of A_M, with the argument evaluated first.  Used
   only to exhibit the second scope reading in S1. *)
Definition AMr (T : Monad) {A B : Type} (f : M T (A -> B)) (x : M T A) : M T B :=
  bind T x (fun b => bind T f (fun a => unit T (a b))).

(* The powerset monad.  [Shan (24.4a-c), p. 286] *)
Definition SetM : Monad :=
  mkMonad (fun A => A -> Prop)
          (fun A a => fun x => x = a)
          (fun A B m k => fun b => exists a, m a /\ k a b).

(* The reader monad over a fixed type R (worlds, assignments).
   [Shan (24.16a-c), p. 289].  G&A's monad is this one with R the type of
   interpretation indices: unit (9) and bind (10), p. 21. *)
Definition Reader (R : Type) : Monad :=
  mkMonad (fun A => R -> A)
          (fun A a => fun _ => a)
          (fun A B m k => fun w => k (m w) w).

(* The continuation monad with answer type O.  [Shan (24.19a-c), p. 290] *)
Definition Cont (O : Type) : Monad :=
  mkMonad (fun A => (A -> O) -> O)
          (fun A a => fun c => c a)
          (fun A B m k => fun c => m (fun a => k a c)).

(* Evaluation: feed the identity continuation.  [Shan p. 291, "epsilon"] *)
Definition eval {O : Type} (m : M (Cont O) O) : O := m (fun x => x).

(* ========================================================================== *)
(*  2. The monad laws, pointwise                                              *)
(* ========================================================================== *)

(* T1.  Left identity, right identity and associativity [Shan (24.3a-c),
   fn. 1 p. 286] for the powerset monad (24.4), as equivalences of membership. *)
Theorem set_monad_laws :
  forall (A B C : Type) (a : A) (m : M SetM A)
         (k : A -> M SetM B) (l : B -> M SetM C),
    (forall b, bind SetM (unit SetM a) k b <-> k a b) /\
    (forall x, bind SetM m (unit SetM (A:=A)) x <-> m x) /\
    (forall c, bind SetM (bind SetM m k) l c
               <-> bind SetM m (fun v => bind SetM (k v) l) c).
Proof.
  intros A B C a m k l; cbn; repeat split.
  - intros [a' [-> H]]; exact H.
  - intros H; exists a; split; [reflexivity | exact H].
  - intros [a' [H ->]]; exact H.
  - intros H; exists x; split; [exact H | reflexivity].
  - intros [b [[a' [Hm Hk]] Hl]]; exists a'; split; [exact Hm|].
    exists b; split; assumption.
  - intros [a' [Hm [b [Hk Hl]]]]; exists b; split; [|exact Hl].
    exists a'; split; assumption.
Qed.

(* T2.  The three laws (24.3a-c) for the reader monad (24.16), as equalities
   at every index w. *)
Theorem reader_monad_laws :
  forall (R A B C : Type) (a : A) (m : M (Reader R) A)
         (k : A -> M (Reader R) B) (l : B -> M (Reader R) C) (w : R),
    bind (Reader R) (unit (Reader R) a) k w = k a w /\
    bind (Reader R) m (unit (Reader R) (A:=A)) w = m w /\
    bind (Reader R) (bind (Reader R) m k) l w
      = bind (Reader R) m (fun v => bind (Reader R) (k v) l) w.
Proof. intros; repeat split; reflexivity. Qed.

(* T3.  The three laws (24.3a-c) for the continuation monad (24.19), as
   equalities at every continuation c. *)
Theorem cont_monad_laws :
  forall (O A B C : Type) (a : A) (m : M (Cont O) A)
         (k : A -> M (Cont O) B) (l : B -> M (Cont O) C),
    (forall c, bind (Cont O) (unit (Cont O) a) k c = k a c) /\
    (forall c, bind (Cont O) m (unit (Cont O) (A:=A)) c = m c) /\
    (forall c, bind (Cont O) (bind (Cont O) m k) l c
               = bind (Cont O) m (fun v => bind (Cont O) (k v) l) c).
Proof. intros; repeat split; reflexivity. Qed.

(* ========================================================================== *)
(*  3. Lifted application in each monad                                       *)
(* ========================================================================== *)

(* T4a.  In the powerset monad A_M f x = { a b | a in f, b in x }.
   [Shan (24.9), p. 288]: pointwise function application over alternatives. *)
Lemma AM_set : forall (A B : Type) (f : M SetM (A -> B)) (x : M SetM A) (c : B),
  AM SetM f x c <-> exists a b, f a /\ x b /\ c = a b.
Proof.
  intros A B f x c; cbn; split.
  - intros [a [Hf [b [Hx Hc]]]]; exists a, b; auto.
  - intros [a [b [Hf [Hx Hc]]]]; exists a; split; [exact Hf|].
    exists b; split; assumption.
Qed.

(* T4b.  In the reader monad A_M f x = fun w => f w (x w).  [Shan (24.17),
   p. 289] *)
Lemma AM_reader : forall (R A B : Type) (f : M (Reader R) (A -> B))
                         (x : M (Reader R) A) (w : R),
  AM (Reader R) f x w = f w (x w).
Proof. reflexivity. Qed.

(* T4c.  In the continuation monad
   A_M f x = fun c => f (fun g => x (fun y => c (g y))).  [Shan (24.21), p. 290] *)
Lemma AM_cont : forall (O A B : Type) (f : M (Cont O) (A -> B))
                       (x : M (Cont O) A) (c : B -> O),
  AM (Cont O) f x c = f (fun g => x (fun y => c (g y))).
Proof. reflexivity. Qed.

(* T5.  A'_M f x = A_M f (unit x).  Shan p. 290 states this for every monad
   as a consequence of the laws; it is proved here for the three instances.
   In the reader monad unit is the intension operator [Shan p. 290]. *)
Lemma AM'_set : forall (A B : Type) (f : M SetM (M SetM A -> B))
                       (x : M SetM A) (c : B),
  AM' SetM f x c <-> AM SetM f (unit SetM x) c.
Proof.
  intros A B f x c; cbn; split.
  - intros [a [Hf Hc]]; exists a; split; [exact Hf|].
    exists x; split; [reflexivity | exact Hc].
  - intros [a [Hf [b [-> Hc]]]]; exists a; split; assumption.
Qed.

Lemma AM'_reader : forall (R A B : Type) (f : M (Reader R) (M (Reader R) A -> B))
                          (x : M (Reader R) A) (w : R),
  AM' (Reader R) f x w = AM (Reader R) f (unit (Reader R) x) w.
Proof. reflexivity. Qed.

Lemma AM'_cont : forall (O A B : Type) (f : M (Cont O) (M (Cont O) A -> B))
                        (x : M (Cont O) A) (c : B -> O),
  AM' (Cont O) f x c = AM (Cont O) f (unit (Cont O) x) c.
Proof. reflexivity. Qed.

(* T4.  Lifted application in the three monads: (24.9), (24.17), (24.21). *)
Theorem lifted_application :
  (forall (A B : Type) (f : M SetM (A -> B)) (x : M SetM A) (c : B),
     AM SetM f x c <-> exists a b, f a /\ x b /\ c = a b) /\
  (forall (R A B : Type) (f : M (Reader R) (A -> B)) (x : M (Reader R) A) (w : R),
     AM (Reader R) f x w = f w (x w)) /\
  (forall (O A B : Type) (f : M (Cont O) (A -> B)) (x : M (Cont O) A) (c : B -> O),
     AM (Cont O) f x c = f (fun g => x (fun y => c (g y)))).
Proof. exact (conj AM_set (conj AM_reader AM_cont)). Qed.

(* T5.  The secondary rule in the three monads: A'_M f x = A_M f (unit x). *)
Theorem secondary_rule :
  (forall (A B : Type) (f : M SetM (M SetM A -> B)) (x : M SetM A) (c : B),
     AM' SetM f x c <-> AM SetM f (unit SetM x) c) /\
  (forall (R A B : Type) (f : M (Reader R) (M (Reader R) A -> B))
          (x : M (Reader R) A) (w : R),
     AM' (Reader R) f x w = AM (Reader R) f (unit (Reader R) x) w) /\
  (forall (O A B : Type) (f : M (Cont O) (M (Cont O) A -> B))
          (x : M (Cont O) A) (c : B -> O),
     AM' (Cont O) f x c = AM (Cont O) f (unit (Cont O) x) c).
Proof. exact (conj AM'_set (conj AM'_reader AM'_cont)). Qed.

(* ========================================================================== *)
(*  4. Order of evaluation                                                    *)
(* ========================================================================== *)

(* T6a.  The reader monad is commutative: the order in which two computations
   are bound does not matter.  G&A fn. 6 p. 23 use this to identify readings
   that differ only in that order. *)
Theorem reader_commutative :
  forall (R A B C : Type) (m : M (Reader R) A) (n : M (Reader R) B)
         (k : A -> B -> M (Reader R) C) (w : R),
    bind (Reader R) m (fun a => bind (Reader R) n (fun b => k a b)) w
    = bind (Reader R) n (fun b => bind (Reader R) m (fun a => k a b)) w.
Proof. reflexivity. Qed.

(* T6b.  Transparency of bind (ours; it is what makes G&A's reading (32)
   contradictory): if a and b have the same value at index i, then binding
   either into the same continuation gives the same result at i. *)
Theorem transparent_substitution :
  forall (R A B : Type) (a b : M (Reader R) A) (k : A -> M (Reader R) B) (i : R),
    a i = b i -> bind (Reader R) a k i = bind (Reader R) b k i.
Proof. intros R A B a b k i H; cbn; rewrite H; reflexivity. Qed.

(* ========================================================================== *)
(*  6. Worked model: Shan's examples                                          *)
(* ========================================================================== *)
Module ShanModel.

Inductive E : Type := John | Mary.
Definition dom : list E := [John; Mary].
Definition E_eqb (x y : E) : bool :=
  match x, y with John, John | Mary, Mary => true | _, _ => false end.

(* The non-deterministic individual m1 = {John, Mary}.  [Shan p. 287] *)
Definition m1 : M SetM E := fun x => x = John \/ x = Mary.

(* k1 a = { like a, hate a }.  [Shan p. 287] *)
Definition k1 (like hate : E -> E -> Prop) : E -> M SetM (E -> Prop) :=
  fun a => fun f => f = like a \/ f = hate a.

(* m1 * k1 has exactly the four members Shan lists on p. 287, for any two
   relations like and hate. *)
Example m1_bind_k1 : forall (like hate : E -> E -> Prop) (f : E -> Prop),
  bind SetM m1 (k1 like hate) f
  <-> f = like John \/ f = hate John \/ f = like Mary \/ f = hate Mary.
Proof.
  intros like hate f; cbn; unfold m1, k1; split.
  - intros [a [[-> | ->] [H | H]]]; auto.
  - intros [H | [H | [H | H]]];
      [exists John | exists John | exists Mary | exists Mary]; auto.
Qed.

(* Continuation monad with answer type bool. *)
Definition K := Cont bool.

(* John smokes; Mary does not. *)
Definition smoke (x : E) : bool := E_eqb x John.

(* everyone = fun c => forall x, c x.  [Shan (24.22), p. 291], with the
   universal quantifier computed over the finite domain. *)
Definition everyone : M K E := fun c => forallb c dom.
(* ours: the existential counterpart; Shan gives only "everyone". *)
Definition someone : M K E := fun c => existsb c dom.

(* [[John smokes]] evaluates to smoke(John).  [Shan (24.20) and p. 291] *)
Example john_smokes : forall p : E -> bool,
  eval (AM K (unit K p) (unit K John)) = p John.
Proof. reflexivity. Qed.

Example john_smokes_true : eval (AM K (unit K smoke) (unit K John)) = true.
Proof. reflexivity. Qed.

(* [[everyone smokes]] evaluates to "for all x, smoke x".  [Shan p. 291] *)
Example everyone_smokes : forall p : E -> bool,
  eval (AM K (unit K p) everyone) = forallb p dom.
Proof. reflexivity. Qed.

Example everyone_smokes_false : eval (AM K (unit K smoke) everyone) = false.
Proof. reflexivity. Qed.

(* everyone is not unit of any individual: it uses its continuation
   non-trivially.  [Shan p. 291, remark after (24.22)] *)
Example everyone_not_pure : forall a : E, exists c, everyone c <> unit K a c.
Proof. intros [|]; [exists (fun x => E_eqb x John) | exists (fun x => E_eqb x Mary)];
       discriminate. Qed.

(* --- Two quantifiers: "everyone loves someone" (ours; computed from
   Shan's (24.21); Shan does not discuss a sentence with two quantifiers) --- *)

(* loves s o: s loves o.  In the model each individual loves only itself. *)
Definition loves (s o : E) : bool := E_eqb s o.

(* The transitive verb takes its object first. *)
Definition vp (L : E -> E -> bool) : M K (E -> bool) :=
  AM K (unit K (fun o s => L s o)) someone.

(* With Shan's A_M (function first) the object quantifier takes widest scope. *)
Example fun_first_reading : forall L,
  eval (AM K (vp L) everyone)
  = existsb (fun y => forallb (fun x => L x y) dom) dom.
Proof. reflexivity. Qed.

(* With the argument evaluated first (AMr, ours) the subject takes widest scope. *)
Example arg_first_reading : forall L,
  eval (AMr K (vp L) everyone)
  = forallb (fun x => existsb (fun y => L x y) dom) dom.
Proof. reflexivity. Qed.

(* S1a.  Separating example: on the model the two scope readings differ. *)
Example scope_readings_differ :
  eval (AMr K (vp loves) everyone) = true /\
  eval (AM K (vp loves) everyone) = false.
Proof. split; reflexivity. Qed.

(* S1b.  Separating example: the continuation monad is NOT commutative
   (contrast T6a for the reader monad). *)
Example cont_not_commutative :
  ~ (forall (m n : M K E) (k : E -> E -> M K bool) (c : bool -> bool),
       bind K m (fun a => bind K n (fun b => k a b)) c
       = bind K n (fun b => bind K m (fun a => k a b)) c).
Proof.
  intros H.
  specialize (H everyone someone (fun a b => unit K (loves a b)) (fun x => x)).
  discriminate H.
Qed.

End ShanModel.

(* ========================================================================== *)
(*  7. Worked model: Giorgolo & Asudeh's opacity fragment                     *)
(* ========================================================================== *)
Module OpacityModel.

(* Interpretation indices: the speaker (sigma), Mary Jane, Dr. Octopus.
   [G&A p. 22: "special index sigma"; Table 1 p. 23] *)
Inductive Idx : Type := sigma | i_mj | i_oc.

(* Entities: Peter Parker (speaker's), Spider-Man as Mary Jane and Dr. Octopus
   represent him, Mary Jane, Dr. Octopus.  [G&A Table 1: pp_sigma, sm_i,
   mj_sigma, o_sigma] *)
Inductive Ent : Type := pp | sm | mj | oc.

(* G&A's monad: the reader monad over indices.  [G&A (9), (10), p. 21] *)
Definition GA := Reader Idx.

(* kappa maps an entity to its interpretation index.  [G&A p. 23].  The value
   sigma for entities other than mj and oc is ours (the source is silent). *)
Definition kappa (x : Ent) : Idx :=
  match x with mj => i_mj | oc => i_oc | _ => sigma end.

(* Spider-Man: sm at the indices of Mary Jane and Dr. Octopus, pp at the
   speaker's index.  [G&A Table 1] *)
Definition spiderman : M GA Ent :=
  fun i => match i with sigma => pp | _ => sm end.

(* love = fun o s i => love(s)(o(kappa s)): the object is interpreted from the
   subject's perspective.  [G&A Table 1].  L s o: s loves o. *)
Definition love (L : Ent -> Ent -> bool) (o : M GA Ent) (s : Ent) : M GA bool :=
  fun _ => L s (o (kappa s)).

(* punch = fun o s => punch(s)(o): an ordinary, non-monadic verb.  [G&A Table 1]
   With this entry the term (29), which applies punch to Dr. Octopus first,
   makes Dr. Octopus the object; this file follows the term as printed.  The
   order of the arguments does not affect the contradiction proved in T8c. *)
Definition punch (P : Ent -> Ent -> bool) (o s : Ent) : bool := P s o.

(* Reading (29) of "Dr. Octopus punched Spider-Man but he didn't punch
   Spider-Man" [G&A (2); term (29), p. 24], entered as printed. *)
Definition reading29 (P : Ent -> Ent -> bool) : M GA bool :=
  bind GA spiderman (fun x => bind GA spiderman (fun y =>
    unit GA (andb (punch P oc x) (negb (punch P oc y))))).

(* Readings (31) and (32) of "Mary Jane loves Peter Parker but she doesn't
   love Spider-Man" [G&A (3); Fig. 3, p. 25]. *)
Definition reading31 (L : Ent -> Ent -> bool) : M GA bool :=
  bind GA (love L (unit GA pp) mj) (fun p =>
  bind GA (love L spiderman mj) (fun q => unit GA (andb p (negb q)))).

Definition reading32 (L : Ent -> Ent -> bool) : M GA bool :=
  bind GA (love L (unit GA pp) mj) (fun p =>
  bind GA spiderman (fun x =>
  bind GA (love L (unit GA x) mj) (fun q => unit GA (andb p (negb q))))).

(* T8a.  Reading (31) has the truth conditions (33): Mary Jane loves pp and
   does not love the entity she calls Spider-Man.  [G&A (33), p. 24] *)
Lemma reading31_truth_conditions : forall L i,
  reading31 L i = andb (L mj pp) (negb (L mj sm)).
Proof. reflexivity. Qed.

(* T8b.  Reading (32), evaluated at the speaker's index, has the unsatisfiable
   truth conditions (34), whatever the love relation.  [G&A (34), p. 24] *)
Lemma reading32_contradictory : forall L,
  reading32 L sigma = andb (L mj pp) (negb (L mj pp)) /\
  reading32 L sigma = false.
Proof. intros L; split; [reflexivity|]; cbn; apply andb_negb_r. Qed.

(* T8c.  Reading (29) is false at every index, whatever the punch relation:
   sentence (2) has only a contradictory reading.  [G&A (30), p. 24] *)
Lemma reading29_contradictory : forall P i, reading29 P i = false.
Proof. intros P i; cbn; apply andb_negb_r. Qed.

(* T8.  The three readings together: (33), (34) and (30) of G&A. *)
Theorem opacity_readings : forall (L P : Ent -> Ent -> bool),
  (forall i, reading31 L i = andb (L mj pp) (negb (L mj sm))) /\
  reading32 L sigma = false /\
  (forall i, reading29 P i = false).
Proof.
  intros L P. split; [intros i; apply reading31_truth_conditions|].
  split; [exact (proj2 (reading32_contradictory L)) | intros i; apply reading29_contradictory].
Qed.

(* The model: Mary Jane loves Peter Parker and nobody else; nobody loves
   anybody otherwise. *)
Definition L0 (s o : Ent) : bool :=
  match s, o with mj, pp => true | _, _ => false end.

(* Computed results: (31) is true and (32) is false on the model. *)
Example reading31_true : reading31 L0 sigma = true.
Proof. reflexivity. Qed.
Example reading32_false : reading32 L0 sigma = false.
Proof. reflexivity. Qed.

(* The two names co-refer for the speaker. *)
Example coreferring_at_sigma : spiderman sigma = unit GA pp sigma.
Proof. reflexivity. Qed.

(* Substitution holds OUTSIDE the scope of love: bound from outside (as in
   (32)), Spider-Man can be replaced by Peter Parker.  Instance of T6b. *)
Example substitution_holds_outside : forall L,
  bind GA spiderman (fun x => love L (unit GA x) mj) sigma
  = bind GA (unit GA pp) (fun x => love L (unit GA x) mj) sigma.
Proof. intros L; apply transparent_substitution; reflexivity. Qed.

(* S2.  Separating example: substitution FAILS inside the argument of love.
   Co-reference at the speaker's index does not license replacing one term
   by the other under an arbitrary function on monadic values. *)
Example substitution_fails_under_love :
  ~ (forall (a b : M GA Ent) (F : M GA Ent -> M GA bool) (i : Idx),
       a i = b i -> F a i = F b i).
Proof.
  intros H.
  specialize (H spiderman (unit GA pp) (fun o => love L0 o mj) sigma eq_refl).
  discriminate H.
Qed.

End OpacityModel.

(* ========================================================================== *)
(*  Assumption audit                                                          *)
(* ========================================================================== *)
(* Every line below is expected to print "Closed under the global context". *)
Print Assumptions set_monad_laws.
Print Assumptions reader_monad_laws.
Print Assumptions cont_monad_laws.
Print Assumptions lifted_application.
Print Assumptions secondary_rule.
Print Assumptions AM_set.
Print Assumptions AM_reader.
Print Assumptions AM_cont.
Print Assumptions AM'_set.
Print Assumptions AM'_reader.
Print Assumptions AM'_cont.
Print Assumptions reader_commutative.
Print Assumptions transparent_substitution.
Print Assumptions ShanModel.m1_bind_k1.
Print Assumptions ShanModel.john_smokes.
Print Assumptions ShanModel.john_smokes_true.
Print Assumptions ShanModel.everyone_smokes.
Print Assumptions ShanModel.everyone_smokes_false.
Print Assumptions ShanModel.everyone_not_pure.
Print Assumptions ShanModel.fun_first_reading.
Print Assumptions ShanModel.arg_first_reading.
Print Assumptions ShanModel.scope_readings_differ.
Print Assumptions ShanModel.cont_not_commutative.
Print Assumptions OpacityModel.opacity_readings.
Print Assumptions OpacityModel.reading31_truth_conditions.
Print Assumptions OpacityModel.reading32_contradictory.
Print Assumptions OpacityModel.reading29_contradictory.
Print Assumptions OpacityModel.reading31_true.
Print Assumptions OpacityModel.reading32_false.
Print Assumptions OpacityModel.coreferring_at_sigma.
Print Assumptions OpacityModel.substitution_holds_outside.
Print Assumptions OpacityModel.substitution_fails_under_love.
