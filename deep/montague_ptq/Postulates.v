(* PTQ p. 28: the nine meaning-postulate families as conditions on models.
   These are predicates, not globally asserted facts. Quantifier order and
   restrictions to the named lexical subclasses are retained. *)
From Coq Require Import List Bool Arith.
From MontaguePTQ Require Import Syntax Models Grammar Translation Meaning.
Import ListNotations.
Set Implicit Arguments.

Definition word_value M A (w : lexeme A) := constants M (category_type A) (lexical_code w).
Arguments word_value M {A} w _.
Definition ordinary_cn c := match c with price | temperature => False | _ => True end.
Definition ordinary_iv v := match v with rise | change => False | _ => True end.
Definition extensional_tv v := match v with seek | conceive => False | _ => True end.
Definition intensional_tv v := match v with seek | conceive => True | _ => False end.

Definition mp1 M := forall n, exists u : entity (carrier M),
  forall i, constants M e (name_code n) i = u.
Definition mp2 M := forall c, ordinary_cn c -> forall i (x : domain (carrier M) ic),
  word_value M (lcn c) i x = true -> exists u, x = (fun _ => u).
Definition mp3 M := forall v, ordinary_iv v ->
  exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x i, word_value M (liv v) i x = P i (x i).
Definition mp4 M := forall v, extensional_tv v ->
  exists S : index (carrier M) -> entity (carrier M) -> entity (carrier M) -> bool,
  forall x Q i, word_value M (ltv v) i Q x = Q i (fun j y => S j (x j) (y j)).
Definition mp5 M := forall v, intensional_tv v -> forall Q,
  exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x i, word_value M (ltv v) i Q x = P i (x i).
Definition mp6 M := forall v p,
  exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x i, word_value M (latt v) i p x = P i (x i).
Definition mp7 M := forall v Q,
  exists P : index (carrier M) -> entity (carrier M) -> bool,
  forall x i, word_value M (lcontrol v) i Q x = P i (x i).
Definition mp8 M :=
  exists G : index (carrier M) -> entity (carrier M) -> domain (carrier M) (category_type IAV),
  forall Q R x i, word_value M (lprep in_) i Q R x =
    Q i (fun j y => G j (y j) R x).
Definition mp9 M := forall x Q i,
  word_value M (ltv seek) i Q x =
  word_value M (lcontrol try_to) i (fun j => word_value M (ltv find) j Q) x.

Record admissible (M : model) : Prop := {
  postulate1 : mp1 M; postulate2 : mp2 M; postulate3 : mp3 M;
  postulate4 : mp4 M; postulate5 : mp5 M; postulate6 : mp6 M;
  postulate7 : mp7 M; postulate8 : mp8 M; postulate9 : mp9 M
}.

Definition logically_true (p : tm [] t) := forall M, admissible M ->
  forall sigma i, eval M p (empty_env M) sigma i = true.
Definition english_consequence (premises : list (tree ct)) (conclusion : tree ct) :=
  forall M, admissible M -> forall r i,
  (forall p, In p premises -> denote M p r i = true) -> denote M conclusion r i = true.

Lemma boolean_implication p q : orb (negb p) q = true <-> (p = true -> q = true).
Proof. destruct p, q; cbn; intuition discriminate. Qed.

Theorem every_man_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed every_man_walks) (empty_env M) sigma i = true <->
  forall u : entity (carrier M),
    word_value M (lcn man) i (fun _ => u) = true ->
    word_value M (liv walk) i (fun _ => u) = true.
Proof.
  rewrite closed_translation_interpretation.
  cbn [every_man_walks denote dvalue]; rewrite truth_spec.
  split.
  - intros H u; apply (proj1 (boolean_implication _ _) (H (fun _ => u))).
  - intros H x; apply boolean_implication; intro C.
    destruct (postulate2 A man I i x C) as [u E]; subst x; apply H; exact C.
Qed.

Theorem a_man_source_reduction M (A : admissible M) sigma i :
  eval M (translate_closed a_man_walks) (empty_env M) sigma i = true <->
  exists u : entity (carrier M),
    word_value M (lcn man) i (fun _ => u) = true /\
    word_value M (liv walk) i (fun _ => u) = true.
Proof.
  rewrite closed_translation_interpretation.
  cbn [a_man_walks denote dvalue]; rewrite truth_spec.
  split.
  - intros [x H]; apply andb_true_iff in H; destruct H as [C V].
    destruct (postulate2 A man I i x C) as [u E]; subst x; exists u; auto.
  - intros [u [C V]]; exists (fun _ => u); apply andb_true_iff; auto.
Qed.

Theorem proper_name_rigidity_is_a_condition M (A : admissible M) n i j :
  constants M e (name_code n) i = constants M e (name_code n) j.
Proof. destruct (postulate1 A n) as [u H]; rewrite !H; reflexivity. Qed.

Theorem compiled_english_consequence premises conclusion :
  english_consequence premises conclusion -> forall M, admissible M -> forall sigma i,
  (forall p, In p premises -> eval M (translate_closed p) (empty_env M) sigma i = true) ->
  eval M (translate_closed conclusion) (empty_env M) sigma i = true.
Proof.
  intros H M A sigma i P; rewrite closed_translation_interpretation.
  apply (H M A); intros p Hp; rewrite <- closed_translation_interpretation; apply P; exact Hp.
Qed.
