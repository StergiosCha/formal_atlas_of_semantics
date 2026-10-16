(* Appendix A1.2's Leibniz equality as a defined object formula. This does
   not add an equality, eta or extensionality rule to the object calculus. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Syntax Models BooleanModels BooleanFinite.
Import ListNotations.
Set Implicit Arguments.

Definition leibniz_equal {symbol G a} (u v : tm symbol G a) : tm symbol G truth :=
  All (Imp (App (Var vz) (weaken u)) (App (Var vz) (weaken v))).

Theorem boolean_leibniz_predicates (FE : FunExt) : forall symbol (M : bmodel symbol)
  G a (u v : tm symbol G a) rho,
  beval M (leibniz_equal u v) rho = true <->
  forall P : bdomain (bindividuals M) a -> bool,
    P (beval M u rho) = true -> P (beval M v rho) = true.
Proof.
  intros; unfold leibniz_equal; cbn -[weaken bforall].
  rewrite bforall_spec; split; intros H P.
  - specialize (H P); rewrite !(beval_weaken (M:=M) FE) in H.
    exact (proj1 (bimp_spec _ _) H).
  - rewrite !(beval_weaken (M:=M) FE); apply bimp_spec; apply H.
Qed.

Theorem boolean_leibniz_equality (FE : FunExt) : forall symbol (M : bmodel symbol)
  G a (u v : tm symbol G a) rho,
  (forall x y : bdomain (bindividuals M) a, {x = y} + {x <> y}) ->
  (beval M (leibniz_equal u v) rho = true <-> beval M u rho = beval M v rho).
Proof.
  intros symbol M G a u v rho Eq; rewrite boolean_leibniz_predicates by exact FE.
  split.
  - intro H.
    specialize (H (fun z => if Eq (beval M u rho) z then true else false)).
    assert (Self : (if Eq (beval M u rho) (beval M u rho) then true else false) = true).
    { destruct (Eq (beval M u rho) (beval M u rho)); [reflexivity | contradiction]. }
    specialize (H Self); cbn in H.
    destruct (Eq (beval M u rho) (beval M v rho)); [assumption | discriminate].
  - intros E P; rewrite E; auto.
Qed.

Theorem finite_leibniz_equality : forall symbol E (FE : FunExt) (F : finite E)
  (lex : forall a, symbol a -> bdomain E a) G a (u v : tm symbol G a) rho,
  beval (finite_model FE F lex) (leibniz_equal u v) rho = true <->
  beval (finite_model FE F lex) u rho = beval (finite_model FE F lex) v rho.
Proof.
  intros; apply boolean_leibniz_equality; [exact FE |].
  exact (value_eq (finite_domain FE F a)).
Qed.

(* Here ClassicalDecision, not merely a hidden reference to a classical
   truth domain, supplies the equality-testing predicate at arbitrary types. *)
Theorem decision_leibniz_equality (FE : FunExt) (CD : ClassicalDecision) :
  forall symbol (M : bmodel symbol) G a (u v : tm symbol G a) rho,
  beval M (leibniz_equal u v) rho = true <-> beval M u rho = beval M v rho.
Proof. intros; apply boolean_leibniz_equality; [exact FE | intros x y; apply CD]. Qed.
