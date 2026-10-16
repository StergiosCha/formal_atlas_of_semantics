(* Proof-to-proof interpretation of every implemented IL derivation.
   Only the existing Ty2 axiom and replacement constructors are used.
   There is no semantic oracle, completeness axiom, or enlarged calculus. *)
From Coq Require Import List.
From MontaguePTQ Require Import Syntax.
From MontagueGallin Require Import Types Target Translation Minimal Substitution Calculus
  SyntaxAlgebra Untensed ILCore ILCalculus ILCompileSyntax ILProofTranslation.
Import ListNotations.
Set Implicit Arguments.
Local Notation C := (ctm source_symbol source_parameter).

Definition derive_application_equality {S P G a b} (f g : ctm S P G (garr a b))
  (x y : ctm S P G a) (HF : Derivation (CEq f g)) (HX : Derivation (CEq x y)) :
  Derivation (CEq (CApp f x) (CApp g y)) :=
  derive_transitivity (derive_context_congruence (AppFunction Hole x) HF)
    (derive_context_congruence (AppArgument g Hole) HX).
Definition derive_equality_equality {S P G a} (p q x y : ctm S P G a)
  (HP : Derivation (CEq p q)) (HX : Derivation (CEq x y)) :
  Derivation (CEq (CEq p x) (CEq q y)) :=
  derive_transitivity (derive_context_congruence (EqLeft Hole x) HP)
    (derive_context_congruence (EqRight q Hole) HX).

Definition compiled_beta G a b (p : ltm (a :: G) b) (q : ltm G a)
  D (r : lvalues G D) i :
  Derivation (CEq (lcompile (LApp (LLam p) q) r i)
    (lcompile p (lbind r (lcompile q r i)) i)).
Proof.
  pose proof (ByAxiom (AS4 (lcompile p (llift r) (cweaken i)) (lcompile q r i))) as H.
  unfold axiom4 in H; rewrite lcompile_beta in H; exact H.
Defined.

Lemma lcompile_lift_variables G D a b (p : ltm (a :: G) b) (r : variable_map G D) i :
  lcompile p (llift (variable_values r)) i = lcompile p (variable_values (lift_map r)) i.
Proof. apply lcompile_ext; apply var_cases; cbn; reflexivity. Qed.
Lemma lcompile_shift_variables G D a b (p : ltm G b) (r : variable_map G D) i :
  lcompile p (@lshift G D a (variable_values r)) i = lcompile p (variable_values (shift_map r)) i.
Proof. apply lcompile_ext; intros; reflexivity. Qed.

Lemma compiled_axiom_one G (g : ltm G (arr t t)) D (r : lvalues G D) i :
  lcompile (il_axiom1 g) r i = axiom1 (lcompile g r i).
Proof.
  cbn [il_axiom1 lcompile axiom1]; rewrite lcompile_and, lcompile_all.
  cbn [lcompile]; rewrite lcompile_true, lcompile_false, lcompile_weaken_under_binder; reflexivity.
Qed.
Lemma compiled_axiom_two G a (x y : ltm G a) (f : ltm G (arr a t)) D (r : lvalues G D) i :
  lcompile (il_axiom2 x y f) r i = axiom2 (lcompile x r i) (lcompile y r i) (lcompile f r i).
Proof. unfold il_axiom2, axiom2; rewrite lcompile_imp; reflexivity. Qed.
Lemma compiled_axiom_three G a b (f g : ltm G (arr a b)) D (r : lvalues G D) i :
  lcompile (il_axiom3 f g) r i = axiom3 (lcompile f r i) (lcompile g r i).
Proof.
  cbn [il_axiom3 lcompile axiom3]; rewrite lcompile_all; cbn [lcompile].
  rewrite !lcompile_weaken_under_binder; reflexivity.
Qed.
Definition compiled_variable G D a (r : variable_map G D) (v : il_axiom_variable G a) :
  axiom_variable source_parameter D (translate_type a) :=
  match v with ILContextVariable w => ContextVariable (r _ w)
  | ILNamedVariable n => ParameterVariable (SourceFree _ n) end.
Lemma compiled_variable_term G D a (r : variable_map G D) (v : il_axiom_variable G a) i :
  lcompile (il_variable_term v) (variable_values r) i = variable_term (compiled_variable r v).
Proof. destruct v; reflexivity. Qed.
Lemma compiled_axiom_five G D a (r : variable_map G D) (f g : il_axiom_variable G (intens a)) i :
  lcompile (il_axiom5 (il_variable_term f) (il_variable_term g)) (variable_values r) i =
  axiom3 (variable_term (compiled_variable r f)) (variable_term (compiled_variable r g)).
Proof. destruct f, g; reflexivity. Qed.

Definition compile_all_axioms G (p : ltm G t) (H : ILAxiom p) :
  forall D (r : variable_map G D) i, Derivation (lcompile p (variable_values r) i).
Proof.
  destruct H; intros D rr i.
  - rewrite compiled_axiom_one, compiled_variable_term.
    exact (ByAxiom (A1 (compiled_variable rr g))).
  - rewrite compiled_axiom_two, !compiled_variable_term.
    exact (ByAxiom (A2 (compiled_variable rr x) (compiled_variable rr y) (compiled_variable rr f))).
  - rewrite compiled_axiom_three, !compiled_variable_term.
    exact (ByAxiom (A3 (compiled_variable rr f) (compiled_variable rr g))).
  - pose proof (compiled_beta (lweaken p) q (variable_values rr) i) as H.
    rewrite lcompile_source_weaken in H; exact H.
  - exact (ByAxiom (AS4 (CVar gz) (lcompile q (variable_values rr) i))).
  - exact (derive_transitivity (compiled_beta (LApp p r) q (variable_values rr) i)
      (derive_symmetry (derive_application_equality (compiled_beta p q (variable_values rr) i)
        (compiled_beta r q (variable_values rr) i)))).
  - exact (derive_transitivity (compiled_beta (LEq p r) q (variable_values rr) i)
      (derive_symmetry (derive_equality_equality (compiled_beta p q (variable_values rr) i)
        (compiled_beta r q (variable_values rr) i)))).
  - pose proof (compiled_beta (LLam p) q (variable_values rr) i) as HL.
    pose proof (compiled_beta (lrename p lswap) (lweaken q) (llift (variable_values rr)) (cweaken i)) as HR.
    rewrite lcompile_weaken_under_binder, lcompile_swap_beta in HR.
    exact (derive_transitivity HL
      (derive_symmetry (derive_context_congruence (LambdaBody Hole) HR))).
  - exact (derive_transitivity (compiled_beta (LDown p) q (variable_values rr) i)
      (derive_symmetry (derive_context_congruence (AppFunction Hole i)
        (compiled_beta p q (variable_values rr) i)))).
  - pose proof (compiled_beta (LUp p) q (variable_values rr) i) as HL.
    pose proof (compiled_beta p q (lshift (variable_values rr)) (CVar gz)) as HR.
    assert (EQ : lcompile p (lbind (lshift (variable_values rr))
        (lcompile q (lshift (variable_values rr)) (CVar gz))) (CVar gz) =
      lcompile p (lshift (lbind (variable_values rr) (lcompile q (variable_values rr) i))) (CVar gz)).
    { apply lcompile_ext; apply var_cases; cbn.
      - change (lcompile q (lshift (variable_values rr)) (CVar gz) =
          cweaken (lcompile q (variable_values rr) i)).
        rewrite lcompile_weaken; apply lcompile_modal_closed; exact m.
      - intros; reflexivity. }
    rewrite EQ in HR.
    exact (derive_transitivity HL
      (derive_symmetry (derive_context_congruence (LambdaBody Hole) HR))).
  - rewrite compiled_axiom_five.
    exact (ByAxiom (A3 (compiled_variable rr f) (compiled_variable rr g))).
  - pose proof (ByAxiom (AS4 (lcompile p (lshift (variable_values rr)) (CVar gz)) i)) as H.
    unfold axiom4 in H; rewrite lcompile_index_beta in H; exact H.
Defined.

Definition compile_il_general G (p : ltm G t) (H : ILDerivation p) :
  forall D (r : variable_map G D) i, Derivation (lcompile p (variable_values r) i).
Proof.
  induction H; intros D rr idx.
  - exact (compile_all_axioms i rr idx).
  - exact (ByReplacement Hole (IHILDerivation1 D rr idx) (IHILDerivation2 D rr idx)).
  - exact (derive_context_congruence (AppFunction Hole (lcompile r (variable_values rr) idx))
      (IHILDerivation D rr idx)).
  - exact (derive_context_congruence (AppArgument (lcompile r (variable_values rr) idx) Hole)
      (IHILDerivation D rr idx)).
  - cbn [lcompile]; rewrite !lcompile_lift_variables.
    exact (derive_context_congruence (LambdaBody Hole)
      (IHILDerivation _ (lift_map rr) (cweaken idx))).
  - cbn [lcompile]; rewrite !lcompile_shift_variables.
    exact (derive_context_congruence (LambdaBody Hole)
      (IHILDerivation _ (shift_map rr) (CVar gz))).
  - exact (derive_context_congruence (AppFunction Hole idx) (IHILDerivation D rr idx)).
  - exact (derive_context_congruence (EqRight (lcompile r (variable_values rr) idx) Hole)
      (IHILDerivation D rr idx)).
  - exact (derive_context_congruence (EqLeft Hole (lcompile r (variable_values rr) idx))
      (IHILDerivation D rr idx)).
Defined.

(* The public result uses exactly checkpoint 6's il_at, not a replacement
   translation or an extended target proof datatype. *)
Definition compile_il_proof G (p : ltm G t) (H : ILDerivation p) : Derivation (il_at p).
Proof.
  unfold il_at; rewrite <- lcompile_agrees_with_existing.
  exact (compile_il_general H (shift_map (@canonical_map G)) (CVar gz)).
Defined.

Lemma il_at_implication G (p q : ltm G t) : il_at (limp p q) = cimp (il_at p) (il_at q).
Proof.
  unfold il_at; rewrite <- !lcompile_agrees_with_existing; apply lcompile_imp.
Qed.
