(* A first proof-to-proof compiler. Its input is an explicit fragment of
   IL proof trees, NOT arbitrary semantic truth and NOT all of ILDerivation.
   Terms may contain any primitive IL operation; inference under lambda or
   Up and the other axiom families are not yet in this proof fragment. *)
From Coq Require Import List Bool.
From MontaguePTQ Require Import Syntax Models.
From MontagueGallin Require Import Types Target Translation Minimal Substitution Calculus
  Untensed UntensedModels ILCore ILCalculus ILCalculusExamples.
Import ListNotations.
Set Implicit Arguments.

Definition il_at {G a} (p : ltm G a) : ctm source_symbol source_parameter
    (gs :: map translate_type G) (translate_type a) :=
  eliminate (compile (embed_il (include_il p)) (shift_map (@canonical_map G)) (GVar gz)).
Theorem il_at_is_existing_translation_body G a (p : ltm G a) :
  il_minimal_translate (include_il p) = CLam (il_at p).
Proof. reflexivity. Qed.

(* Each constructor has an erasure to a genuine source IL derivation.
   There is intentionally no constructor taking an arbitrary ILDerivation. *)
Inductive ILPointwiseProof : forall G, ltm G t -> Type :=
| IPRefl : forall G a (p : ltm G a), ILPointwiseProof (LEq p p)
| IPBetaIdentity : forall G a (q : ltm G a),
    ILPointwiseProof (LEq (LApp (LLam (LVar vz)) q) q)
| IPEqualityElim : forall G (p q : ltm G t),
    ILPointwiseProof (LEq p q) -> ILPointwiseProof p -> ILPointwiseProof q
| IPAppFunction : forall G a b (p q : ltm G (arr a b)) (r : ltm G a),
    ILPointwiseProof (LEq p q) -> ILPointwiseProof (LEq (LApp p r) (LApp q r))
| IPAppArgument : forall G a b (p q : ltm G a) (r : ltm G (arr a b)),
    ILPointwiseProof (LEq p q) -> ILPointwiseProof (LEq (LApp r p) (LApp r q))
| IPDown : forall G a (p q : ltm G (intens a)),
    ILPointwiseProof (LEq p q) -> ILPointwiseProof (LEq (LDown p) (LDown q))
| IPEqLeft : forall G a (p q r : ltm G a),
    ILPointwiseProof (LEq p q) -> ILPointwiseProof (LEq (LEq p r) (LEq q r))
| IPEqRight : forall G a (p q r : ltm G a),
    ILPointwiseProof (LEq p q) -> ILPointwiseProof (LEq (LEq r p) (LEq r q)).

Definition pointwise_proof_is_source_derivation G p (H : @ILPointwiseProof G p) : ILDerivation p.
Proof.
  induction H.
  - apply il_derive_reflexivity.
  - exact (ILByAxiom (IL_AS42 q)).
  - exact (IL_R1 IHILPointwiseProof1 IHILPointwiseProof2).
  - exact (IL_R2 r IHILPointwiseProof).
  - exact (IL_R3 r IHILPointwiseProof).
  - exact (IL_R6 IHILPointwiseProof).
  - exact (IL_R8 r IHILPointwiseProof).
  - exact (IL_R7 r IHILPointwiseProof).
Defined.

(* This constructs target proof trees using Ty2 AS4 and R. Soundness,
   completeness, model evaluation and BooleanTruth are not inputs. *)
Definition compile_pointwise_proof G p (H : @ILPointwiseProof G p) : Derivation (il_at p).
Proof.
  induction H.
  - exact (derive_reflexivity (il_at p)).
  - exact (ByAxiom (AS4 (CVar gz) (il_at q))).
  - exact (ByReplacement Hole IHILPointwiseProof1 IHILPointwiseProof2).
  - exact (derive_context_congruence (AppFunction Hole (il_at r)) IHILPointwiseProof).
  - exact (derive_context_congruence (AppArgument (il_at r) Hole) IHILPointwiseProof).
  - exact (derive_context_congruence (AppFunction Hole (CVar gz)) IHILPointwiseProof).
  - exact (derive_context_congruence (EqLeft Hole (il_at r)) IHILPointwiseProof).
  - exact (derive_context_congruence (EqRight (il_at r) Hole) IHILPointwiseProof).
Defined.

Definition pointwise_beta_example : ILPointwiseProof
  (LEq (LDown (LApp (LLam (LVar vz)) (@LUp [] t (LCon 0)))) (LDown (LUp (LCon 0)))) :=
  IPDown (IPBetaIdentity (LUp (LCon 0))).
Definition compiled_pointwise_beta_example : Derivation
  (il_at (LEq (LDown (LApp (LLam (LVar vz)) (@LUp [] t (LCon 0)))) (LDown (LUp (LCon 0))))) :=
  compile_pointwise_proof pointwise_beta_example.
