(* PTQ T1-T17, pp. 25-27, with capture avoidance for T3 (note 12).
   The recursion is total over all typed analysis trees. There are no fallback
   meanings. Syntactic variable names are replaced by fresh de Bruijn binders. *)
From Coq Require Import List Bool Arith.
From MontaguePTQ Require Import Syntax Models Grammar.
Import ListNotations.
Set Implicit Arguments.

Definition pronouns G := nat -> tm G ic.
Definition shift {G a} (r : pronouns G) : pronouns (a :: G) := fun n => weaken (r n).
Definition bind {G} (r : pronouns G) (n : nat) : pronouns (ic :: G) :=
  fun m => if Nat.eqb m n then Var vz else weaken (r m).
Definition join {G} (j : junction) (p q : tm G t) : tm G t :=
  match j with conjunction => And p q | disjunction => Or p q end.
Definition sign {G} (k : tense_sign) (p : tm G t) : tm G t :=
  match k with negative => Neg p | future => Will p | negative_future => Neg (Will p)
  | perfect => Has p | negative_perfect => Neg (Has p) end.

Definition translate_name {G} (n : proper_name) : tm G npty :=
  Lam (App (Down (Var vz)) (Up (@Con _ e (name_code n)))).
Definition translate_be {G} : tm G (category_type TV) :=
  Lam (Lam (App (Down (Var (vs vz)))
    (Up (Lam (Eq (Down (Var (vs vz))) (Down (Var vz))))))).
Definition translate_necessarily {G} : tm G (category_type (slash ct ct)) :=
  Lam (Box (Down (Var vz))).

Definition translate_determiner {G} (d : determiner) (c : tm G ivty) : tm G npty :=
  match d with
  | every => Lam (All (Imp (App (weaken (weaken c)) (Var vz))
      (App (Down (Var (vs vz))) (Var vz))))
  | a_or_an => Lam (Ex (And (App (weaken (weaken c)) (Var vz))
      (App (Down (Var (vs vz))) (Var vz))))
  | the => Lam (Ex (And
      (All (Iff (App (weaken (weaken (weaken c))) (Var vz)) (Eq (Var vz) (Var (vs vz)))))
      (App (Down (Var (vs vz))) (Var vz))))
  end.

Fixpoint translate {A} (u : tree A) : forall G, pronouns G -> tm G (category_type A) :=
  match u in tree A' return forall G, pronouns G -> tm G (category_type A') with
  | s1_word w => fun G _ => Con (lexical_code w)
  | s1_name n => fun G _ => translate_name n
  | s1_pronoun n => fun G r => Lam (App (Down (Var vz)) (weaken (r n)))
  | s1_be => fun G _ => translate_be
  | s1_necessarily => fun G _ => translate_necessarily
  | s2 d c => fun G r => translate_determiner d (translate c r)
  | s3 c n p => fun G r => Lam (And
      (App (weaken (translate c r)) (Var vz)) (translate p (bind r n)))
  | s4 p q => fun G r => App (translate p r) (Up (translate q r))
  | s5 p q => fun G r => App (translate p r) (Up (translate q r))
  | s6 p q => fun G r => App (translate p r) (Up (translate q r))
  | s7 p q => fun G r => App (translate p r) (Up (translate q r))
  | s8 p q => fun G r => App (translate p r) (Up (translate q r))
  | s9 p q => fun G r => App (translate p r) (Up (translate q r))
  | s10 p q => fun G r => App (translate p r) (Up (translate q r))
  | s11 j p q => fun G r => join j (translate p r) (translate q r)
  | s12 j p q => fun G r => Lam (join j
      (App (weaken (translate p r)) (Var vz)) (App (weaken (translate q r)) (Var vz)))
  | s13 p q => fun G r => Lam (Or
      (App (weaken (translate p r)) (Var vz)) (App (weaken (translate q r)) (Var vz)))
  | s14 p n q => fun G r => App (translate p r) (Up (Lam (translate q (bind r n))))
  | s15 p n q => fun G r => Lam (App (translate p (shift r))
      (Up (Lam (App (translate q (bind (shift r) n)) (Var (vs vz))))))
  | s16 p n q => fun G r => Lam (App (translate p (shift r))
      (Up (Lam (App (translate q (bind (shift r) n)) (Var (vs vz))))))
  | s17 k p q => fun G r => sign k (App (translate p r) (Up (translate q r)))
  end.
Definition initial_pronouns : pronouns [] := fun n => Free (2 * n).
Definition translate_closed {A} (u : tree A) : tm [] (category_type A) :=
  translate u initial_pronouns.

Example two_unicorn_analyses_are_different :
  translate_closed seeks_unicorn_dicto <> translate_closed seeks_unicorn_re.
Proof. discriminate. Qed.

Theorem bill_walks_interpretation M sigma i :
  eval M (translate_closed bill_walks) (empty_env M) sigma i =
  constants M ivty (lexical_code (liv walk)) i
    (fun j => constants M e (name_code bill) j).
Proof. reflexivity. Qed.

Theorem pronoun_binding_hits M G (r : pronouns G) rho sigma x n i :
  eval M (bind r n n) (extend rho x) sigma i = x.
Proof. unfold bind; rewrite Nat.eqb_refl; reflexivity. Qed.
Theorem pronoun_binding_misses M G (r : pronouns G) rho sigma x n m i :
  m <> n -> eval M (bind r n m) (extend rho x) sigma i = eval M (r m) rho sigma i.
Proof. intro H; unfold bind; apply Nat.eqb_neq in H; rewrite H; apply eval_weaken. Qed.

Theorem relative_clause_interpretation M G (c : tree CN) n (p : tree ct)
  (r : pronouns G) rho sigma i x :
  eval M (translate (s3 c n p) r) rho sigma i x =
  andb (eval M (translate c r) rho sigma i x)
    (eval M (translate p (bind r n)) (@extend M G ic rho x) sigma i).
Proof. cbn; rewrite eval_weaken; reflexivity. Qed.

Theorem quantifying_in_interpretation M G (p : tree NP) n (q : tree ct)
  (r : pronouns G) rho sigma i :
  eval M (translate (s14 p n q) r) rho sigma i =
  eval M (translate p r) rho sigma i
    (fun j x => eval M (translate q (bind r n)) (@extend M G ic rho x) sigma j).
Proof. reflexivity. Qed.
