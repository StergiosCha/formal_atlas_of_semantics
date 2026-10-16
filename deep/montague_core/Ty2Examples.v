(* Two-world fixtures. Familiar modal distinctions, not novelty claims or
   a source-faithfulness certificate for an English lexical analysis. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Syntax Models Calculus Examples BooleanModels
  BooleanFinite Ty2Syntax Ty2Models Ty2Calculus Ty2Embedding.
Import ListNotations.
Set Implicit Arguments.

Inductive world_word : wty -> Type :=
| CoreWord : forall a, word a -> world_word (embed_type a)
| Actual : world_word ws
| Alternative : world_word ws
| Weather : world_word (warr ws wt)
| PersonConcept : world_word (warr ws we)
| Distinguished : world_word (warr we wt).

Definition core_words {a} (c : word a) := @CoreWord a c.
Definition small_core_lex a (c : word a) : bdomain bool a :=
  match c in word a return bdomain bool a with
  | John => true | Man => fun x => x | Walk => fun _ => true | Move => fun _ => true
  end.
Definition two_worlds (FE : FunExt) : wmodel world_word :=
  world_finite_model FE finite_bool finite_bool
    (fun a c => match c in world_word a return wdomain bool bool a with
    | @CoreWord a c => lift_value a (@small_core_lex a c)
    | Actual => true | Alternative => false
    | Weather => fun w => w
    | PersonConcept => fun w => w
    | Distinguished => fun x => x
    end).

Definition wempty_env {symbol} (M : wmodel symbol) : wenv M [] :=
  fun a v => match v in wvar G a return
    match G with [] => wdomain (windividuals M) (worlds M) a | _ :: _ => unit end
    with wz => tt | wvs _ => tt end.

Definition actual {G} : wtm world_word G ws := WConst Actual.
Definition alternative {G} : wtm world_word G ws := WConst Alternative.
Definition weather {G} : wtm world_word G (warr ws wt) := WConst Weather.
Definition person_concept {G} : wtm world_word G (warr ws we) := WConst PersonConcept.
Definition wjohn {G} : wtm world_word G we := WConst (CoreWord John).
Definition distinguished {G} : wtm world_word G (warr we wt) := WConst Distinguished.

Example world_sensitive_truth (FE : FunExt) :
  weval (two_worlds FE) (at_world (@weather []) actual) (wempty_env _) = true /\
  weval (two_worlds FE) (at_world (@weather []) alternative) (wempty_env _) = false.
Proof. split; reflexivity. Qed.

Example actual_truth_is_not_necessity (FE : FunExt) :
  weval (two_worlds FE) (at_world (@weather []) actual) (wempty_env _) = true /\
  weval (two_worlds FE) (necessarily (@weather [])) (wempty_env _) = false.
Proof. split; reflexivity. Qed.

Example necessity_elimination_derivation :
  wderives constructive [necessarily (@weather [])] (at_world weather actual).
Proof.
  change (wderives constructive [necessarily (@weather [])]
    (winstantiate actual (WApp weather (WVar wz)))).
  apply wd_all_elim; apply wd_assume; cbn; auto.
Qed.

Theorem necessity_elimination_in_models (FE : FunExt) :
  wconsequence [necessarily (@weather [])] (at_world weather actual).
Proof. exact (world_derivation_sound FE necessity_elimination_derivation). Qed.

Theorem no_necessitation_from_actual_assumption (FE : FunExt) : forall L,
  ~ wderives L [at_world (@weather []) actual] (necessarily weather).
Proof.
  intro L; apply (world_countermodel_blocks_derivation FE
    (M:=two_worlds FE) (rho:=wempty_env _)).
  - intros p [E | E]; [subst; reflexivity | contradiction].
  - reflexivity.
Qed.

Definition rigid_concept {G} : wtm world_word G (warr ws we) := WLam wjohn.
Definition rigid_claim {G} : wtm world_word G (warr ws wt) :=
  WLam (WApp distinguished (WApp rigid_concept (WVar wz))).
Definition flexible_claim {G} : wtm world_word G (warr ws wt) :=
  WLam (WApp distinguished (WApp person_concept (WVar wz))).

Example concepts_agree_actually (FE : FunExt) :
  weval (two_worlds FE) (at_world (@rigid_concept []) actual) (wempty_env _) =
  weval (two_worlds FE) (at_world (@person_concept []) actual) (wempty_env _).
Proof. reflexivity. Qed.

Example concepts_disagree_elsewhere (FE : FunExt) :
  weval (two_worlds FE) (at_world (@rigid_concept []) alternative) (wempty_env _) <>
  weval (two_worlds FE) (at_world (@person_concept []) alternative) (wempty_env _).
Proof. discriminate. Qed.

Example actual_agreement_does_not_preserve_necessity (FE : FunExt) :
  weval (two_worlds FE) (necessarily (@rigid_claim [])) (wempty_env _) = true /\
  weval (two_worlds FE) (necessarily (@flexible_claim [])) (wempty_env _) = false.
Proof. split; reflexivity. Qed.

(* The argument is evaluated at Actual before abstraction over a world.
   It is not the concept that varies with the abstracted world. *)
Definition frozen_concept : wtm world_word [] (warr ws we) :=
  WApp (WLam (WLam (WVar (wvs wz)))) (at_world person_concept actual).

Example freezing_is_not_worldwise_re_evaluation (FE : FunExt) :
  weval (two_worlds FE) (at_world frozen_concept alternative) (wempty_env _) = true /\
  weval (two_worlds FE) (at_world (@person_concept []) alternative) (wempty_env _) = false.
Proof. split; reflexivity. Qed.

Example explicit_world_beta_conversion :
  wbeta (at_world (WLam (WApp weather (WVar wz))) (@actual []))
        (at_world weather actual).
Proof. apply wb_step. Qed.

Example typed_world_substitution_avoids_capture :
  winstantiate (@WVar world_word [ws] ws wz)
    (@WLam world_word [ws; ws] ws ws (WVar (wvs wz))) =
  @WLam world_word [ws] ws ws (WVar (wvs wz)).
Proof. reflexivity. Qed.

Theorem old_instantiation_in_world_models (FE : FunExt) :
  wconsequence (map (embed_term (@core_words)) [@man_john []; every_man_walks])
    (embed_term (@core_words) walk_john).
Proof. exact (core_derivation_world_sound FE (@core_words) john_walks_derivation). Qed.

Theorem old_syllogism_in_world_models (FE : FunExt) :
  wconsequence (map (embed_term (@core_words)) [@every_man_walks []; every_walker_moves])
    (embed_term (@core_words) every_man_moves).
Proof. exact (core_derivation_world_sound FE (@core_words) syllogism_derivation). Qed.

Example sixteen_world_dependent_predicates (FE : FunExt) :
  length (values (world_finite_domain FE finite_bool finite_bool
    (warr ws (warr we wt)))) = 16.
Proof. reflexivity. Qed.
