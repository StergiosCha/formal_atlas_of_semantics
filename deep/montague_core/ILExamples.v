(* Binding and world-shift regressions, not claims of new linguistic facts. *)
From Coq Require Import List Bool.
From MontagueProof Require Import Models BooleanModels BooleanFinite Ty2Syntax
  Ty2Models Ty2Examples ILSyntax ILTranslation.
Import ListNotations.
Set Implicit Arguments.

Inductive il_word : ity -> Type :=
| IJohn : il_word ie
| IWeather : il_word (intens it)
| IConcept : il_word (intens ie)
| INested : il_word (intens (intens ie))
| IProperty : il_word (iarr ie it).
Inductive il_target : wty -> Type :=
| LiftedWord : forall a, il_word a -> il_target (world_type a)
| IActual : il_target ws
| IAlternative : il_target ws.
Definition il_constants a (c : il_word a) := LiftedWord c.
Definition il_lex a (c : il_word a) : wdomain bool bool (world_type a) :=
  match c in il_word a return wdomain bool bool (world_type a) with
  | IJohn => true | IWeather => fun w => w | IConcept => fun w => w
  | INested => fun w _ => w | IProperty => fun x => x
  end.
Definition il_two_worlds (FE : FunExt) : wmodel il_target :=
  world_finite_model FE finite_bool finite_bool
    (fun a c => match c in il_target a return wdomain bool bool a with
    | @LiftedWord a c => @il_lex a c | IActual => true | IAlternative => false
    end).
Definition iempty_env {target} (M : wmodel target) : ienv M [] :=
  fun a v => match v in ivar G a return
    match G with [] => idomain M a | _ :: _ => unit end
    with iz => tt | ivs _ => tt end.
Definition il_weather {G} : itm il_word G it := IDown (IConst IWeather).
Definition il_person {G} : itm il_word G ie := IDown (IConst IConcept).
Definition il_frozen : itm il_word [] (intens ie) :=
  IApp (ILam (IUp (IVar iz))) il_person.
Definition il_recomputed : itm il_word [] (intens ie) := IUp il_person.
Definition il_nonrigid_intension : itm il_word [] (intens ie) := IDown (IConst INested).

Example source_world_sensitive_truth (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) (@il_weather []) (iempty_env _) true = true /\
  ieval il_constants (il_two_worlds FE) (@il_weather []) (iempty_env _) false = false.
Proof. split; reflexivity. Qed.

Example source_actual_truth_not_necessity (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) (@il_weather []) (iempty_env _) true = true /\
  ieval il_constants (il_two_worlds FE) (IBox (@il_weather [])) (iempty_env _) true = false.
Proof. split; reflexivity. Qed.

Example assigned_variable_survives_world_shift (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) (@IUp il_word [ie] ie (IVar iz))
    (@iextend il_target (il_two_worlds FE) [] ie (iempty_env _) true) true false = true.
Proof. reflexivity. Qed.

Example il_binder_translation_is_capture_free :
  explicit_world il_constants (@ILam il_word [] ie (intens ie) (IUp (IVar iz)))
    (@ivar_embed []) (WConst IActual) = WLam (WLam (WVar (wvs wz))).
Proof. reflexivity. Qed.

Example down_translation_uses_current_world :
  explicit_world il_constants (@il_person []) (@ivar_embed []) (WConst IAlternative) =
  WApp (WConst (LiftedWord IConcept)) (WConst IAlternative).
Proof. reflexivity. Qed.

Example up_rebinds_world_but_not_assignment :
  explicit_world il_constants il_frozen (@ivar_embed []) (WConst IActual) =
  WApp (WLam (WLam (WVar (wvs wz))))
    (WApp (WConst (LiftedWord IConcept)) (WConst IActual)).
Proof. reflexivity. Qed.

Example unsafe_index_substitution_changes_denotation (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) il_frozen (iempty_env _) true false = true /\
  ieval il_constants (il_two_worlds FE) il_recomputed (iempty_env _) true false = false.
Proof. split; reflexivity. Qed.

Theorem source_freezing_and_recomputation_are_distinct (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) il_frozen (iempty_env _) true <>
  ieval il_constants (il_two_worlds FE) il_recomputed (iempty_env _) true.
Proof. intro H; apply (f_equal (fun f => f false)) in H; discriminate. Qed.

Example target_preserves_freezing_counterexample (FE : FunExt) :
  weval (il_two_worlds FE) (translate_intension il_constants il_frozen)
    (wempty_env _) true false = true /\
  weval (il_two_worlds FE) (translate_intension il_constants il_recomputed)
    (wempty_env _) true false = false.
Proof. split; reflexivity. Qed.

Example up_down_requires_a_side_condition (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) (IUp (IDown il_nonrigid_intension))
    (iempty_env _) true false = false /\
  ieval il_constants (il_two_worlds FE) il_nonrigid_intension (iempty_env _) true false = true.
Proof. split; reflexivity. Qed.

Theorem nested_extension_is_not_index_rigid (FE : FunExt) :
  ~ index_rigid il_constants (il_two_worlds FE) il_nonrigid_intension.
Proof.
  intro R; specialize (R (iempty_env _) true false).
  apply (f_equal (fun f => f false)) in R; discriminate.
Qed.

Definition il_quantified : itm il_word [] it :=
  IAll (IDown (IUp (IApp (IConst IProperty) (IVar iz)))).
Example quantification_survives_world_abstraction (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) il_quantified (iempty_env _) true = false /\
  weval (il_two_worlds FE) (translate_intension il_constants il_quantified)
    (wempty_env _) true = false.
Proof. split; reflexivity. Qed.

Definition il_higher_order : itm il_word [] it :=
  IAll (IApp (IVar iz) (IConst IJohn)).
Example higher_order_quantification_is_not_a_sample (FE : FunExt) :
  ieval il_constants (il_two_worlds FE) il_higher_order (iempty_env _) true = false /\
  weval (il_two_worlds FE) (translate_intension il_constants il_higher_order)
    (wempty_env _) true = false.
Proof. split; reflexivity. Qed.

Example implication_translation_regression (FE : FunExt) :
  weval (il_two_worlds FE)
    (translate_intension il_constants (IImp (IBox il_weather) (@il_weather [])))
    (wempty_env _) false = true.
Proof. reflexivity. Qed.

(* The target's ordinary beta rule is safe: its argument explicitly mentions
   IActual. This is not permission to substitute a world-sensitive IL term
   under Up while forgetting the evaluation world. *)
Example target_beta_keeps_the_evaluation_world :
  wbeta (explicit_world il_constants il_frozen (@ivar_embed []) (WConst IActual))
    (WLam (WApp (WConst (LiftedWord IConcept)) (WConst IActual))).
Proof. apply wb_step. Qed.

Example preservation_applies_to_open_intensional_terms (FE : FunExt)
  (rho : wenv (il_two_worlds FE) [we]) w :
  weval (il_two_worlds FE)
    (translate_intension il_constants (@IUp il_word [ie] ie (IVar iz))) rho w =
  ieval il_constants (il_two_worlds FE) (@IUp il_word [ie] ie (IVar iz))
    (@source_env il_target (il_two_worlds FE) [ie] rho) w.
Proof.
  exact (@intension_translation_preservation il_word il_target il_constants
    (il_two_worlds FE) FE [ie] (intens ie) (IUp (IVar iz)) rho w).
Qed.
