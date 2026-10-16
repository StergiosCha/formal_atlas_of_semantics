(* Direct translation of the ACTUAL legacy IL datatype, including time,
   equality, all named constants and arbitrary-term var_s weakening.
   The legacy source is imported unchanged and its assumptions are audited
   separately. This file is not part of the axiom-closed Boolean workbench. *)
From Coq Require Import List.
From MontagueProof Require Import Models.
From MontagueLegacy Require Import IndexSyntax IndexModels.
From LegacyPTQ Require PTQ_deep2.
Import ListNotations.
Set Implicit Arguments.
Module Old := PTQ_deep2.

Fixpoint legacy_type (a : Old.ILType) : pty :=
  match a with
  | Old.ty_e => pe | Old.ty_t => pt
  | Old.ty_arrow a b => parr (legacy_type a) (legacy_type b)
  | Old.ty_s a => parr pi (legacy_type a)
  end.

Fixpoint legacy_carrier (a : Old.ILType) :
  Old.Den a = pdomain Old.Entity Old.World Old.Time (legacy_type a) :=
  match a with
  | Old.ty_e => eq_refl | Old.ty_t => eq_refl
  | Old.ty_arrow a b => arrow_carrier (legacy_carrier a) (legacy_carrier b)
  | Old.ty_s a => arrow_carrier eq_refl (legacy_carrier a)
  end.
Definition legacy_lift a := carrier_cast (legacy_carrier a).
Definition legacy_lower a := carrier_cast (eq_sym (legacy_carrier a)).

Lemma legacy_lower_lift a x : legacy_lower a (legacy_lift a x) = x.
Proof. apply cast_back. Qed.
Lemma legacy_lift_lower a x : legacy_lift a (legacy_lower a x) = x.
Proof. apply cast_forward. Qed.
Lemma legacy_application a b (f : Old.Den (Old.ty_arrow a b)) x :
  legacy_lift (Old.ty_arrow a b) f (legacy_lift a x) = legacy_lift b (f x).
Proof. apply cast_application. Qed.
Lemma legacy_lambda a b (f : Old.Den (Old.ty_arrow a b)) :
  legacy_lift (Old.ty_arrow a b) f = fun x => legacy_lift b (f (legacy_lower a x)).
Proof. apply cast_lambda. Qed.
Lemma legacy_intension a (f : Old.Den (Old.ty_s a)) :
  legacy_lift (Old.ty_s a) f = fun i => legacy_lift a (f i).
Proof. apply cast_lambda. Qed.
Lemma legacy_equality a (x y : Old.Den a) :
  (legacy_lift a x = legacy_lift a y) = (x = y).
Proof. apply cast_equality. Qed.
Lemma legacy_forall a (f : Old.Den a -> Prop) :
  (forall y, f (legacy_lower a y)) = (forall x, f x).
Proof. apply cast_forall. Qed.
Lemma legacy_exists a (f : Old.Den a -> Prop) :
  (exists y, f (legacy_lower a y)) = (exists x, f x).
Proof. apply cast_exists. Qed.

Inductive legacy_word : Old.ILType -> Type :=
| LJohn : legacy_word Old.ty_e | LBill : legacy_word Old.ty_e
| LMary : legacy_word Old.ty_e | LNinety : legacy_word Old.ty_e
| LWalk : legacy_word Old.ty_iv | LRun : legacy_word Old.ty_iv
| LTalk : legacy_word Old.ty_iv | LRise : legacy_word Old.ty_iv
| LChange : legacy_word Old.ty_iv
| LMan : legacy_word Old.ty_cn | LWoman : legacy_word Old.ty_cn
| LUnicorn : legacy_word Old.ty_cn | LPark : legacy_word Old.ty_cn
| LFish : legacy_word Old.ty_cn | LPrice : legacy_word Old.ty_cn
| LTemperature : legacy_word Old.ty_cn
| LFind : legacy_word Old.ty_tv | LLose : legacy_word Old.ty_tv
| LEat : legacy_word Old.ty_tv | LLove : legacy_word Old.ty_tv
| LSeek : legacy_word Old.ty_tv
| LTry : legacy_word (Old.ty_arrow Old.ty_iv Old.ty_iv)
| LWish : legacy_word (Old.ty_arrow Old.ty_iv Old.ty_iv)
| LNecessarily : legacy_word (Old.ty_arrow Old.ty_iv Old.ty_iv)
| LAllegedly : legacy_word (Old.ty_arrow Old.ty_iv Old.ty_iv).
Definition word_value a (c : legacy_word a) : Old.Den a :=
  match c in legacy_word a return Old.Den a with
  | LJohn => Old.john_e | LBill => Old.bill_e | LMary => Old.mary_e | LNinety => Old.ninety_e
  | LWalk => Old.walk_den | LRun => Old.run_den | LTalk => Old.talk_den
  | LRise => Old.rise_den | LChange => Old.change_den
  | LMan => Old.man_den | LWoman => Old.woman_den | LUnicorn => Old.unicorn_den
  | LPark => Old.park_den | LFish => Old.fish_den | LPrice => Old.price_den
  | LTemperature => Old.temperature_den
  | LFind => Old.find_den | LLose => Old.lose_den | LEat => Old.eat_den
  | LLove => Old.love_den | LSeek => Old.seek_den
  | LTry => Old.try_to_den | LWish => Old.wish_to_den
  | LNecessarily => Old.necessarily_den | LAllegedly => Old.allegedly_den
  end.
Inductive legacy_symbol : pty -> Type :=
| LegacySymbol : forall a, legacy_word a -> legacy_symbol (legacy_type a).
Definition legacy_lex a (c : legacy_symbol a) : pdomain Old.Entity Old.World Old.Time a :=
  match c in legacy_symbol a return pdomain Old.Entity Old.World Old.Time a with
  | @LegacySymbol a c => legacy_lift a (@word_value a c)
  end.
Definition named {G a} (c : legacy_word a) : ptm legacy_symbol G (legacy_type a) :=
  PConst (LegacySymbol c).

Fixpoint legacy_vars (G : Old.Ctx) (D : list pty) : Type :=
  match G with [] => unit | a :: G => (pvar D (legacy_type a) * legacy_vars G D)%type end.
Fixpoint shift_vars {G D b} : legacy_vars G D -> legacy_vars G (b :: D) :=
  match G return legacy_vars G D -> legacy_vars G (b :: D) with
  | [] => fun _ => tt
  | a :: G => fun r => (pvs (fst r), shift_vars (snd r))
  end.
Definition lift_vars {G D a} (r : legacy_vars G D) : legacy_vars (a :: G) (legacy_type a :: D) :=
  (pz, shift_vars r).

Fixpoint compile_legacy {G a} (t : Old.IL G a) : forall D,
  legacy_vars G D -> ptm legacy_symbol D pi -> ptm legacy_symbol D (legacy_type a) :=
  match t in Old.IL G' a' return forall D,
    legacy_vars G' D -> ptm legacy_symbol D pi -> ptm legacy_symbol D (legacy_type a') with
  | @Old.var_z _ _ => fun D r _ => PVar (fst r)
  | @Old.var_s _ _ _ t => fun D r i => compile_legacy t (snd r) i
  | Old.c_john _ => fun D _ _ => named LJohn
  | Old.c_bill _ => fun D _ _ => named LBill
  | Old.c_mary _ => fun D _ _ => named LMary
  | Old.c_ninety _ => fun D _ _ => named LNinety
  | Old.c_walk _ => fun D _ _ => named LWalk
  | Old.c_run _ => fun D _ _ => named LRun
  | Old.c_talk _ => fun D _ _ => named LTalk
  | Old.c_rise _ => fun D _ _ => named LRise
  | Old.c_change _ => fun D _ _ => named LChange
  | Old.c_man _ => fun D _ _ => named LMan
  | Old.c_woman _ => fun D _ _ => named LWoman
  | Old.c_unicorn _ => fun D _ _ => named LUnicorn
  | Old.c_park _ => fun D _ _ => named LPark
  | Old.c_fish _ => fun D _ _ => named LFish
  | Old.c_price _ => fun D _ _ => named LPrice
  | Old.c_temperature _ => fun D _ _ => named LTemperature
  | Old.c_find _ => fun D _ _ => named LFind
  | Old.c_lose _ => fun D _ _ => named LLose
  | Old.c_eat _ => fun D _ _ => named LEat
  | Old.c_love _ => fun D _ _ => named LLove
  | Old.c_seek _ => fun D _ _ => named LSeek
  | Old.c_try_to _ => fun D _ _ => named LTry
  | Old.c_wish_to _ => fun D _ _ => named LWish
  | Old.c_necessarily _ => fun D _ _ => named LNecessarily
  | Old.c_allegedly _ => fun D _ _ => named LAllegedly
  | Old.lam t => fun D r i => PLam (compile_legacy t (lift_vars r) (pweaken i))
  | Old.app f x => fun D r i => PApp (compile_legacy f r i) (compile_legacy x r i)
  | Old.eq_ x y => fun D r i => PEq (compile_legacy x r i) (compile_legacy y r i)
  | Old.not_ p => fun D r i => PNot (compile_legacy p r i)
  | Old.and_ p q => fun D r i => PAnd (compile_legacy p r i) (compile_legacy q r i)
  | Old.or_ p q => fun D r i => POr (compile_legacy p r i) (compile_legacy q r i)
  | Old.imp_ p q => fun D r i => PImp (compile_legacy p r i) (compile_legacy q r i)
  | Old.iff_ p q => fun D r i => PIff (compile_legacy p r i) (compile_legacy q r i)
  | Old.forall_ p => fun D r i => PAll (compile_legacy p (lift_vars r) (pweaken i))
  | Old.exists_ p => fun D r i => PExists (compile_legacy p (lift_vars r) (pweaken i))
  | Old.nec_ p => fun D r i => PAll (compile_legacy p (shift_vars r)
      (PPair (PVar pz) (PTime (pweaken i))))
  | Old.will_ p => fun D r i => PExists (PAnd
      (PBefore (PTime (pweaken i)) (PVar pz))
      (compile_legacy p (shift_vars r) (PPair (PWorld (pweaken i)) (PVar pz))))
  | Old.has_ p => fun D r i => PExists (PAnd
      (PBefore (PVar pz) (PTime (pweaken i)))
      (compile_legacy p (shift_vars r) (PPair (PWorld (pweaken i)) (PVar pz))))
  | Old.up t => fun D r _ => PLam (compile_legacy t (shift_vars r) (PVar pz))
  | Old.down t => fun D r i => PApp (compile_legacy t r i) i
  end.

Fixpoint assignments_match {G D} (r : legacy_vars G D)
  (rho : @penv Old.Entity Old.World Old.Time D) (env : Old.Env G) : Prop :=
  match G as G0 return legacy_vars G0 D -> Old.Env G0 -> Prop with
  | [] => fun _ _ => True
  | a :: G => fun r env => rho _ (fst r) = legacy_lift a (fst env) /\
      assignments_match (snd r) rho (snd env)
  end r env.

Lemma assignments_shift : forall G D b (r : legacy_vars G D) rho env x,
  assignments_match r rho env ->
  assignments_match (@shift_vars G D b r) (pextend rho x) env.
Proof. induction G; intros; cbn in *; [exact I | split; [apply H | apply IHG; apply H]]. Qed.

Lemma assignments_lift : forall G D a (r : legacy_vars G D) rho env x,
  assignments_match r rho env ->
  assignments_match (@lift_vars G D a r) (pextend rho x)
    (Old.env_cons (legacy_lower a x) env).
Proof.
  intros; split; [cbn; symmetry; apply legacy_lift_lower | apply assignments_shift; assumption].
Qed.

(* The environment premise is inhabited for EVERY legacy assignment. *)
Definition empty_target_env : @penv Old.Entity Old.World Old.Time [] :=
  fun a v => match v in pvar G a return
    match G with [] => pdomain Old.Entity Old.World Old.Time a | _ :: _ => unit end
    with pz => tt | pvs _ => tt end.
Fixpoint canonical_vars (G : Old.Ctx) : legacy_vars G (map legacy_type G) :=
  match G as G0 return legacy_vars G0 (map legacy_type G0) with
  | [] => tt
  | a :: G => (pz, shift_vars (canonical_vars G))
  end.
Fixpoint canonical_env (G : Old.Ctx) : Old.Env G -> @penv Old.Entity Old.World Old.Time (map legacy_type G) :=
  match G as G0 return Old.Env G0 -> @penv Old.Entity Old.World Old.Time (map legacy_type G0) with
  | [] => fun _ => empty_target_env
  | a :: G => fun env => pextend (canonical_env G (snd env)) (legacy_lift a (fst env))
  end.
Lemma canonical_assignments_match : forall G env,
  assignments_match (canonical_vars G) (canonical_env G env) env.
Proof.
  induction G; intros; cbn; [exact I | split; [reflexivity |]].
  apply assignments_shift; apply IHG.
Qed.

Definition legacy_as_index_function {G a} (t : Old.IL G a)
  : ptm legacy_symbol (map legacy_type G) (parr pi (legacy_type a)) :=
  PLam (compile_legacy t (shift_vars (canonical_vars G)) (PVar pz)).

Definition target_eval := @peval legacy_symbol Old.Entity Old.World Old.Time legacy_lex Old.time_lt.

Ltac expose_target lhs :=
  lazymatch goal with |- _ = ?rhs => change (lhs = rhs) end.

Theorem legacy_interpretation_preservation (FE : FunExt) : forall G a (t : Old.IL G a)
  D (r : legacy_vars G D) (i : ptm legacy_symbol D pi) rho env,
  assignments_match r rho env ->
  target_eval (compile_legacy t r i) rho = legacy_lift a (Old.eval t env (target_eval i rho)).
Proof.
  intros G a t; induction t; intros D r i rho env H;
    cbn -[legacy_lift target_eval] in *; try reflexivity.
  - exact (proj1 H).
  - apply IHt; exact (proj2 H).
  - expose_target (fun x => target_eval (compile_legacy t (lift_vars r) (pweaken i)) (pextend rho x)).
    rewrite legacy_lambda; apply FE; intro x.
    refine (eq_trans (IHt _ (lift_vars r) (pweaken i) (pextend rho x)
      (Old.env_cons (legacy_lower _ x) env) (@assignments_lift _ _ _ r rho env x H)) _).
    unfold target_eval; rewrite (peval_weaken _ _ FE); reflexivity.
  - expose_target (target_eval (compile_legacy t1 r i) rho (target_eval (compile_legacy t2 r i) rho)).
    refine (eq_trans (f_equal2 (fun f x => f x) (IHt1 _ r i rho env H) (IHt2 _ r i rho env H)) _).
    apply legacy_application.
  - expose_target (target_eval (compile_legacy t1 r i) rho = target_eval (compile_legacy t2 r i) rho).
    refine (eq_trans (f_equal2 (fun x y => x = y) (IHt1 _ r i rho env H) (IHt2 _ r i rho env H)) _).
    apply legacy_equality.
  - expose_target (~ target_eval (compile_legacy t r i) rho).
    exact (f_equal (fun p => ~ p) (IHt _ r i rho env H)).
  - expose_target (target_eval (compile_legacy t1 r i) rho /\ target_eval (compile_legacy t2 r i) rho).
    exact (f_equal2 and (IHt1 _ r i rho env H) (IHt2 _ r i rho env H)).
  - expose_target (target_eval (compile_legacy t1 r i) rho \/ target_eval (compile_legacy t2 r i) rho).
    exact (f_equal2 or (IHt1 _ r i rho env H) (IHt2 _ r i rho env H)).
  - expose_target (target_eval (compile_legacy t1 r i) rho -> target_eval (compile_legacy t2 r i) rho).
    exact (f_equal2 (fun p q => p -> q) (IHt1 _ r i rho env H) (IHt2 _ r i rho env H)).
  - expose_target (target_eval (compile_legacy t1 r i) rho <-> target_eval (compile_legacy t2 r i) rho).
    exact (f_equal2 iff (IHt1 _ r i rho env H) (IHt2 _ r i rho env H)).
  - expose_target (forall x, target_eval (compile_legacy t (lift_vars r) (pweaken i)) (pextend rho x)).
    transitivity (forall x, Old.eval t (Old.env_cons (legacy_lower _ x) env) (target_eval i rho)).
    + apply (f_equal (fun f : pdomain Old.Entity Old.World Old.Time (legacy_type σ) -> Prop => forall x, f x)).
      apply FE; intro x.
      refine (eq_trans (IHt _ (lift_vars r) (pweaken i) (pextend rho x)
        (Old.env_cons (legacy_lower _ x) env) (@assignments_lift _ _ _ r rho env x H)) _).
      unfold target_eval; rewrite (peval_weaken _ _ FE); reflexivity.
    + exact (legacy_forall σ (fun x => Old.eval t (Old.env_cons x env) (target_eval i rho))).
  - expose_target (exists x, target_eval (compile_legacy t (lift_vars r) (pweaken i)) (pextend rho x)).
    transitivity (exists x, Old.eval t (Old.env_cons (legacy_lower _ x) env) (target_eval i rho)).
    + apply (f_equal (fun f : pdomain Old.Entity Old.World Old.Time (legacy_type σ) -> Prop => exists x, f x)).
      apply FE; intro x.
      refine (eq_trans (IHt _ (lift_vars r) (pweaken i) (pextend rho x)
        (Old.env_cons (legacy_lower _ x) env) (@assignments_lift _ _ _ r rho env x H)) _).
      unfold target_eval; rewrite (peval_weaken _ _ FE); reflexivity.
    + exact (legacy_exists σ (fun x => Old.eval t (Old.env_cons x env) (target_eval i rho))).
  - expose_target (forall w, target_eval (compile_legacy t (shift_vars r)
      (PPair (PVar pz) (PTime (pweaken i)))) (pextend rho w)).
    apply (f_equal (fun f : Old.World -> Prop => forall w, f w)); apply FE; intro w.
    refine (eq_trans (IHt _ (shift_vars (b:=pw) r) _ (pextend (a:=pw) rho w) env
      (@assignments_shift _ _ pw r rho env w H)) _).
    unfold target_eval; cbn -[pweaken]; rewrite (peval_weaken _ _ FE); reflexivity.
  - expose_target (exists t' : Old.Time, Old.time_lt (snd (target_eval (pweaken i) (pextend (a:=ptime) rho t'))) t' /\
      target_eval (compile_legacy t (shift_vars r) (PPair (PWorld (pweaken i)) (PVar pz)))
        (pextend (a:=ptime) rho t')).
    apply (f_equal (fun f : Old.Time -> Prop => exists t', f t')); apply FE; intro t'.
    apply f_equal2.
    + unfold target_eval; rewrite (peval_weaken _ _ FE); reflexivity.
    + refine (eq_trans (IHt _ (shift_vars (b:=ptime) r) _ (pextend (a:=ptime) rho t') env
        (@assignments_shift _ _ ptime r rho env t' H)) _).
      unfold target_eval; cbn -[pweaken]; rewrite (peval_weaken _ _ FE); reflexivity.
  - expose_target (exists t' : Old.Time, Old.time_lt t' (snd (target_eval (pweaken i) (pextend (a:=ptime) rho t'))) /\
      target_eval (compile_legacy t (shift_vars r) (PPair (PWorld (pweaken i)) (PVar pz)))
        (pextend (a:=ptime) rho t')).
    apply (f_equal (fun f : Old.Time -> Prop => exists t', f t')); apply FE; intro t'.
    apply f_equal2.
    + unfold target_eval; rewrite (peval_weaken _ _ FE); reflexivity.
    + refine (eq_trans (IHt _ (shift_vars (b:=ptime) r) _ (pextend (a:=ptime) rho t') env
        (@assignments_shift _ _ ptime r rho env t' H)) _).
      unfold target_eval; cbn -[pweaken]; rewrite (peval_weaken _ _ FE); reflexivity.
  - expose_target (fun i' : Old.Index => target_eval (compile_legacy t (shift_vars r) (PVar pz)) (pextend (a:=pi) rho i')).
    rewrite legacy_intension; apply FE; intro i'.
    apply IHt; apply assignments_shift; exact H.
  - expose_target (target_eval (compile_legacy t r i) rho (target_eval i rho)).
    refine (eq_trans (f_equal (fun f => f (target_eval i rho)) (IHt _ r i rho env H)) _).
    rewrite legacy_intension; reflexivity.
Qed.

Theorem legacy_open_preservation (FE : FunExt) : forall G a (t : Old.IL G a) env i,
  target_eval (legacy_as_index_function t) (canonical_env G env) i =
  legacy_lift a (Old.eval t env i).
Proof.
  intros; unfold legacy_as_index_function; cbn -[compile_legacy canonical_env].
  apply legacy_interpretation_preservation; [exact FE |].
  apply assignments_shift; apply canonical_assignments_match.
Qed.

Theorem legacy_truth_preservation (FE : FunExt) : forall G (p : Old.IL G Old.ty_t) env i,
  target_eval (legacy_as_index_function p) (canonical_env G env) i <-> Old.eval p env i.
Proof. intros; rewrite (legacy_open_preservation FE); reflexivity. Qed.

Theorem legacy_counterexample_preservation (FE : FunExt) : forall G
  (p q : Old.IL G Old.ty_t) env i,
  (target_eval (legacy_as_index_function p) (canonical_env G env) i /\
   ~ target_eval (legacy_as_index_function q) (canonical_env G env) i) <->
  (Old.eval p env i /\ ~ Old.eval q env i).
Proof. intros; repeat rewrite (legacy_open_preservation FE); reflexivity. Qed.
