(* A3 L2 — vacuity / triviality probe machinery (Ltac2, Coq 8.20, stdlib only).

   For a proved theorem T with statement  forall b1..bk, H1 -> .. -> Hn -> C:

     vacuity goal     forall b1..bk, H1 -> .. -> Hn -> False
                      provable  =>  the hypotheses are jointly unsatisfiable,
                      so T is vacuous (machine-checked refutation of content).

     triviality goal  forall <dependent binders>, C
                      i.e. the statement with every *non-dependent Prop*
                      premise stripped; provable by a bounded trivial tactic
                      bank  =>  the conclusion never needed the hypotheses.

   Both goals are built symbolically from Constr.type of the theorem's
   reference — no vernacular generation, no LLM. Everything runs inside one
   ambient `Goal True` proof; each probe is an `assert <goal> by (timeout 5
   <bank>)` whose success/failure is caught with Control.case, so one bad
   theorem never kills a batch. Verdicts are printed as machine-parseable
   lines:

     PROBE|<fqname>|vacuity|VACUOUS      hypotheses proved contradictory
     PROBE|<fqname>|vacuity|ok           not shown vacuous (NOT a proof of ok)
     PROBE|<fqname>|triviality|TRIVIAL   conclusion provable sans hypotheses
     PROBE|<fqname>|triviality|ok        not shown trivial
     PROBE|<fqname>|<probe>|BAILOUT|<r>  probe could not be run — never
                                         silently skipped, never guessed.

   Consumed by run_probes.py, which writes records/<key>.probe.json. *)

From Ltac2 Require Import Ltac2.
Require Import Lia.

Ltac2 Type exn ::= [ ProbeBailout (string) ].

(* ---------- output ---------- *)

Ltac2 emit (name : string) (probe : string) (verdict : string) : unit :=
  Message.print (Message.of_string
    (String.concat "" ["PROBE|"; name; "|"; probe; "|"; verdict])).

Ltac2 bail_verdict (e : exn) (fallback : string) : string :=
  match e with
  | ProbeBailout r => String.app "BAILOUT|" r
  | _ => String.app "BAILOUT|" fallback
  end.

(* ---------- vacuity goal: replace the conclusion with False ---------- *)

Ltac2 rec vacuity_goal (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Cast c _ _ => vacuity_goal c
  | Constr.Unsafe.Prod b body =>
      Constr.Unsafe.make (Constr.Unsafe.Prod b (vacuity_goal body))
  | Constr.Unsafe.LetIn b v body =>
      Constr.Unsafe.make (Constr.Unsafe.LetIn b v (vacuity_goal body))
  | _ => constr:(False)
  end.

(* ---------- triviality goal: strip non-dependent Prop premises ---------- *)

(* [prefix] is the telescope of binders kept so far, innermost first, each
   paired with (Some v) when it was a let-in. Rebuilding the prefix over a
   term yields a closed term, which is what lets us ask Coq for the sort of
   an open premise type: by impredicativity, [forall prefix, ty] lives in
   Prop exactly when [ty] does. *)

Ltac2 rebuild_prefix (prefix : (binder * constr option) list) (core : constr) : constr :=
  List.fold_left
    (fun acc bv =>
       let (b, v) := bv in
       match v with
       | None => Constr.Unsafe.make (Constr.Unsafe.Prod b acc)
       | Some vv => Constr.Unsafe.make (Constr.Unsafe.LetIn b vv acc)
       end)
    core prefix.

Ltac2 sort_is_prop (prefix : (binder * constr option) list) (ty : constr) : bool :=
  let closed := rebuild_prefix prefix ty in
  match Control.case (fun () => Constr.type closed) with
  | Val p => let (srt, _) := p in Constr.equal srt constr:(Prop)
  | Err _ => Control.zero (ProbeBailout "premise_sort_check_failed")
  end.

(* Dependency test for Rel 1 in [body] that does not trust
   Constr.Unsafe.occurn: in Coq 8.20.1 the underlying external has inverted
   polarity (it answers "does NOT occur", the semantics of noccur_between).
   Substituting two distinct closed dummies for Rel 1 and comparing is
   polarity-proof: the results coincide iff Rel 1 never occurs, and when they
   do coincide either one IS the correctly lowered body. *)

Ltac2 strip_if_nondep (body : constr) : constr option :=
  let s1 := Constr.Unsafe.substnl [constr:(True)] 0 body in
  let s2 := Constr.Unsafe.substnl [constr:(False)] 0 body in
  if Constr.equal s1 s2 then Some s1 else None.

(* Walk the Prod telescope. A binder is stripped iff (a) the rest of the
   statement does not depend on it (Rel 1 unused) and (b) its type is a Prop
   — i.e. it is an honest hypothesis, not data. Everything else, including
   dependent Prop premises and let-ins, is kept. Returns the rebuilt goal and
   how many premises were stripped. *)

Ltac2 rec triv_walk (prefix : (binder * constr option) list) (n : int) (t : constr)
    : constr * int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Cast c _ _ => triv_walk prefix n c
  | Constr.Unsafe.Prod b body =>
      match strip_if_nondep body with
      | Some lowered =>
          if sort_is_prop prefix (Constr.Binder.type b)
          then triv_walk prefix (Int.add n 1) lowered
          else triv_walk ((b, None) :: prefix) n body
      | None => triv_walk ((b, None) :: prefix) n body
      end
  | Constr.Unsafe.LetIn b v body =>
      triv_walk ((b, Some v) :: prefix) n body
  | _ => (rebuild_prefix prefix t, n)
  end.

Ltac2 triviality_goal (t : constr) : constr * int := triv_walk [] 0 t.

(* ---------- the bounded tactic bank ---------- *)

(* assert <g> by (timeout 5 (intros; solve [bank])); clear — run through
   Ltac1 so the whole attempt is under Ltac1's wall-clock timeout. The bank
   is fixed and cheap on failure: exact I (catches conclusions that unfold
   to True), tauto, congruence, lia, firstorder. No hint databases beyond
   core are ever consulted, and the probed theory is Required but not
   Imported, so its own lemmas cannot leak into a probe proof via hints. *)

Ltac2 solve_bank (g : constr) : unit :=
  ltac1:(g |-
           let h := fresh "PROBE_HYP" in
           assert g as h by
             (timeout 5 (intros; solve [ exact I | tauto | congruence
                                       | lia | firstorder ]));
           clear h)
    (Ltac1.of_constr g).

Ltac2 try_solve (g : constr) : bool :=
  match Control.case (fun () => solve_bank g) with
  | Val _ => true
  | Err _ => false
  end.

(* ---------- probe runners ---------- *)

Ltac2 checked (g : constr) : constr option :=
  match Constr.Unsafe.check g with
  | Val g2 => Some g2
  | Err _ => None
  end.

Ltac2 run_probe (name : string) (probe : string) (build : unit -> constr) : unit :=
  match Control.case build with
  | Err e => emit name probe (bail_verdict e "goal_build_failed")
  | Val p =>
      let (g, _) := p in
      match checked g with
      | None => emit name probe (String.app "BAILOUT|" "ill_typed_probe_goal")
      | Some g2 =>
          let positive := match String.equal probe "vacuity" with
                          | true => "VACUOUS" | false => "TRIVIAL" end in
          if try_solve g2 then emit name probe positive else emit name probe "ok"
      end
  end.

(* One theorem, both probes. Never raises: every failure path is caught and
   reported as a BAILOUT line, so a batch of hundreds survives any single
   bad statement. *)

Ltac2 probe_theorem (name : string) (r : Std.reference) : unit :=
  match Control.case (fun () => Constr.type (Env.instantiate r)) with
  | Err _ =>
      emit name "vacuity" "BAILOUT|statement_unavailable";
      emit name "triviality" "BAILOUT|statement_unavailable"
  | Val p =>
      let (stmt, _) := p in
      run_probe name "vacuity" (fun () => vacuity_goal stmt);
      run_probe name "triviality"
        (fun () => let (g, _) := triviality_goal stmt in g)
  end.
