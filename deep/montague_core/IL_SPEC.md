# Implicit-index IL to explicit-world Ty2: checkpoint 5

This checkpoint-5 contract remains unchanged in its mathematical scope.
Checkpoint 6 separately proves a translation of the actual legacy IL into
a Prop-valued world/time target; see `../montague_legacy/LEGACY_SPEC.md`.
The legacy gaps below describe what this Boolean world-only translation
does not establish. Checkpoint 7 supplies a guarded target observation
relation in [OBSERVATION_SPEC.md](../montague_legacy/OBSERVATION_SPEC.md).
Full legacy-to-Boolean composition and unrestricted model-class comparison
remain open in the combined project.

## Result and its scope

`explicit_world_preservation` proves that the translation of every well-typed
term of the declared world-only IL fragment has the same denotation as its
independently defined implicit-index evaluator. The theorem quantifies over
the source and target contexts, a typed variable map, related assignments,
and a target term denoting the current world. It takes `FunExt` explicitly.

This is a forward interpretation-preservation theorem. It is not Gallin's
full equivalence theorem, a reverse translation, an IL proof-system adequacy
theorem or a theorem about the actual constructors of `deep/PTQ_deep2.v`.
No independent source reviewer has approved the fragment.

The new files are `ILSyntax.v`, `ILTranslation.v` and `ILExamples.v`.
They add 28 named proved statements. The complete workbench now has 173
in 20 files, with 23 deliberately invalid fixtures rejected by `check.py`.

## 1. Source types and terms

The types are e, t, arrows, and an intension constructor `intens a`.
There is no source world sort available for ordinary source variables:
the source evaluator carries the current world as a separate parameter.
Types translate by:

| Source | Target |
| --- | --- |
| `ie` | `we` |
| `it` | `wt` |
| `iarr a b` | `warr (world_type a) (world_type b)` |
| `intens a` | `warr ws (world_type a)` |

Terms include typed variables, rigid typed constants, lambda, application,
implication, universal quantification at every source type, intension `IUp`,
extension `IDown`, and absolute necessity `IBox`. Binding uses intrinsically
typed de Bruijn variables. There is no tense, primitive equality, choice,
general IL substitution operation or source derivability relation here.

The source constant policy is deliberate. A constant at e denotes the same
individual at every evaluation world. A constant at `intens ie` denotes one
fixed function from worlds to individuals, which may take different values
at different worlds. Applying `IDown` to that constant yields a world-varying
expression of type e. This is not a claim that all linguistic individuals
or noun extensions are rigid.

## 2. Independently defined semantics, shared domains

For a target `wmodel M`, the source carrier at type a is defined as
`wdomain E W (world_type a)`. This is an explicit shared-domain convention:
truth is `bool`, arrows are full internal function spaces, and intensions
are functions from W. Source lexical values are obtained from a supplied
typed map into the target signature. Source universal quantifiers use the
model's reflected quantifier at the translated type.

`ieval` is a separate structural recursion on source syntax. It does not call
`explicit_world`, `translate_intension` or `weval`. Therefore preservation is
not true by defining source evaluation to mean evaluation of its translation.
But it also does not establish an isomorphism between independently chosen
source and target model classes: the domains and quantifiers are shared.

Writing `I(t, rho, w)` for this source evaluator, its important clauses are:

```text
I(x, rho, w)           = rho(x)
I(c, rho, w)           = lexical(c)
I(lambda x. t,rho,w)   = (a |-> I(t, extend(rho,a), w))
I(f u,rho,w)           = I(f,rho,w)(I(u,rho,w))
I(p implies q,rho,w)   = Boolean implication of the two values at w
I(forall x. p,rho,w)   = forall_value(a |-> I(p,extend(rho,a),w))
I(up t,rho,w)          = (w' |-> I(t,rho,w'))
I(down t,rho,w)        = I(t,rho,w)(w)
I(box p,rho,w)         = forall_world(w' |-> I(p,rho,w'))
```

Both quantifiers carry reflection proofs. Necessity ranges over all W;
there is no accessibility relation or time parameter. An assignment is
fixed when `up` or `box` changes the evaluation world. A lambda captures
its current evaluation world, while application evaluates its argument at
that same current world before assigning the resulting value.

## 3. Translation and binding invariant

`explicit_world constants t r w` takes a source term t, a typed variable
map r, and a target term w of world type. It produces a target term of
`world_type` of the source type. Intrinsic typing enforces type preservation.

Under a source lambda or universal binder, `ilift r` maps the new source
variable to the new target variable and shifts every older variable. The
current-world term is weakened under that binder too.

Under `IUp` or `IBox`, `ishift r` shifts all existing source variables but
adds no new source variable. A fresh target world variable supplies the
new current world. `IUp` becomes target lambda, `IBox` target universal
quantification, and `IDown t` becomes application of translated t to the
current-world term. The distinction between these two kinds of binders is
the central invariant of the construction.

The theorem's assignment premise is pointwise:

```text
for each source variable v, target_assignment(r(v)) = source_assignment(v).
```

Its conclusion is:

```text
weval M (explicit_world constants t r w) target_assignment
  = ieval constants M t source_assignment (weval M w target_assignment).
```

The proof is by induction on the source term. Source lambda and universal
cases use the target weakening theorem to preserve the current world;
fresh-world cases preserve the old assignment and vary only the index.
FunExt is used for equalities of functions, including quantifier predicates.
No global axiom, excluded-middle import or proof-irrelevance principle is added.

`translate_intension` packages the construction as a world function over
the translated source context. Its preservation corollary, `translated_truth_iff`,
and `translated_counterexample_iff` relate values at every supplied world.
The last two use a source assignment projected from a target assignment;
they are not whole-model-class equivalence or completeness theorems.

## 4. Cancellation and the substitution warning

The equation `down(up t) = t` is proved semantically without FunExt.
The reverse direction is proved for index-rigid intension expressions:
`index_rigid t` means that for each fixed assignment, changing the current
world does not change the denoted value of t. The reverse proof uses FunExt.
Variables, constants, `up` terms and `box` terms are proved index-rigid.

Index rigidity of an intension expression does not mean that the intension
denotes a constant function. A rigid constant c can denote `w |-> w`.
Its assigned function is fixed; the result of applying that function need not be.

The reverse cancellation fails in general. The concrete model of the nested
constant N uses `bool` as both entity and world carriers, while their object types
remain distinct. N denotes `w |-> (v |-> w)`, where the result is an
individual with the corresponding Boolean code. Thus `down N` evaluated
at w is a constant individual concept, whereas `up(down(down N))` picks
the individual corresponding to each newly supplied world. They differ
at the alternative world when evaluated at the actual world. This is a
regression check, not a newly discovered limitation of Montague's theory.

A second fixture compares, at the actual world:

```text
(lambda x. up x) (down c)
up (down c)
```

For a concept c that picks different individuals at the two worlds, the
first freezes its actual value before abstracting over a world. The second
re-evaluates c at the newly supplied world. Both source and target evaluations
show the difference. No unrestricted source beta/substitution rule is defined.
The target beta step is separately proved and retains the explicit actual
world in the argument. There is no failure of the target's proved beta theorem.

## 5. Relationship to the old IL and the sources

This fragment is source-informed by the world/intension type discussion in
Chatzikyriakidis and Luo (2020), pp. 9-10, and the Ty2 account in Hahn and
Richter (2015), pp. 516-520. The source evaluator's clauses were compared
with the already audited `deep/PTQ_deep2.v`; the old file is not imported or
changed. The code and exact source hashes are recorded in the other contracts.
Gallin's monograph has not received a new direct audit in this checkpoint.

The precise outstanding legacy bridge is substantive:

- The old index is `World * Time`, not just a world. Its `up` varies the
  entire index; its necessity varies only the world at a fixed time.
  Dropping tense constructors alone does not justify dropping time. A
  fixed-time correspondence needs restrictions on denotations and assignments,
  or a target that represents both index components explicitly.
- Old truth is Coq `Prop` and primitive equality is Coq equality. This
  fragment has Boolean truth and no primitive equality. A semantic relation
  or a parallel Prop-valued target would have to justify that change.
- Old `var_s` weakens any subterm, whereas new `ivs` shifts variables.
  A direct syntax bridge must represent that general weakening clause.
- Old fixed lexical constructors and the complete English/PTQ grammar
  have not been mapped. A typed signature parameter is not their source audit.

Accordingly, the next legacy milestone should specify a fragment inclusion
and an index/truth relation, then prove the evaluator diagram for those
actual definitions. An alternative next mathematical milestone is a
rigidity-aware source substitution calculus with a proved admissibility
condition. Neither should be reported as already supplied by this translation.

## 6. Verification and publication boundary

Run `python3 deep/montague_core/check.py --check`. It builds fresh sources,
kernel-rechecks them, audits every named proof's global assumptions, checks
the explicit preservation and cancellation signatures, and rejects bad
variable capture, index-sensitive substitution, unconditional reverse
cancellation and assignment-changing world abstraction.

Existing corpus Coq files, assessments, LaTeX draft, deployed frontend and
live worker remain unchanged. The new statements are local workbench results,
not published atlas evidence or an independently approved semantic analysis.
