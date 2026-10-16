# World-sensitive layer: checkpoint 4

This contract describes the checkpoint-4 Ty2 layer, retained in checkpoint 5.
The subsequently implemented world-only IL translation has its own contract
in [IL_SPEC.md](IL_SPEC.md). Checkpoint 6 adds an actual legacy correspondence
to a parallel Prop-valued world/time target in `../montague_legacy/LEGACY_SPEC.md`.
Checkpoint 7 adds a guarded comparison of the existing Boolean and Prop
target evaluators; see [OBSERVATION_SPEC.md](../montague_legacy/OBSERVATION_SPEC.md).
It does not compare tense or cover every legacy translation. The table below
records obligations not established by this Boolean Ty2 layer itself.

## What is now established

The workbench now has a selected Ty2 language with distinct entity, truth and
world types, constant-domain Boolean models, a C-style proof calculus and
soundness. It also has an interpretation-preserving embedding of the previous
extensional Boolean core and a theorem transporting the semantic consequences
of its existing derivations.

The model's world domain is real data, not a placeholder annotation. The
finite two-world example computes different truth values at different worlds,
and its countermodels distinguish local truth from absolute necessity and
actual coextension from agreement of individual concepts at every world.

These are implementations of familiar semantic distinctions, not claims of
new linguistic discoveries. The work is still represented and checked in Coq.

## Source contract

Directly consulted:

- Chatzikyriakidis and Luo (2020), printed pp. 9-10 and footnote 11, on
  adding the world type s and representing intensions by `s -> A`.
- Hahn and Richter (2015), Definitions 1-2, printed pp. 516-518, for the
  Ty2 types and typed abstraction/application, together with Definitions
  4-5, pp. 518-520, for full/general model distinctions.

The artifact hashes and bibliographic details are in `README.md` and
`MODEL_SPEC.md`. Gallin's monograph is background cited by those sources;
this does not claim a fresh direct audit of the monograph.

The selected fragment retains the C-style implication and universal
constructors rather than implementing every logical constant in the full
Hahn-Richter language. It has no primitive equality, choice operator,
combinator basis, tense or full PTQ translation. The statement in the book
that the approaches have the same expressive power is a source statement,
not a theorem mechanically proved by this checkpoint.

## Typed syntax and interpretation

`Ty2Syntax.v` declares `we`, `wt`, `ws` and `warr`. Its terms have intrinsic
typing, de Bruijn variables, lexical constants, lambda, application,
implication and universal quantification. Worlds and individuals remain
different object types even when an example uses `bool` for both carriers.

`Ty2Models.v` interprets those types by:

```text
we        -> E
wt        -> bool
ws        -> W
warr a b  -> domain(a) -> domain(b)
```

E and W must both be inhabited. The entity domain and all higher-order
domains are constant across worlds. Function domains are full Coq function
spaces, not an unproved identification with an external set universe.
Quantifiers return Booleans and carry the same reflection obligation as
the extensional Boolean model: true exactly when every domain value passes.

`world_finite_model` constructs complete finite domains at every type from
finite data for E and W, with FunExt explicitly supplied for function-space
proofs. `world_decision_model` handles arbitrary inhabited E and W under an
explicit ClassicalDecision premise. Neither premise is imported globally.

There is no hidden current-world argument to `weval`. World dependence is
represented by terms of function type. For example:

- a sentence intension has type `s -> t`;
- an individual concept has type `s -> e`;
- a world-dependent noun extension can have type `s -> (e -> t)`;
- evaluating an intension at a world is typed function application.

Lexical constants denote fixed objects of their assigned types. A constant
of type `s -> e` denotes one function, whose values can differ across worlds.
That is different from a constant of type e whose denotation is fixed.

## Binding and the proof calculus

Renaming and simultaneous substitution are capture-avoiding operations on
the new typed terms. Their Boolean interpretation properties are proved in
`weval_rename`, `weval_substitution` and `weval_instantiate`. `wbeta_sound`
proves soundness of the explicit syntactic beta relation, including its
congruence cases. All these general semantic proofs take FunExt.

`Ty2Calculus.v` has its own seven C-style rule constructors, now quantifying
at world types as well as entity, truth and function types. The classical
rule remains indexed by the declared logical mode. `world_derivation_sound`
proves either mode sound for the new Boolean model class. A separate theorem
uses actual countermodels to exclude derivations.

These new proofs do not automatically transfer all checkpoint-2 structural
metatheorems to `wderives`. For example, arbitrary substitution of entire
Ty2 derivations is not separately proved here. Semantic substitution of
Ty2 terms and soundness of all its declared derivation constructors are proved.

## Necessity policy

The defined `necessarily p` is universal quantification over all worlds,
applied to a proposition intension p. `necessity_meaning` proves exactly that
interpretation. This is absolute necessity over W, with no accessibility
relation or varying-domain policy hidden inside it.

Instantiating a necessary proposition at a specified world is valid. The
example includes an object derivation and its semantic consequence theorem.
Conversely, an actual-world truth does not license deriving its necessity.
`no_necessitation_from_actual_assumption` excludes that derivation in either
mode by a two-world countermodel and the general soundness theorem.

There is no unrestricted necessitation rule from arbitrary local assumptions.
This does not deny standard necessitation of theorems in a suitable modal
calculus. No complete axiomatization of S5 or of another modal system is claimed.

## The extensional-core bridge

`embed_type` maps e, t and arrows into the corresponding world-language types.
`embed_term` maps all original term constructors and variables. A typed mapping
of source lexical constants to target lexical constants is an explicit input.

The two recursive domain interpreters are not silently treated as identical
Coq types. `value_maps` supplies forward and backward conversions. Their
round-trip identities are proved by induction on types, using FunExt for
function types. No equality-proof irrelevance or dependent-cast axiom is used.

For every world model, `core_reduct` supplies an extensional Boolean model
by converting the appropriate lexical values and quantifiers. The quantifier
reflection proof uses the domain conversions and their round trips. Then
`embedding_interpretation` proves that translated terms preserve their
denotations under related environments. The formula specialization relates
literal Boolean values directly.

`core_derivation_world_sound` uses this interpretation theorem and the earlier
Boolean soundness theorem to transport every existing C derivation's semantic
consequence to the translated formulas. The old instantiation and syllogism
examples exercise that general result without rewriting their original proofs.

Exact limitations of this bridge:

- It embeds the world-free core into the world-free part of Ty2. It does not
  automatically turn an old `e -> t` lexical constant into a varying
  `s -> (e -> t)` extension or provide a per-world lexical translation.
- It preserves term interpretation and semantic consequences of derivations.
  It is not yet a syntactic translation from `derives` proofs to `wderives`
  proofs, a conservativity theorem or a reverse implication.
- It is not a translation of the older IL syntax in `deep/PTQ_deep2.v`.

## Two-world regression cases

In the model `two_worlds`, E and W both have two elements. Actual denotes one
world and Alternative denotes the other. Weather is true only at Actual.
PersonConcept denotes John at Actual but a different individual at Alternative.
The rigid concept denotes John at both worlds. A simple predicate distinguishes
John from the other individual.

The checked observations are:

1. Weather is actually true and false at the alternative world.
2. Consequently Weather is not necessary.
3. The rigid and varying concepts agree at Actual but disagree at Alternative.
4. The predicate holds necessarily of the rigid concept, but not of the
   varying concept. Actual agreement does not justify that substitution.
5. Freezing the varying concept's actual value before abstracting over a
   world differs from evaluating the concept at the newly supplied world.
6. Typed world beta conversion and a capture-avoidance fixture behave as specified.
7. The full finite enumeration includes sixteen tables of type `s -> (e -> t)`.

The freezing example is a distinction between terms with different binding
and evaluation structure. It is not a counterexample to the proved Ty2 beta
theorem. There is no primitive implicit-index IL substitution operation in
this checkpoint whose correctness could be inferred from that theorem.

## Audit of the older IL implementation

The current `deep/PTQ_deep2.v` was inspected, including its types, environments
and complete interpreter. SHA256 at consultation:
`ee13df1359e47ca5856a3a35eacb9107beba145253a2f07c8fb39894477cd926`.
It was not edited or imported into this separately assumption-audited workbench.
It has global domain/lexical parameters and classical imports; importing it
would change the assumption boundary rather than constitute a proved bridge.

| Older IL clause | New Ty2 counterpart | Remaining obligation |
| --- | --- | --- |
| Intension type `Index -> Den a`, with `Index = World * Time` | Explicit `s -> a` | Specify a no-tense or fixed-time fragment, or explicitly retain the full index type. |
| `eval term env index` | `weval` of a world-explicit term | Define a syntax translation with an explicit current-world variable and prove interpretation preservation. |
| `up` abstracts over a new index while keeping the environment | Lambda over an explicit index/world variable | Prove the translated treatment of free variables, rigidity and substitution. |
| `down` applies an intension to the current index | Typed application to the explicit world | Translate the argument and distinguish index-varying expressions from fixed assignments. |
| `nec_` quantifies over worlds while holding time fixed | Absolute universal world quantification | State the fixed-time restriction; the present world-only calculus has no tense. |
| Truth and primitive equality interpreted in Coq Prop | Boolean truth; no new primitive Ty2 equality | Supply a justified truth/equality bridge or a parallel Prop-valued target interpretation. |

Thus there is an identifiable route to a connection, not a completed legacy
IL-to-Ty2 theorem. In particular, the existing C-to-Ty2 result must not be
presented as Gallin equivalence or as a translation of the complete legacy
PTQ implementation.

## Subsequent bounded milestone

Checkpoint 5 now specifies a world-only Boolean IL fragment and proves its
explicit-world interpretation preservation. It excludes primitive equality
and tense; see `IL_SPEC.md` for constants, assignments and index rigidity.
The relation to the actual legacy implementation still needs a theorem,
not an inference from similar constructor names. In particular, omitting
tense does not remove time dependence of old intensions and assignments.
Henkin closure/completeness, external set-model adequacy and source-level
fidelity review remain separate tracks.

No atlas grades, existing corpus Coq files, deployed reader or live worker
are changed by this checkpoint.
