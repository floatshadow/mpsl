# MPSL Internals

This document describes the implemented architecture of MPSL. It is intended
for maintainers adding syntax, semantic laws, or proof tactics. User-facing
syntax and tactics are documented in [Language](language.md) and
[Proof mode](proof-mode.md).

## Design goals

MPSL is a small entailment prover for a fixed step-indexed separation logic.
Its architecture is shaped by four constraints:

1. malformed object-language expressions must be rejected before they reach
   the semantic layer;
2. higher-order values must respect indexed equivalence;
3. every proof-mode context transformation must have a semantic soundness
   theorem;
4. tactic metaprogramming must produce ordinary proof terms checked by Lean's
   kernel.

The project deliberately has no abstraction for generic ghost resources,
resource algebras, program languages, or weakest preconditions. There is one
resource implementation: an exclusive location-to-value heap.

## Dependency structure

The principal dependency direction is:

```text
Heap ───────────────┐
                    v
OFE ──> SProp ──> IProp ──> Connectives
  \                           ^
   \                          |
    └─> Ty ──> Expr ──> Denote
                ^          ^
                |          |
              Elab      ProofMode.Context
                             |
                             v
                      ProofMode.Rules
                             |
                             v
                      ProofMode.Tactics

Expr + Context ─────────> ProofMode.Pretty
```

Dependencies point toward definitions and theorems required by the consumer.
The semantic layer does not import the DSL frontend or tactics. The tactic
layer does not define logical truth. Pretty-printing observes syntax and proof
contexts but contributes no proof rule.

## Module map

| Module | Interface and responsibility |
| --- | --- |
| [`Heap.lean`](../MPSL/Heap.lean) | Partial heaps, subheap inclusion, disjointness, union, singleton ownership, and heap laws |
| [`OFE.lean`](../MPSL/Semantics/OFE.lean) | Indexed equivalence, bundled carriers, and non-expansive function spaces |
| [`SProp.lean`](../MPSL/Semantics/SProp.lean) | Downward-closed step propositions and finite-observation equality |
| [`IProp.lean`](../MPSL/Semantics/IProp.lean) | Heap-monotone assertions, semantic entailment, and assertion OFE |
| [`Connectives.lean`](../MPSL/Semantics/Connectives.lean) | Logical, separating, quantifier, modal, equality, and points-to semantics and laws |
| [`Ty.lean`](../MPSL/Syntax/Ty.lean) | Object-language type codes |
| [`Expr.lean`](../MPSL/Syntax/Expr.lean) | Intrinsically typed variables and expressions |
| [`Denote.lean`](../MPSL/Syntax/Denote.lean) | OFE interpretation of types, typed environments, and non-expansive expression denotation |
| [`Elab.lean`](../MPSL/Elab.lean) | `mpsl{...}` parser, type-directed elaboration, binders, and diagnostics |
| [`Context.lean`](../MPSL/ProofMode/Context.lean) | Named persistent/spatial contexts, structural operations, denotation, and soundness |
| [`Rules.lean`](../MPSL/ProofMode/Rules.lean) | Kernel-checked inference rules over structured proof states |
| [`Tactics.lean`](../MPSL/ProofMode/Tactics.lean) | Public tactic syntax, name checks, matching, and rule application |
| [`Pretty.lean`](../MPSL/ProofMode/Pretty.lean) | Reconstruction of DSL syntax and Iris-style proof-state rendering |

`MPSL.lean` is the public import facade. It exports elaboration, formula
denotation, proof tactics, and pretty-printing.

## Semantic foundation

### Heap resources

`Heap Loc Val` is `Loc -> Option Val`. `Heap.Subheap` is the resource-extension
order. `Heap.Disjoint` and `Heap.union` provide composition for separating
connectives. The heap OFE is discrete, so step indexing affects logical
observations rather than heap identity.

Points-to owns a singleton subheap. Ownership is exclusive because two
singletons at the same location cannot occur in disjoint fragments. Heap
monotonicity makes the logic affine: assertions may ignore extra owned cells.

### Ordered families of equivalences

`OFE` packages indexed equivalence, its equivalence laws, monotonicity toward
smaller indices, and the principle that equivalence at every index yields Lean
equality. `NEFun A B` packages a function with its non-expansiveness proof.

Object-language arrows denote `NEFun`, not arbitrary Lean functions. This is
the key higher-order invariant: functions cannot distinguish inputs beyond the
current observation index.

The project has no completeness or contractiveness interface because no
implemented feature consumes limits or fixed points.

### Step propositions and assertions

`SProp` stores a downward-closed predicate `Nat -> Prop`. Its OFE observes two
predicates only through a bounded step. `IProp Loc Val` maps a heap to `SProp`
and proves monotonicity under `Heap.Subheap`.

`IProp.Entails P Q` is semantic inclusion at every heap and observation step.
All connective laws eventually reduce to this relation. The proof mode never
introduces a second notion of logical consequence.

`Connectives.lean` is the semantic center of the project. It defines the
assertion constructors and proves their non-expansiveness and inference laws.
Higher layers should reuse these laws instead of unfolding `IProp.holds`.

## Typed object language

`Ty` is the closed universe of DSL types. `Var Γ τ` is a typed de Bruijn
variable, and `Expr Loc Val Γ τ` is an expression whose object type is tracked
by Lean. `Formula Loc Val` is the closed `iProp` fragment.

This indexing localizes type safety in the constructors:

- application fixes the argument type from the function index;
- equality compares terms at one declared type;
- points-to accepts only `loc` and `val`;
- quantifier and lambda bodies extend the context at the binder type;
- formula connectives return only `iProp`.

`Ty.model` gives every object type a semantic carrier and OFE. `Env` mirrors a
type context with semantic values. `Expr.denoteNE` interprets every expression
as a non-expansive function from its environment to its result carrier.

Closed embedding is explicit. `Expr.embed` places a closed typed expression
under binders without adding a general substitution mechanism.

## Elaboration

The frontend is a dedicated elaborator, not a family of notation macros. It
performs one pass over `mpslTerm` syntax while maintaining a list of typed
bindings:

```text
surface syntax
  -> parse MPSL type and term categories
  -> resolve names to typed de Bruijn variables
  -> check each constructor's object type
  -> construct Expr Loc Val [] τ
```

Lean values can cross the language seam only through `loc(...)`, `val(...)`,
formula antiquotation, and explicitly typed closed expression embedding. This
keeps host elaboration available without allowing arbitrary Lean terms to
bypass DSL typing.

Elaboration errors should use DSL types and source syntax. Constructor names,
unification metavariables, and denotation terms are implementation details.

## Proof mode

The proof mode represents object-logic assumptions as two flat named lists:

```text
Γp : persistent assertions
Γs : spatial assertions
R  : current assertion goal
```

Lean's local context remains the pure context. The MPSL context denotes:

```text
□(andDenote Γp) ∗ sepDenote Γs
```

Names do not affect denotation, but they are the stable interface used by
tactics. The tactic layer maintains uniqueness across both lists.

The flat representation is intentional. A compound assertion remains one
named hypothesis until an elimination rule replaces it. Spatial separation is
represented by the fold of the spatial list, while persistent reuse follows
from the boxed additive fold.

### Context operations

`Context` provides lookup, replacement, extraction, ordered multi-extraction,
spatial partitioning, and movement into the persistent list. Each operation is
paired with a theorem relating the old and new denotations.

The computation returns an `Option` and a rule receives the successful result
as an explicit equation. A `by rfl` witness confirms that the requested names
and shape were actually found; the companion theorem proves the semantic
consequence.

### Rule theorems

`Rules.lean` is the soundness seam. It combines context-operation theorems with
semantic connective laws to implement introduction, elimination, framing,
quantifiers, equality, and modalities.

Löb induction is certified at two levels. `IProp.lob` proves the object-logic
law by induction on the step index. The proof-mode rule keeps persistent
assumptions in place, generalizes a nonempty spatial environment as
`Γs −∗ R`, installs its later as the persistent induction hypothesis, and
restores the named spatial hypotheses. The empty-spatial specialization uses
`▷ R` directly. This prevents the induction hypothesis from duplicating owned
resources.

Rule theorems retain raw contexts until the proof is complete. Folding the
context too early would erase names and zones. Semantically, however, every
rule proves ordinary `IProp.Entails`; the structured state adds bookkeeping,
not a new logic.

### Tactic implementation

Most tactics are macros expanding to `apply` or `exact` with a rule theorem.
The small meta-programmed part enforces unique names and implements
definitionally checked `massumption`.

Tactic code may inspect reducible context expressions and build theorem
applications. It must not unfold heap satisfaction to synthesize a proof,
introduce axioms, or use `sorry`. A successful tactic invocation leaves a
normal Lean proof term for the kernel to check.

## Pretty-printing

Lean prints pure variables and propositions itself. `Pretty.lean` delaborates
the structured target into persistent hypotheses, a `☐` divider, spatial
hypotheses, a `∗` divider, and the DSL goal.

The printer traverses raw context lists rather than their semantic folds. This
preserves one named hypothesis per line. It performs narrow normalization of
proof-mode record projections and list operations, but avoids broad reduction
that would expose heap predicates.

Open quantifier goals require reconstructing DSL variables from semantic
environments. Standalone persistence certificates have a separate display
path as semantic entailments.

Pretty-printing is presentation only. Failure to delaborate must fall back to
Lean's ordinary printer and cannot affect proof soundness.

## Soundness and trust

The trusted foundation is Lean's kernel plus the definitions in the semantic
model. The architecture limits the role of tactics:

```text
tactic syntax
  -> context computation
  -> application of a proved rule theorem
  -> ordinary Lean subgoals
  -> kernel-checked proof term
```

Context algorithms are not trusted merely because they compute. Their result
equations feed separately proved denotational theorems. Pretty-printing and
diagnostics are outside the proof path.

The project should contain no declaration depending on `sorryAx`. Negative
tests are part of the soundness envelope: they check that spatial contraction,
invalid `□` introduction, and duplicate names are rejected.

## Extension workflows

### Add a DSL constructor

1. Add its type-indexed constructor to `Expr`.
2. Add surface syntax and type checking in `Elab`.
3. Define its semantic connective or value interpretation.
4. Extend `Expr.denoteNE` and prove non-expansiveness.
5. Extend pretty-print reconstruction.
6. Add positive and negative elaboration tests.

### Add a semantic law

1. State it as `IProp.Entails` or two entailments for equivalence.
2. Prove it from connective and heap definitions in the semantic layer.
3. Avoid dependencies on syntax, elaboration, or tactics.
4. Add a semantic regression test.

### Add a proof tactic

1. Reuse an existing semantic law or prove the missing one.
2. Express the context change with existing operations where possible.
3. Add and prove a context operation only when the existing interface cannot
   express the transformation.
4. Add a rule theorem with every computed equation explicit.
5. Add the smallest macro or elaborator that applies that theorem.
6. Test a successful proof and a resource-invalid rejection.
7. Add a pretty-print snapshot for any new context shape or side goal.

These dependency orders keep the modules deep: callers gain behavior through
small interfaces, while semantic complexity remains local to the layer that
owns it.

## Tests and build

The default `lake build` checks:

- `MPSLElabTests`: grammar, typing, and AST construction;
- `MPSLSemanticsTests`: semantic laws, proof-mode behavior, and negative
  resource-safety cases;
- `MPSLPrettyPrintTests`: stable user-facing rendering and absence of internal
  denotation terms.

Test support in `MPSLTest` supplies concrete locations and values plus
pretty-print assertions. It is not imported by the library facade.

## Deliberate omissions

MPSL does not include:

- program syntax, operational semantics, weakest preconditions, or Hoare
  triples;
- generic resource algebras, ownership terms, ghost state, or updates;
- invariants or view shifts;
- fractional points-to permissions;
- recursive predicates, guarded recursion, completeness, contractiveness, or
  fixed-point operators;
- automatic frame selection or unrestricted spatial contraction.
