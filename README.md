# MPSL

MPSL is an intrinsically typed DSL embedded in Lean for proving higher-order,
step-indexed separation-logic entailments. Assertions use a fixed exclusive
location-to-value heap with direct points-to ownership. MPSL has no generic
ghost-resource interface and no program-verification layer.

The implementation includes:

- a typed assertion language with products, sums, functions, quantifiers,
  equality, BI connectives, `□`, `▷`, and `↦`;
- ordered families of equivalences and bundled non-expansive functions;
- a downward-closed, step-indexed semantic model over partial heaps;
- proved affine BI, modal, equality, quantifier, and points-to laws;
- a sound named proof mode with persistent and spatial contexts;
- Iris-style proof-state rendering in Lean's InfoView.

## Quick start

```lean
import MPSL

open MPSL
open scoped MPSL

def assertion : Formula Nat String :=
  mpsl{ ∀ l : loc, ∀ v : val, □ True ⇒ ▷ (l ↦ v) }

example (P Q : Formula Nat String) :
    mpsl{ `P ∗ `Q } ⊢ mpsl{ `Q ∗ `P } := by
  mintro h
  mdestruct h as hP hQ
  msep [hQ]
  · mexact hQ
  · mexact hP
```

`mpsl{...}` elaborates directly into the intrinsically typed AST. The
backtick embeds an existing closed formula. Canonical surface spellings
include `𝟘`, `𝟙`, `×`, `→`, `λ`, `∀`, `∃`, `↦`, `∧`, `∨`, `∗`, `-∗`, `□`, and
`▷`.

The proof mode keeps Lean variables and pure propositions in Lean's local
context, reusable object-logic hypotheses in a persistent zone, and owned
resources in a spatial zone. Every tactic applies a proved semantic rule and
produces a proof term checked by Lean's kernel.

## Build

The repository uses the Lean toolchain selected by `lean-toolchain`.

```sh
lake build
```

The default build checks the library plus elaboration, semantics, and
pretty-print regression suites. Individual targets are:

```sh
lake build MPSLElabTests
lake build MPSLSemanticsTests
lake build MPSLPrettyPrintTests
```

## Documentation

- [Proof mode and complete tactic reference](docs/proof-mode.md)
- [Language and semantic model](docs/language.md)
- [Architecture and internals](docs/internals.md)

## Scope

MPSL intentionally omits program syntax, weakest preconditions, Hoare logic,
generic resource algebras, ghost state, `Own`, view shifts, fancy updates,
invariants, guarded recursion, and Löb induction.
