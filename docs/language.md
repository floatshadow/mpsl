# MPSL Assertion Language

This document specifies the implemented MPSL object language and its semantic
interpretation. For using entailment tactics, see the current
[proof-mode guide](proof-mode.md).

## Scope

MPSL is an embedded DSL in Lean for stating and proving separation-logic
entailments. It is higher-order: formulas are values of type `iProp`, functions
may accept and return formulas, and quantifiers may range over any DSL type.
It is step-indexed: every proposition denotes a downward-closed set of natural
number observations and the logic includes `▷`.

The only spatial resource is an exclusive partial heap from locations to
values. The language has no programs, weakest preconditions, Hoare triples,
generic resource algebras, ghost ownership, view shifts, invariants, recursive
terms, or guarded fixed points.

## Surface syntax

Types are:

```text
τ ::= loc | val | iProp | 𝟘 | 𝟙
    | τ × τ | τ + τ | τ → τ
```

Terms and formulas share one typed syntax category:

```text
t, u, P, Q ::=
    x
  | loc(leanTerm) | val(leanTerm)
  | `leanFormula | embed[τ](closedDslExpr)
  | ()
  | λ x : τ, t | t(u)
  | (t, u) | fst t | snd t
  | inl[τ](t) | inr[τ](t)
  | case t of | inl x => u | inr y => v
  | False | True
  | t =[τ] u | eq[τ](t, u)
  | P ⇒ Q | P ∧ Q | P ∨ Q
  | P ∗ Q | P -∗ Q
  | ∀ x : τ, P | ∃ x : τ, P
  | t ↦ u
  | □ P | ▷ P
```

Canonical spellings are Unicode. The parser also accepts these ASCII forms:

| Canonical | ASCII |
| --- | --- |
| `𝟘`, `𝟙` | `0`, `1` |
| `τ → σ` | `τ -> σ` |
| `λ x : τ, t` | `fun x : τ => t` |
| `∀`, `∃` | `forall`, `exists` |
| `P ⇒ Q` | `P -> Q` |
| `P ∧ Q`, `P ∨ Q` | `P /\ Q`, `P \/ Q` |
| `P ∗ Q`, `P -∗ Q` | `P * Q`, `P -* Q` |
| `l ↦ v` | `l |-> v` |
| `□ P`, `▷ P` | `always P`, `later P` |

Product types use `×`; `*` is reserved for separating conjunction. Sum
injections carry the missing summand type: `inl[σ](t)` and `inr[τ](u)`.

`loc` and `val` are distinct object-language types even when a project chooses
the same Lean carrier for both. This makes the type of points-to precise:

```text
Γ ⊢ l : loc       Γ ⊢ v : val
--------------------------------
Γ ⊢ l ↦ v : iProp
```

## Lean embedding

The dedicated term form `mpsl{...}` runs the MPSL parser and elaborator:

```lean
import MPSL

open MPSL

def higherOrder : Formula Nat String :=
  mpsl{ (λ P : iProp, P ∗ P)(True) }

def product : Formula Nat String :=
  mpsl{ (loc(0), val("zero")) =[loc × val]
    (loc(0), val("zero")) }
```

Lean terms enter the DSL only at explicit embedding sites:

- `loc(e)` embeds `e : Loc` at DSL type `loc`;
- `val(e)` embeds `e : Val` at DSL type `val`;
- `` `P `` embeds a closed `Formula Loc Val` at `iProp`;
- `embed[τ](e)` embeds an already constructed closed `Expr Loc Val [] τ`.

The general `embed[τ]` constructor weakens a closed expression beneath DSL
binders. It is not an escape from intrinsic typing: Lean still checks the
embedded expression's indexed `Expr` type.

The elaborator maintains a typed binder context, resolves identifiers to de
Bruijn variables, and reports mismatched object types before constructing the
AST. `mpsl{...}` may produce any closed DSL expression when the expected Lean
type is sufficiently specific; `Formula Loc Val` requires result type `iProp`.

## Intrinsically typed syntax

The core type index is:

```lean
inductive Ty where
  | loc | val | iprop | empty | unit
  | prod (left right : Ty)
  | sum (left right : Ty)
  | arr (domain codomain : Ty)
```

Variables and expressions are indexed by an object-language context and result
type:

```lean
inductive Var : List Ty -> Ty -> Type

inductive Expr (Loc Val) : List Ty -> Ty -> Type

abbrev Formula (Loc Val) := Expr Loc Val [] .iprop
```

Every constructor preserves its indices. For example, application requires an
argument matching the function domain; equality requires two terms of its
declared type; quantifier bodies extend the context; points-to requires `loc`
and `val`. Once elaboration succeeds, an ill-typed formula cannot be
represented.

The current syntax module does not expose a general weakening, substitution,
or beta-normalization interface. `Expr.embed` handles the implemented use case
of placing a closed expression under binders.

## OFE interpretation of types

An ordered family of equivalences supplies an indexed relation `x =ₙ y` with:

- reflexivity, symmetry, and transitivity at each step;
- monotonicity from a larger observation index to a smaller one;
- ordinary equality when values are equivalent at every step.

`Ty.model Loc Val τ` bundles the Lean carrier and its OFE:

```text
⟦loc⟧, ⟦val⟧       lifted discrete host types
⟦𝟘⟧, ⟦𝟙⟧          lifted Empty and Unit
⟦τ × σ⟧            product OFE
⟦τ + σ⟧            sum OFE
⟦τ → σ⟧            bundled non-expansive functions
⟦iProp⟧            step-indexed assertions
```

Arrow values are `NEFun`, not arbitrary Lean functions. A function must prove
that equivalent inputs at step `n` produce equivalent outputs at step `n`.
This restriction is essential when a function consumes `iProp`: an arbitrary
function could inspect more of an assertion than the current index permits.

There is no completeness or contractiveness class. No implemented feature
uses limits, recursive predicates, or a fixed-point theorem.

## Environments and expression denotation

`Env Loc Val Γ` is an intrinsically typed list of semantic values matching
`Γ`. Its OFE is pointwise. Every expression denotes a bundled non-expansive
map:

```lean
Expr.denoteNE : Expr Loc Val Γ τ -> NEFun (Env Loc Val Γ) ⟦τ⟧
```

The interpreter is total by structural recursion over `Expr`. Variables read
their indexed environment position, lambdas produce `NEFun`, application uses
the bundled function, and formula constructors call their semantic `IProp`
connectives. `Expr.denote_nonexpansive` exposes the non-expansiveness property
without requiring callers to inspect the interpreter.

A closed formula is evaluated in `Env.nil`:

```lean
Formula.denote : Formula Loc Val -> IProp Loc Val
```

## Heap model

The resource model is a partial heap:

```lean
abbrev Heap (Loc Val : Type) := Loc -> Option Val
```

The semantic operations are:

- `Heap.empty`;
- `Heap.singleton l v`, requiring `DecidableEq Loc`;
- `Heap.Subheap h₁ h₂`, meaning every binding of `h₁` occurs unchanged in
  `h₂`;
- `Heap.Disjoint h₁ h₂`, meaning no location is defined in both;
- left-biased `Heap.union h₁ h₂`, whose bias is unobservable for disjoint
  heaps.

Heaps use the discrete OFE: indexed equivalence is ordinary function equality
at every step. The representation admits infinite partial heaps; finiteness is
not observable in the logic.

Points-to is full and exclusive. It holds when the singleton heap is a subheap
of the owned heap:

```text
n ∈ ⟦l ↦ v⟧(h)  iff  singleton ⟦l⟧ ⟦v⟧ ⊑ h
```

Two points-to assertions for the same location cannot inhabit disjoint heap
fragments, yielding `(l ↦ v₁) ∗ (l ↦ v₂) ⊢ᵢ False`.

## Step propositions

A step proposition is a downward-closed predicate on natural numbers:

```lean
structure SProp where
  steps : Nat -> Prop
  downward : smaller <= larger -> steps larger -> steps smaller
```

Membership `n ∈ P` means that `P` is observable for `n` steps. Indexed
equivalence is agreement at every observation no larger than `n`:

```text
P =ₙ Q  iff  ∀ m <= n, (m ∈ P ↔ m ∈ Q)
```

`SProp.bottom`, `top`, `conj`, `disj`, and `later` preserve downward closure.
The later proposition holds at step zero and shifts positive observations by
one.

## Assertions and entailment

An assertion maps owned heaps to step propositions and is monotone under heap
extension:

```lean
structure IProp (Loc Val) where
  holds : Heap Loc Val -> SProp
  monotone : h₁ ⊑ h₂ -> n ∈ holds h₁ -> n ∈ holds h₂
```

The heap OFE is discrete, so `IProp.holds_nonexpansive` proves this map
non-expansive without storing another function wrapper. Assertions themselves
form an OFE by pointwise step-proposition equivalence.

Semantic entailment is inclusion at every heap and step:

```text
P ⊢ᵢ Q  iff  ∀ h n, n ∈ P(h) -> n ∈ Q(h)
```

Formula entailment `P ⊢ Q` abbreviates entailment between the denotations of
two closed formulas.

Monotonicity makes the logic affine: an assertion may ignore extra owned
cells. Resources can therefore be discarded, but exclusive cells cannot be
duplicated.

## Connective denotations

For a heap `h` and observation step `n`:

```text
⟦False⟧(h) = bottom
⟦True⟧(h)  = top

n ∈ ⟦t =[τ] u⟧(h)
  iff ⟦t⟧ =ₙ ⟦u⟧ in the OFE for τ

n ∈ ⟦P ∧ Q⟧(h)
  iff n ∈ ⟦P⟧(h) and n ∈ ⟦Q⟧(h)

n ∈ ⟦P ∨ Q⟧(h)
  iff n ∈ ⟦P⟧(h) or n ∈ ⟦Q⟧(h)

n ∈ ⟦P ⇒ Q⟧(h)
  iff for every m <= n and h ⊑ h',
      m ∈ ⟦P⟧(h') implies m ∈ ⟦Q⟧(h')

n ∈ ⟦P ∗ Q⟧(h)
  iff there are disjoint h₁ and h₂ with h₁ ∪ h₂ = h,
      n ∈ ⟦P⟧(h₁), and n ∈ ⟦Q⟧(h₂)

n ∈ ⟦P -∗ Q⟧(h)
  iff for every m <= n and h' disjoint from h,
      m ∈ ⟦P⟧(h') implies m ∈ ⟦Q⟧(h ∪ h')

n ∈ ⟦∃ x : τ, P⟧(h)
  iff there is x : ⟦τ⟧ with n ∈ ⟦P⟧(h)

n ∈ ⟦∀ x : τ, P⟧(h)
  iff every x : ⟦τ⟧ satisfies n ∈ ⟦P⟧(h)

n ∈ ⟦□ P⟧(h)
  iff n ∈ ⟦P⟧(empty)

n ∈ ⟦▷ P⟧(h)
  iff n = 0, or n = m + 1 and m ∈ ⟦P⟧(h)
```

`True` is also the separating unit in this affine model. The reverse unit law
uses heap monotonicity to absorb the fragment assigned to `True`.

`□ P` observes `P` on the empty heap, so it owns no spatial cell and can be
duplicated after persistence is certified. `▷` shifts only the logical index;
it does not represent execution of a program step.

All implemented constructors are proved non-expansive. Their BI, modal,
quantifier, equality, and points-to laws are proved in the semantic layer and
exercised by the semantic regression suite.

