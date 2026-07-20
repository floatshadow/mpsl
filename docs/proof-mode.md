# MPSL Proof Mode

MPSL proof mode proves entailments between closed formulas of the embedded
separation logic:

```lean
P ⊢ Q
```

It is an entailment prover, not a program-verification framework. There are no
program states, weakest preconditions, Hoare triples, ghost resources, or
invariants. Spatial ownership is limited to the fixed exclusive points-to
resource `l ↦ v`.

## Getting started

Import `MPSL`, open the namespace and scoped notation, then use `mintro` to
name the left side of an entailment:

```lean
import MPSL

open MPSL
open scoped MPSL

example (P Q : Formula Nat String) :
    mpsl{ `P ∗ `Q } ⊢ mpsl{ `Q ∗ `P } := by
  mintro h
  mdestruct h as hP hQ
  msep [hQ]
  · mexact hQ
  · mexact hP
```

The backtick in `` `P `` embeds a closed `Formula` into a larger DSL term.
The outer `mpsl{...}` elaborates the typed object-language syntax.

## Proof state

The InfoView presents three contexts:

```text
x : Nat
hEq : x = x
⊢
hSpec : □ `P
──────────────────────────────────────☐
hCell : (loc(0) ↦ val("value"))
──────────────────────────────────────∗
(`P ∗ (loc(0) ↦ val("value")))
```

Lean variables and ordinary Lean propositions form the pure context above
`⊢`. MPSL persistent hypotheses appear above the `☐` divider and may be reused.
Spatial hypotheses appear above the `∗` divider and must be partitioned when
proving a separating conjunction.

Hypothesis names are unique across both MPSL zones. A tactic that would create
a duplicate name fails with:

```text
duplicate proof-mode hypothesis name 'h'
```

The logic is affine: either kind of hypothesis may be discarded with
`mclear`, but a spatial hypothesis may not be copied.

## Introducing assumptions

### `mintro h`

At the start of `P ⊢ Q`, `mintro h` enters proof mode and adds `h : P` to the
spatial zone. On a goal `P -∗ Q`, it introduces `P` spatially. On `P ⇒ Q`, it
introduces `P` spatially only when the existing spatial zone is empty.

```lean
example (P Q : Formula Nat String) :
    P ⊢ mpsl{ `Q -∗ (`P ∗ `Q) } := by
  mintro hP
  mintro hQ
  msep [hP]
  · mexact hP
  · mexact hQ
```

### `mintro #h`

On `P ⇒ Q`, `mintro #h` puts `h : P` in the persistent zone. It first creates
a side goal certifying `P ⊢ᵢ □ P`; the continuation is the second goal. This
form can retain an existing spatial context.

### `mpersistent h`

`mpersistent h` moves a spatial hypothesis `h : P` into the persistent zone.
It creates two goals, in this order:

1. prove the persistence certificate `P ⊢ᵢ □ P`;
2. continue with `h` in the persistent zone.

For `h : □ P`, the certificate is the standard idempotence law:

```lean
mpersistent h
· exact IProp.always_idem_intro _
· -- h is persistent here
```

## Closing goals

| Tactic | Effect |
| --- | --- |
| `mexact h` | Close the goal with the named, definitionally equal hypothesis. |
| `massumption` | Close with the first definitionally matching hypothesis, searching persistent then spatial. |
| `mtruth` | Prove `True`. Unused hypotheses are discarded affinely. |
| `mfalse h` | Close any goal from a named `False` hypothesis. |
| `mrefl` | Prove object-language equality by reflexivity. |
| `msymm h` | Prove `y =[τ] x` from named `x =[τ] y`. |
| `mtrans h1 h2` | Prove `x =[τ] z` from named `x =[τ] y` and `y =[τ] z`. |

`mexact` is deterministic and should be preferred when the intended
hypothesis is known. `massumption` is conservative: it uses definitional
equality only and performs no logical search.

## Additive connectives

### `msplit`

On `P ∧ Q`, `msplit` creates goals for `P` and `Q`. Both goals receive the
entire persistent and spatial context because conjunction is additive.

### `mleft` and `mright`

On `P ∨ Q`, `mleft` selects `P` and `mright` selects `Q`.

### `mdestruct h as h1 h2`

This named elimination form handles several connectives:

- spatial `P ∗ Q`: replace `h` by spatial `h1 : P` and `h2 : Q`;
- persistent `P ∗ Q`: replace `h` by two persistent hypotheses;
- persistent `P ∧ Q`: replace `h` by two persistent hypotheses;
- `P ∨ Q` in either zone: create one goal with `h1 : P` and one with
  `h2 : Q`, preserving the source zone.

A spatial `P ∧ Q` cannot be turned into two spatial hypotheses because that
would duplicate its resource. Use one of the persistent-conjunct forms:

```lean
mdestruct h as #hP hQ  -- certify P persistent; keep Q spatial
mdestruct h as hP #hQ  -- keep P spatial; certify Q persistent
```

Each form first creates the corresponding persistence certificate and then
continues with the marked conjunct in the persistent zone.

## Separating conjunction

### `msep [h1, ..., hn]`

On `P ∗ Q`, the listed spatial hypotheses are assigned to the left goal. All
remaining spatial hypotheses are assigned to the right goal. Persistent
hypotheses are available in both goals. `msep []` gives the entire spatial
zone to the right goal.

Names may be selected in any order. Each name must exist and can occur only
once; a spatial hypothesis cannot appear in both partitions.

### `msepR [h1, ..., hn]`

This is the symmetric partition form: the listed spatial hypotheses go to the
right goal and the remainder goes to the left. Goals are still presented in
left-to-right order.

### `msep`

The argument-free form certifies the left operand as persistent, then proves
both operands using the full context. It creates the left operand's
persistence-certificate goal followed by the two connective goals. It does
not search for a persistent operand. For ordinary spatial splits, prefer an
explicit `msep [...]` or `msepR [...]` partition.

## Applying and framing

### `mapply hf ha`

Close the current goal by applying a named `P ⇒ Q` or `P -∗ Q` hypothesis
`hf` to a named premise `ha : P`. Implication uses hypotheses through the
additive context. Wand application extracts the wand and premise as spatial
resources. Any unused resources may be discarded because the logic is affine.

### `mframe h`

On `P ∗ Q`, extract the explicitly named hypothesis and match it against the
left or right operand. The remaining context is used for the other operand.
There is no automatic choice of a frame.

### `mframe [h1, ..., hn]`

Extract a nonempty ordered list of hypotheses and combine their assertions
with `∗` as one left frame. This supports non-adjacent selections such as
`[hP, hR]`. Persistent hypotheses are reusable; extracted spatial hypotheses
are removed from the continuation.

## Quantifiers

Object-logic quantifiers range over Lean values denoting a DSL type. The
quantifier itself remains an MPSL proposition and does not split resources.

### `mforall x`

On `∀ x : τ, Φ x`, introduce an arbitrary Lean variable `x` and prove
`Φ x` with the same MPSL context.

### `mexists witness` and `mexists $! witness`

On `∃ x : τ, Φ x`, choose a witness. The first form accepts a DSL term such as
`loc(0)`. The `$!` form injects a value from Lean's pure context.

```lean
mforall y
mexists $! y
```

### `mopenexists h as x hx`

Eliminate a named existential. It introduces a fresh Lean witness `x` and
replaces `h : ∃ x, Φ x` with `hx : Φ x` in the same MPSL zone.

### `mspecialize h at witness as ht`

Instantiate `h : ∀ x, Φ x` and name the result `ht`. A spatial universal is
replaced by its instance. A persistent universal is retained and the instance
is added persistently. Use `at $! value` for a witness from Lean's pure
context.

## Modalities

| Tactic | Effect |
| --- | --- |
| `malways` | Change `□ P` to `P`; requires an empty spatial zone. Persistent hypotheses remain available. |
| `mopen h as hP` | Replace persistent `h : □ P` with persistent `hP : P`. Move a spatial boxed hypothesis first with `mpersistent`. |
| `mlater` | Change `▷ P` to `P` using later introduction. The context is unchanged. |
| `mopenlater h as hP` | On goal `▷ Q`, replace spatial `h : ▷ P` with spatial `hP : P` and prove `Q` under later monotonicity. |

There is no Löb induction, guarded fixed point, or general rule for stripping
`▷` from an arbitrary hypothesis and unguarded goal.

## Structural and low-level tactics

| Tactic | Effect |
| --- | --- |
| `mclear h` | Affinely discard a named persistent or spatial hypothesis. |
| `mnormalize` | Unfold the proof-mode context and DSL denotation with a fixed simplification set. This is a low-level escape hatch, not proof search. |
| `mstop` | Leave the structured proof state and expose the underlying semantic entailment. MPSL tactics no longer apply afterward. |

## Resource-safety rules

The following are intentionally rejected:

- assigning one spatial points-to hypothesis to both `msep` branches;
- destructing spatial `P ∧ Q` into two spatial hypotheses;
- proving `□ P` while spatial resources remain;
- moving `P` into the persistent zone without proving `P ⊢ᵢ □ P`;
- creating duplicate hypothesis names.

These are logical restrictions, not tactic limitations. Each successful
tactic constructs a proof from sound semantic rules, and Lean's kernel checks
the resulting term.
