import MPSL.Semantics.IProp

set_option autoImplicit false

namespace MPSL.IProp

open scoped Heap

universe u v w

variable {Loc : Type u} {Val : Type v}

def falsum : IProp Loc Val where
  holds := fun _ => SProp.bottom
  monotone := by simp [SProp.bottom]

def truth : IProp Loc Val where
  holds := fun _ => SProp.top
  monotone := by simp [SProp.top]

def and (left right : IProp Loc Val) : IProp Loc Val where
  holds := fun heap => SProp.conj (left.holds heap) (right.holds heap)
  monotone := by
    intro smaller larger included step holds
    exact ⟨left.monotone included holds.1, right.monotone included holds.2⟩

def or (left right : IProp Loc Val) : IProp Loc Val where
  holds := fun heap => SProp.disj (left.holds heap) (right.holds heap)
  monotone := by
    intro smaller larger included step holds
    cases holds with
    | inl leftHolds => exact Or.inl (left.monotone included leftHolds)
    | inr rightHolds => exact Or.inr (right.monotone included rightHolds)

def imp (left right : IProp Loc Val) : IProp Loc Val where
  holds := fun heap =>
    { steps := fun step => forall smaller, smaller <= step -> forall larger,
        Heap.Subheap heap larger ->
        smaller ∈ left.holds larger -> smaller ∈ right.holds larger
      downward := by
        intro smaller larger included holds observed observedIncluded
        exact holds observed (Nat.le_trans observedIncluded included) }
  monotone := by
    intro smallerHeap largerHeap heapsIncluded step holds
    intro smallerStep stepIncluded futureHeap futureIncluded
    exact holds smallerStep stepIncluded futureHeap
      (Heap.subheap_trans heapsIncluded futureIncluded)

def sep (left right : IProp Loc Val) : IProp Loc Val where
  holds := fun heap =>
    { steps := fun step => exists leftHeap rightHeap,
        Heap.Disjoint leftHeap rightHeap ∧
        Heap.union leftHeap rightHeap = heap ∧
        step ∈ left.holds leftHeap ∧
        step ∈ right.holds rightHeap
      downward := by
        intro smaller larger included holds
        obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
        exact ⟨leftHeap, rightHeap, disjoint, combined,
          left.holds leftHeap |>.downward included leftHolds,
          right.holds rightHeap |>.downward included rightHolds⟩ }
  monotone := by
    intro smallerHeap largerHeap included step holds
    obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
    obtain ⟨extendedLeft, extendedDisjoint, extendedCombined, leftIncluded⟩ :=
      Heap.extend_split disjoint combined included
    exact ⟨extendedLeft, rightHeap, extendedDisjoint, extendedCombined,
      left.monotone leftIncluded leftHolds, rightHolds⟩

def wand (left right : IProp Loc Val) : IProp Loc Val where
  holds := fun heap =>
    { steps := fun step => forall smaller, smaller <= step -> forall extra,
        Heap.Disjoint heap extra ->
        smaller ∈ left.holds extra ->
        smaller ∈ right.holds (Heap.union heap extra)
      downward := by
        intro smaller larger included holds observed observedIncluded
        exact holds observed (Nat.le_trans observedIncluded included) }
  monotone := by
    intro smallerHeap largerHeap heapsIncluded step holds
    intro smallerStep stepIncluded extra disjoint leftHolds
    have smallDisjoint : Heap.Disjoint smallerHeap extra := by
      intro location smallValue extraValue smallFound extraFound
      exact disjoint location smallValue extraValue
        (heapsIncluded location smallValue smallFound) extraFound
    have result := holds smallerStep stepIncluded extra smallDisjoint leftHolds
    exact right.monotone (Heap.union_mono_left heapsIncluded disjoint) result

def pointsTo [DecidableEq Loc] (location : Loc) (value : Val) : IProp Loc Val where
  holds := fun heap =>
    { steps := fun _ => Heap.Subheap (Heap.singleton location value) heap
      downward := by simp }
  monotone := by
    intro smaller larger included step holds
    exact Heap.subheap_trans holds included

def always (proposition : IProp Loc Val) : IProp Loc Val where
  holds := fun _ => proposition.holds Heap.empty
  monotone := by
    intro smaller larger included step holds
    exact holds

def later (proposition : IProp Loc Val) : IProp Loc Val where
  holds := fun heap => SProp.later (proposition.holds heap)
  monotone := by
    intro smaller larger included step holds
    cases holds with
    | inl zero => exact Or.inl zero
    | inr observed =>
        obtain ⟨previous, stepValue, previousHolds⟩ := observed
        exact Or.inr ⟨previous, stepValue, proposition.monotone included previousHolds⟩

-- OFE Carrier **without** equivAt_refl/symm/trans **nor** eq_of_equivAt
def equal {Carrier : Type w} (equivAt : Nat -> Carrier -> Carrier -> Prop)
    (equivAtMono : forall {smaller larger left right},
      smaller <= larger -> equivAt larger left right -> equivAt smaller left right)
    (left right : Carrier) : IProp Loc Val where
  holds := fun _ =>
    { steps := fun step => equivAt step left right
      downward := by
        intro smaller larger included equivalent
        exact equivAtMono included equivalent }
  monotone := by
    intro smaller larger included step equivalent
    exact equivalent

def exists_ {Witness : Type w} (body : Witness -> IProp Loc Val) : IProp Loc Val where
  holds := fun heap =>
    { steps := fun step => exists witness, step ∈ (body witness).holds heap
      downward := by
        intro smaller larger included holds
        obtain ⟨witness, witnessHolds⟩ := holds
        exact ⟨witness, (body witness).holds heap |>.downward included witnessHolds⟩ }
  monotone := by
    intro smaller larger included step holds
    obtain ⟨witness, witnessHolds⟩ := holds
    exact ⟨witness, (body witness).monotone included witnessHolds⟩

def forall_ {Witness : Type w} (body : Witness -> IProp Loc Val) : IProp Loc Val where
  holds := fun heap =>
    { steps := fun step => forall witness, step ∈ (body witness).holds heap
      downward := by
        intro smaller larger included holds witness
        exact (body witness).holds heap |>.downward included (holds witness) }
  monotone := by
    intro smaller larger included step holds witness
    exact (body witness).monotone included (holds witness)

theorem and_nonexpansive : OFE.NonExpansive₂ (@and Loc Val) := by
  intro step left left' right right' leftEq rightEq heap observed included
  exact and_congr (leftEq heap observed included) (rightEq heap observed included)

theorem or_nonexpansive : OFE.NonExpansive₂ (@or Loc Val) := by
  intro step left left' right right' leftEq rightEq heap observed included
  exact or_congr (leftEq heap observed included) (rightEq heap observed included)

theorem imp_nonexpansive : OFE.NonExpansive₂ (@imp Loc Val) := by
  intro step left left' right right' leftEq rightEq heap observed observedIncluded
  constructor
  · intro holds smaller smallerIncluded larger heapIncluded leftHolds
    have withinStep : smaller <= step :=
      Nat.le_trans smallerIncluded observedIncluded
    apply (rightEq larger smaller withinStep).mp
    apply holds smaller smallerIncluded larger heapIncluded
    exact (leftEq larger smaller withinStep).mpr leftHolds
  · intro holds smaller smallerIncluded larger heapIncluded leftHolds
    have withinStep : smaller <= step :=
      Nat.le_trans smallerIncluded observedIncluded
    apply (rightEq larger smaller withinStep).mpr
    apply holds smaller smallerIncluded larger heapIncluded
    exact (leftEq larger smaller withinStep).mp leftHolds

theorem sep_nonexpansive : OFE.NonExpansive₂ (@sep Loc Val) := by
  intro step left left' right right' leftEq rightEq heap observed included
  constructor
  · rintro ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩
    exact ⟨leftHeap, rightHeap, disjoint, combined,
      (leftEq leftHeap observed included).mp leftHolds,
      (rightEq rightHeap observed included).mp rightHolds⟩
  · rintro ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩
    exact ⟨leftHeap, rightHeap, disjoint, combined,
      (leftEq leftHeap observed included).mpr leftHolds,
      (rightEq rightHeap observed included).mpr rightHolds⟩

theorem wand_nonexpansive : OFE.NonExpansive₂ (@wand Loc Val) := by
  intro step left left' right right' leftEq rightEq heap observed observedIncluded
  constructor
  · intro holds smaller smallerIncluded extra disjoint leftHolds
    have withinStep : smaller <= step :=
      Nat.le_trans smallerIncluded observedIncluded
    apply (rightEq (Heap.union heap extra) smaller withinStep).mp
    apply holds smaller smallerIncluded extra disjoint
    exact (leftEq extra smaller withinStep).mpr leftHolds
  · intro holds smaller smallerIncluded extra disjoint leftHolds
    have withinStep : smaller <= step :=
      Nat.le_trans smallerIncluded observedIncluded
    apply (rightEq (Heap.union heap extra) smaller withinStep).mpr
    apply holds smaller smallerIncluded extra disjoint
    exact (leftEq extra smaller withinStep).mp leftHolds

theorem always_nonexpansive : OFE.NonExpansive (@always Loc Val) := by
  intro step left right equivalent heap observed included
  exact equivalent Heap.empty observed included

theorem later_nonexpansive : OFE.NonExpansive (@later Loc Val) := by
  intro step left right equivalent heap observed included
  cases observed with
  | zero =>
      exact iff_of_true (SProp.zero_mem_later _) (SProp.zero_mem_later _)
  | succ previous =>
      have previousIncluded : previous <= step := by omega
      exact (SProp.succ_mem_later_iff (left.holds heap) previous).trans
        ((equivalent heap previous previousIncluded).trans
          (SProp.succ_mem_later_iff (right.holds heap) previous).symm)

theorem exists_nonexpansive {Witness : Type w}
    {step : Nat}
    {left right : Witness -> IProp Loc Val}
    (equivalent : forall witness, IProp.EquivAt step (left witness) (right witness)) :
    IProp.EquivAt step (exists_ left) (exists_ right) := by
  intro heap observed included
  constructor
  · rintro ⟨witness, holds⟩
    exact ⟨witness, (equivalent witness heap observed included).mp holds⟩
  · rintro ⟨witness, holds⟩
    exact ⟨witness, (equivalent witness heap observed included).mpr holds⟩

theorem forall_nonexpansive {Witness : Type w}
    {step : Nat}
    {left right : Witness -> IProp Loc Val}
    (equivalent : forall witness, IProp.EquivAt step (left witness) (right witness)) :
    IProp.EquivAt step (forall_ left) (forall_ right) := by
  intro heap observed included
  constructor
  · intro holds witness
    exact (equivalent witness heap observed included).mp (holds witness)
  · intro holds witness
    exact (equivalent witness heap observed included).mpr (holds witness)

theorem equal_nonexpansive {Carrier : Type w} [OFE Carrier]
    {step : Nat}
    {left left' right right' : Carrier}
    (leftEq : OFE.equivAt step left left') (rightEq : OFE.equivAt step right right') :
    IProp.EquivAt step
      (@equal Loc Val Carrier OFE.equivAt (@OFE.mono Carrier _) left right)
      (@equal Loc Val Carrier OFE.equivAt (@OFE.mono Carrier _) left' right') := by
  intro heap observed included
  have leftEq' := OFE.mono included leftEq
  have rightEq' := OFE.mono included rightEq
  constructor
  · intro equivalent
    exact OFE.trans (OFE.symm leftEq') (OFE.trans equivalent rightEq')
  · intro equivalent
    exact OFE.trans leftEq' (OFE.trans equivalent (OFE.symm rightEq'))

theorem pointsTo_nonexpansive [DecidableEq Loc] :
    OFE.NonExpansive₂
      (fun (location : ULift.{max u v, u} Loc) (value : ULift.{max u v, v} Val) =>
        pointsTo location.down value.down) := by
  intro step left left' right right' leftEq rightEq
  cases leftEq
  cases rightEq
  exact OFE.refl step _

/-!
## Certified affine BI laws

The theorems below are the semantic interface used by the proof mode. In the
formulas, `⊢ᵢ` is semantic entailment and `⊣⊢` abbreviates entailment in both
directions.

### Equality

Equality is step-indexed. Leibniz substitution therefore requires `P` to be
non-expansive.

```text
True ⊢ᵢ x = x              x = y ⊢ᵢ y = x

(x = y) ∧ (y = z) ⊢ᵢ x = z
(x = y) ∧ P x ⊢ᵢ P y                         (P non-expansive)
```

### Additive BI

```text
P ⊢ᵢ True                 False ⊢ᵢ P

R ⊢ᵢ P    R ⊢ᵢ Q         P ⊢ᵢ P ∨ Q         Q ⊢ᵢ P ∨ Q
─────────────────         ───────────         ───────────
    R ⊢ᵢ P ∧ Q

R ∧ P ⊢ᵢ Q               R ⊢ᵢ P ⇒ Q
──────────────            ──────────────
R ⊢ᵢ P ⇒ Q               R ∧ P ⊢ᵢ Q

P' ⊢ᵢ P    Q ⊢ᵢ Q'
───────────────────
(P ⇒ Q) ⊢ᵢ (P' ⇒ Q')
```

### Multiplicative BI

`True` is also the separating unit. Resource discard is valid, so this is the
affine specialization of BI rather than general resource-sensitive BI.

```text
P ⊢ᵢ P'    Q ⊢ᵢ Q'       P ∗ Q ⊢ᵢ P         P ∗ Q ⊢ᵢ Q
───────────────────       True ∗ P ⊣⊢ P       P ∗ True ⊣⊢ P
P ∗ Q ⊢ᵢ P' ∗ Q'

(P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R)       P ∗ Q ⊣⊢ Q ∗ P

R ∗ P ⊢ᵢ Q  ↔  R ⊢ᵢ P −∗ Q

P' ⊢ᵢ P    Q ⊢ᵢ Q'
───────────────────
(P −∗ Q) ⊢ᵢ (P' −∗ Q')
```

### Quantifiers

```text
P t ⊢ᵢ ∃ x, P x          (∀ x, P x ⊢ᵢ Q)  →  (∃ x, P x) ⊢ᵢ Q
∀ x, P x ⊢ᵢ P t          (∀ x, R ⊢ᵢ P x)  →  R ⊢ᵢ ∀ x, P x
```

### Always

`□` is MPSL's fixed heap-independent persistent modality.

```text
P ⊢ᵢ Q  →  □ P ⊢ᵢ □ Q       □ P ⊢ᵢ P
True ⊢ᵢ P  →  True ⊢ᵢ □ P    □ P ⊣⊢ □ □ P
□ P ⊢ᵢ □ P ∗ □ P

□ (P ∧ Q) ⊣⊢ □ P ∧ □ Q      □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q
□ (P ∗ Q) ⊣⊢ □ P ∧ □ Q      □ (P ⇒ Q) ⊢ᵢ (□ P ⇒ □ Q)
□ (∃ x, P x) ⊣⊢ ∃ x, □ P x
□ (∀ x, P x) ⊣⊢ ∀ x, □ P x
```

### Later

```text
P ⊢ᵢ Q  →  ▷ P ⊢ᵢ ▷ Q       P ⊢ᵢ ▷ P

▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q      ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q
▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q      ▷ (∀ x, P x) ⊣⊢ ∀ x, ▷ P x

(∃ x, ▷ P x) ⊢ᵢ ▷ (∃ x, P x)
▷ (∃ x, P x) ⊢ᵢ ∃ x, ▷ P x                 (given a default witness)

▷ (P ⇒ Q) ⊢ᵢ (▷ P ⇒ ▷ Q)    ▷ (P −∗ Q) ⊢ᵢ (▷ P −∗ ▷ Q)
□ (▷ P) ⊣⊢ ▷ (□ P)
```

### Fixed resource

```text
(l ↦ v₁) ∗ (l ↦ v₂) ⊢ᵢ False
```

### Unimplemented and out of scope

TODO: add syntax-aware proof-mode Leibniz rewriting after weakening, renaming,
and capture-avoiding substitution are available for the embedded language. The
semantic non-expansive substitution rule is already certified here.

MPSL currently has no syntax for internal biconditional, negation, affinely,
absorbingly, or except-0, so their derived laws are not exposed. Generic
resource algebras, `Own`, ghost state, view shifts, Löb induction,
contractiveness, guarded fixed points, and weakest preconditions are deliberate
non-goals. Converses of the one-way `□` and `▷` rules above are not claimed.
-/

theorem truth_intro (proposition : IProp Loc Val) : proposition ⊢ᵢ truth := by
  intro heap step holds
  trivial

theorem falsum_elim (proposition : IProp Loc Val) : falsum ⊢ᵢ proposition := by
  intro heap step holds
  exact False.elim holds

theorem equal_refl {Carrier : Type w} (equivAt : Nat -> Carrier -> Carrier -> Prop)
    (equivAtMono : forall {smaller larger left right},
      smaller <= larger -> equivAt larger left right -> equivAt smaller left right)
    (equivAtRefl : forall step value, equivAt step value value) (value : Carrier) :
    (@truth Loc Val) ⊢ᵢ (@equal Loc Val Carrier equivAt equivAtMono value value) := by
  intro heap step holds
  exact equivAtRefl step value

theorem equal_symm {Carrier : Type w} (equivAt : Nat -> Carrier -> Carrier -> Prop)
    (equivAtMono : forall {smaller larger left right},
      smaller <= larger -> equivAt larger left right -> equivAt smaller left right)
    (equivAtSymm : forall {step left right}, equivAt step left right -> equivAt step right left)
    (left right : Carrier) :
    (@equal Loc Val Carrier equivAt equivAtMono left right) ⊢ᵢ
      (@equal Loc Val Carrier equivAt equivAtMono right left) := by
  intro heap step equivalent
  exact equivAtSymm equivalent

theorem equal_trans {Carrier : Type w} (equivAt : Nat -> Carrier -> Carrier -> Prop)
    (equivAtMono : forall {smaller larger left right},
      smaller <= larger -> equivAt larger left right -> equivAt smaller left right)
    (equivAtTrans : forall {step first second third},
      equivAt step first second -> equivAt step second third -> equivAt step first third)
    (first second third : Carrier) :
    and (@equal Loc Val Carrier equivAt equivAtMono first second)
      (@equal Loc Val Carrier equivAt equivAtMono second third) ⊢ᵢ
      (@equal Loc Val Carrier equivAt equivAtMono first third) := by
  intro heap step equivalent
  exact equivAtTrans equivalent.1 equivalent.2

theorem equal_subst {Carrier : Type w} [OFE Carrier]
    (predicate : Carrier -> IProp Loc Val) (predicateNonexpansive : OFE.NonExpansive predicate)
    (left right : Carrier) :
    and (equal OFE.equivAt (@OFE.mono Carrier _) left right) (predicate left) ⊢ᵢ
      predicate right := by
  intro heap step holds
  exact (predicateNonexpansive step left right holds.1 heap step (Nat.le_refl step)).mp holds.2

theorem and_intro {premise left right : IProp Loc Val} :
    premise ⊢ᵢ left -> premise ⊢ᵢ right -> premise ⊢ᵢ and left right := by
  intro toLeft toRight heap step holds
  exact ⟨toLeft heap step holds, toRight heap step holds⟩

theorem and_elim_left (left right : IProp Loc Val) : and left right ⊢ᵢ left := by
  intro heap step holds
  exact holds.1

theorem and_elim_right (left right : IProp Loc Val) : and left right ⊢ᵢ right := by
  intro heap step holds
  exact holds.2

theorem and_mono {left right left' right' : IProp Loc Val} :
    left ⊢ᵢ left' -> right ⊢ᵢ right' -> and left right ⊢ᵢ and left' right' := by
  intro leftRule rightRule heap step holds
  exact ⟨leftRule heap step holds.1, rightRule heap step holds.2⟩

theorem or_intro_left (left right : IProp Loc Val) : left ⊢ᵢ or left right := by
  intro heap step holds
  exact Or.inl holds

theorem or_intro_right (left right : IProp Loc Val) : right ⊢ᵢ or left right := by
  intro heap step holds
  exact Or.inr holds

theorem or_elim {left right conclusion : IProp Loc Val} :
    left ⊢ᵢ conclusion -> right ⊢ᵢ conclusion -> or left right ⊢ᵢ conclusion := by
  intro fromLeft fromRight heap step holds
  cases holds with
  | inl leftHolds => exact fromLeft heap step leftHolds
  | inr rightHolds => exact fromRight heap step rightHolds

theorem imp_intro {context premise conclusion : IProp Loc Val} :
    and context premise ⊢ᵢ conclusion -> context ⊢ᵢ imp premise conclusion := by
  intro rule heap step contextHolds smaller included larger heapIncluded premiseHolds
  apply rule larger smaller
  exact ⟨context.monotone heapIncluded
    (context.holds heap |>.downward included contextHolds), premiseHolds⟩

theorem imp_elim (premise conclusion : IProp Loc Val) :
    and (imp premise conclusion) premise ⊢ᵢ conclusion := by
  intro heap step holds
  exact holds.1 step (Nat.le_refl step) heap (Heap.subheap_refl heap) holds.2

theorem imp_mono {left left' right right' : IProp Loc Val} :
    left' ⊢ᵢ left -> right ⊢ᵢ right' -> imp left right ⊢ᵢ imp left' right' := by
  intro leftRule rightRule
  apply imp_intro
  exact entails_trans (and_mono (entails_refl (imp left right)) leftRule)
    (entails_trans (imp_elim left right) rightRule)

theorem sep_mono {left right left' right' : IProp Loc Val} :
    left ⊢ᵢ left' -> right ⊢ᵢ right' -> sep left right ⊢ᵢ sep left' right' := by
  intro leftRule rightRule heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  exact ⟨leftHeap, rightHeap, disjoint, combined,
    leftRule leftHeap step leftHolds, rightRule rightHeap step rightHolds⟩

theorem sep_elim_left (left right : IProp Loc Val) : sep left right ⊢ᵢ left := by
  intro heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  exact left.monotone (Heap.subheap_of_union_eq_left combined) leftHolds

theorem sep_elim_right (left right : IProp Loc Val) : sep left right ⊢ᵢ right := by
  intro heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  exact right.monotone (Heap.subheap_of_union_eq_right disjoint combined) rightHolds

theorem sep_comm (left right : IProp Loc Val) : sep left right ⊢ᵢ sep right left := by
  intro heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  refine ⟨rightHeap, leftHeap, Heap.disjoint_symm disjoint, ?_, rightHolds, leftHolds⟩
  rw [← combined]
  funext location
  cases leftFound : leftHeap location with
  | none =>
      cases rightFound : rightHeap location <;>
        simp [Heap.union, leftFound, rightFound]
  | some leftValue =>
      have rightMissing : rightHeap location = none := by
        cases rightFound : rightHeap location with
        | none => simp at rightFound ⊢
        | some rightValue =>
            exact False.elim
              (disjoint location leftValue rightValue leftFound rightFound)
      simp [Heap.union, leftFound, rightMissing]

theorem sep_truth_left (proposition : IProp Loc Val) : sep truth proposition ⊢ᵢ proposition :=
  sep_elim_right truth proposition

theorem sep_truth_right (proposition : IProp Loc Val) : sep proposition truth ⊢ᵢ proposition :=
  sep_elim_left proposition truth

theorem sep_truth_intro_left (proposition : IProp Loc Val) : proposition ⊢ᵢ sep truth proposition := by
  intro heap step holds
  exact ⟨Heap.empty, heap, Heap.disjoint_empty_left heap, Heap.union_empty_left heap,
    True.intro, holds⟩

theorem sep_truth_intro_right (proposition : IProp Loc Val) : proposition ⊢ᵢ sep proposition truth := by
  exact entails_trans (sep_truth_intro_left proposition) (sep_comm truth proposition)

theorem sep_assoc_left (first second third : IProp Loc Val) :
    sep (sep first second) third ⊢ᵢ sep first (sep second third) := by
  intro heap step holds
  obtain ⟨firstSecondHeap, thirdHeap, firstSecondThird, combinedOuter,
    firstSecondHolds, thirdHolds⟩ := holds
  obtain ⟨firstHeap, secondHeap, firstSecond, combinedInner,
    firstHolds, secondHolds⟩ := firstSecondHolds
  have firstThird : Heap.Disjoint firstHeap thirdHeap :=
    Heap.disjoint_of_subheap_left
      (Heap.subheap_of_union_eq_left combinedInner) firstSecondThird
  have secondThird : Heap.Disjoint secondHeap thirdHeap :=
    Heap.disjoint_of_subheap_left
      (Heap.subheap_of_union_eq_right firstSecond combinedInner) firstSecondThird
  refine ⟨firstHeap, Heap.union secondHeap thirdHeap,
    Heap.disjoint_union_right firstSecond firstThird, ?_, firstHolds, ?_⟩
  · rw [← combinedOuter, ← combinedInner, Heap.union_assoc]
  · exact ⟨secondHeap, thirdHeap, secondThird, rfl, secondHolds, thirdHolds⟩

theorem sep_assoc_right (first second third : IProp Loc Val) :
    sep first (sep second third) ⊢ᵢ sep (sep first second) third := by
  intro heap step holds
  obtain ⟨firstHeap, secondThirdHeap, firstSecondThird, combinedOuter,
    firstHolds, secondThirdHolds⟩ := holds
  obtain ⟨secondHeap, thirdHeap, secondThird, combinedInner,
    secondHolds, thirdHolds⟩ := secondThirdHolds
  have firstSecond : Heap.Disjoint firstHeap secondHeap :=
    Heap.disjoint_of_subheap_right
      (Heap.subheap_of_union_eq_left combinedInner) firstSecondThird
  have firstThird : Heap.Disjoint firstHeap thirdHeap :=
    Heap.disjoint_of_subheap_right
      (Heap.subheap_of_union_eq_right secondThird combinedInner) firstSecondThird
  refine ⟨Heap.union firstHeap secondHeap, thirdHeap,
    Heap.disjoint_union_left firstThird secondThird, ?_, ?_, thirdHolds⟩
  · rw [Heap.union_assoc, combinedInner, combinedOuter]
  · exact ⟨firstHeap, secondHeap, firstSecond, rfl, firstHolds, secondHolds⟩

theorem sep_intro_from {context leftContext rightContext left right : IProp Loc Val} :
    context ⊢ᵢ sep leftContext rightContext ->
    leftContext ⊢ᵢ left -> rightContext ⊢ᵢ right ->
    context ⊢ᵢ sep left right := by
  intro partition leftRule rightRule
  exact entails_trans partition (sep_mono leftRule rightRule)

theorem wand_intro {context premise conclusion : IProp Loc Val} :
    sep context premise ⊢ᵢ conclusion -> context ⊢ᵢ wand premise conclusion := by
  intro rule heap step contextHolds smaller included extra disjoint premiseHolds
  apply rule (Heap.union heap extra) smaller
  exact ⟨heap, extra, disjoint, rfl,
    context.holds heap |>.downward included contextHolds, premiseHolds⟩

theorem wand_elim (premise conclusion : IProp Loc Val) :
    sep (wand premise conclusion) premise ⊢ᵢ conclusion := by
  intro heap step holds
  obtain ⟨wandHeap, premiseHeap, disjoint, combined, wandHolds, premiseHolds⟩ := holds
  rw [← combined]
  exact wandHolds step (Nat.le_refl step) premiseHeap disjoint premiseHolds

theorem wand_mono {left left' right right' : IProp Loc Val} :
    left' ⊢ᵢ left -> right ⊢ᵢ right' -> wand left right ⊢ᵢ wand left' right' := by
  intro leftRule rightRule
  apply wand_intro
  exact entails_trans (sep_mono (entails_refl (wand left right)) leftRule)
    (entails_trans (wand_elim left right) rightRule)

theorem wand_adjunction {context premise conclusion : IProp Loc Val} :
    sep context premise ⊢ᵢ conclusion ↔ context ⊢ᵢ wand premise conclusion := by
  constructor
  · exact wand_intro
  · intro rule
    exact entails_trans (sep_mono rule (entails_refl premise)) (wand_elim premise conclusion)

theorem exists_intro {Witness : Type w} (body : Witness -> IProp Loc Val) (witness : Witness) :
    body witness ⊢ᵢ exists_ body := by
  intro heap step holds
  exact ⟨witness, holds⟩

theorem exists_elim {Witness : Type w} {body : Witness -> IProp Loc Val}
    {conclusion : IProp Loc Val} :
    (forall witness, body witness ⊢ᵢ conclusion) -> exists_ body ⊢ᵢ conclusion := by
  intro rules heap step holds
  obtain ⟨witness, witnessHolds⟩ := holds
  exact rules witness heap step witnessHolds

theorem forall_intro {Witness : Type w} {premise : IProp Loc Val}
    {body : Witness -> IProp Loc Val} :
    (forall witness, premise ⊢ᵢ body witness) -> premise ⊢ᵢ forall_ body := by
  intro rules heap step holds witness
  exact rules witness heap step holds

theorem forall_elim {Witness : Type w} (body : Witness -> IProp Loc Val) (witness : Witness) :
    forall_ body ⊢ᵢ body witness := by
  intro heap step holds
  exact holds witness

theorem always_and_intro (left right : IProp Loc Val) :
    and (always left) (always right) ⊢ᵢ always (and left right) := by
  intro heap step holds
  exact holds

theorem always_and_elim (left right : IProp Loc Val) :
    always (and left right) ⊢ᵢ and (always left) (always right) := by
  intro heap step holds
  exact holds

theorem always_or_intro (left right : IProp Loc Val) :
    or (always left) (always right) ⊢ᵢ always (or left right) := by
  intro heap step holds
  exact holds

theorem always_or_elim (left right : IProp Loc Val) :
    always (or left right) ⊢ᵢ or (always left) (always right) := by
  intro heap step holds
  exact holds

theorem always_sep_intro (left right : IProp Loc Val) :
    and (always left) (always right) ⊢ᵢ always (sep left right) := by
  intro heap step holds
  exact ⟨Heap.empty, Heap.empty, Heap.disjoint_empty_left Heap.empty,
    Heap.union_empty_left Heap.empty, holds.1, holds.2⟩

theorem always_sep_elim (left right : IProp Loc Val) :
    always (sep left right) ⊢ᵢ and (always left) (always right) := by
  intro heap step holds
  exact ⟨sep_elim_left left right Heap.empty step holds,
    sep_elim_right left right Heap.empty step holds⟩

theorem always_exists_intro {Witness : Type w} (body : Witness -> IProp Loc Val) :
    (exists_ fun witness => always (body witness)) ⊢ᵢ always (exists_ body) := by
  intro heap step holds
  exact holds

theorem always_exists_elim {Witness : Type w} (body : Witness -> IProp Loc Val) :
    always (exists_ body) ⊢ᵢ (exists_ fun witness => always (body witness)) := by
  intro heap step holds
  exact holds

theorem always_forall_intro {Witness : Type w} (body : Witness -> IProp Loc Val) :
    (forall_ fun witness => always (body witness)) ⊢ᵢ always (forall_ body) := by
  intro heap step holds
  exact holds

theorem always_forall_elim {Witness : Type w} (body : Witness -> IProp Loc Val) :
    always (forall_ body) ⊢ᵢ (forall_ fun witness => always (body witness)) := by
  intro heap step holds
  exact holds

theorem always_imp (left right : IProp Loc Val) :
    always (imp left right) ⊢ᵢ imp (always left) (always right) := by
  intro heap step holds smaller smallerIncluded larger heapIncluded leftHolds
  exact holds smaller smallerIncluded Heap.empty (Heap.subheap_refl Heap.empty) leftHolds

theorem always_mono {left right : IProp Loc Val} :
    left ⊢ᵢ right -> always left ⊢ᵢ always right := by
  intro rule heap step holds
  exact rule Heap.empty step holds

theorem always_elim (proposition : IProp Loc Val) : always proposition ⊢ᵢ proposition := by
  intro heap step holds
  exact proposition.monotone (Heap.empty_subheap heap) holds

theorem always_intro_from_truth {proposition : IProp Loc Val} :
    truth ⊢ᵢ proposition -> truth ⊢ᵢ always proposition := by
  intro rule heap step holds
  exact rule Heap.empty step True.intro

theorem always_idem_intro (proposition : IProp Loc Val) :
    always proposition ⊢ᵢ always (always proposition) := by
  intro heap step holds
  exact holds

theorem always_idem_elim (proposition : IProp Loc Val) :
    always (always proposition) ⊢ᵢ always proposition := by
  intro heap step holds
  exact holds

theorem always_dup (proposition : IProp Loc Val) :
    always proposition ⊢ᵢ sep (always proposition) (always proposition) := by
  intro heap step holds
  exact ⟨Heap.empty, heap, Heap.disjoint_empty_left heap, Heap.union_empty_left heap,
    holds, holds⟩

theorem always_later_intro (proposition : IProp Loc Val) :
    always (later proposition) ⊢ᵢ later (always proposition) := by
  intro heap step holds
  exact holds

theorem always_later_elim (proposition : IProp Loc Val) :
    later (always proposition) ⊢ᵢ always (later proposition) := by
  intro heap step holds
  exact holds

theorem later_mono {left right : IProp Loc Val} :
    left ⊢ᵢ right -> later left ⊢ᵢ later right := by
  intro rule heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later (right.holds heap)
  | succ previous =>
      apply (SProp.succ_mem_later_iff (right.holds heap) previous).2
      apply rule heap previous
      exact (SProp.succ_mem_later_iff (left.holds heap) previous).1 holds

theorem later_intro (proposition : IProp Loc Val) : proposition ⊢ᵢ later proposition := by
  intro heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later (proposition.holds heap)
  | succ previous =>
      apply (SProp.succ_mem_later_iff (proposition.holds heap) previous).2
      exact proposition.holds heap |>.downward (Nat.le_succ previous) holds

theorem later_or_intro (left right : IProp Loc Val) :
    or (later left) (later right) ⊢ᵢ later (or left right) := by
  intro heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later _
  | succ previous =>
      apply (SProp.succ_mem_later_iff ((or left right).holds heap) previous).2
      cases holds with
      | inl leftHolds =>
          exact Or.inl ((SProp.succ_mem_later_iff (left.holds heap) previous).1 leftHolds)
      | inr rightHolds =>
          exact Or.inr ((SProp.succ_mem_later_iff (right.holds heap) previous).1 rightHolds)

theorem later_or_elim (left right : IProp Loc Val) :
    later (or left right) ⊢ᵢ or (later left) (later right) := by
  intro heap step holds
  cases step with
  | zero => exact Or.inl (SProp.zero_mem_later _)
  | succ previous =>
      have previousHolds :=
        (SProp.succ_mem_later_iff ((or left right).holds heap) previous).1 holds
      cases previousHolds with
      | inl leftHolds =>
          exact Or.inl ((SProp.succ_mem_later_iff (left.holds heap) previous).2 leftHolds)
      | inr rightHolds =>
          exact Or.inr ((SProp.succ_mem_later_iff (right.holds heap) previous).2 rightHolds)

theorem later_exists_intro {Witness : Type w} (body : Witness -> IProp Loc Val) :
    (exists_ fun witness => later (body witness)) ⊢ᵢ later (exists_ body) := by
  intro heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later _
  | succ previous =>
      obtain ⟨witness, witnessHolds⟩ := holds
      apply (SProp.succ_mem_later_iff ((exists_ body).holds heap) previous).2
      exact ⟨witness,
        (SProp.succ_mem_later_iff ((body witness).holds heap) previous).1 witnessHolds⟩

theorem later_exists_elim {Witness : Type w} (body : Witness -> IProp Loc Val)
    (defaultWitness : Witness) :
    later (exists_ body) ⊢ᵢ (exists_ fun witness => later (body witness)) := by
  intro heap step holds
  cases step with
  | zero =>
      exact ⟨defaultWitness, SProp.zero_mem_later _⟩
  | succ previous =>
      obtain ⟨witness, witnessHolds⟩ :=
        (SProp.succ_mem_later_iff ((exists_ body).holds heap) previous).1 holds
      exact ⟨witness,
        (SProp.succ_mem_later_iff ((body witness).holds heap) previous).2 witnessHolds⟩

theorem later_forall_intro {Witness : Type w} (body : Witness -> IProp Loc Val) :
    (forall_ fun witness => later (body witness)) ⊢ᵢ later (forall_ body) := by
  intro heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later _
  | succ previous =>
      apply (SProp.succ_mem_later_iff ((forall_ body).holds heap) previous).2
      intro witness
      exact (SProp.succ_mem_later_iff ((body witness).holds heap) previous).1
        (holds witness)

theorem later_forall_elim {Witness : Type w} (body : Witness -> IProp Loc Val) :
    later (forall_ body) ⊢ᵢ (forall_ fun witness => later (body witness)) := by
  intro heap step holds witness
  cases step with
  | zero => exact SProp.zero_mem_later _
  | succ previous =>
      apply (SProp.succ_mem_later_iff ((body witness).holds heap) previous).2
      exact (SProp.succ_mem_later_iff ((forall_ body).holds heap) previous).1 holds witness

theorem later_imp (left right : IProp Loc Val) :
    later (imp left right) ⊢ᵢ imp (later left) (later right) := by
  intro heap step holds smaller smallerIncluded larger heapIncluded leftHolds
  cases smaller with
  | zero => exact SProp.zero_mem_later _
  | succ previous =>
      have implicationLater : Nat.succ previous ∈ (later (imp left right)).holds heap :=
        (later (imp left right)).holds heap |>.downward smallerIncluded holds
      have implication :=
        (SProp.succ_mem_later_iff ((imp left right).holds heap) previous).1 implicationLater
      have premise :=
        (SProp.succ_mem_later_iff (left.holds larger) previous).1 leftHolds
      apply (SProp.succ_mem_later_iff (right.holds larger) previous).2
      exact implication previous (Nat.le_refl previous) larger heapIncluded premise

theorem later_wand (left right : IProp Loc Val) :
    later (wand left right) ⊢ᵢ wand (later left) (later right) := by
  intro heap step holds smaller smallerIncluded extra disjoint leftHolds
  cases smaller with
  | zero => exact SProp.zero_mem_later _
  | succ previous =>
      have wandLater : Nat.succ previous ∈ (later (wand left right)).holds heap :=
        (later (wand left right)).holds heap |>.downward smallerIncluded holds
      have wandHolds :=
        (SProp.succ_mem_later_iff ((wand left right).holds heap) previous).1 wandLater
      have premise :=
        (SProp.succ_mem_later_iff (left.holds extra) previous).1 leftHolds
      apply (SProp.succ_mem_later_iff (right.holds (Heap.union heap extra)) previous).2
      exact wandHolds previous (Nat.le_refl previous) extra disjoint premise

theorem later_and_intro (left right : IProp Loc Val) :
    and (later left) (later right) ⊢ᵢ later (and left right) := by
  intro heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later ((and left right).holds heap)
  | succ previous =>
      apply (SProp.succ_mem_later_iff ((and left right).holds heap) previous).2
      exact ⟨
        (SProp.succ_mem_later_iff (left.holds heap) previous).1 holds.1,
        (SProp.succ_mem_later_iff (right.holds heap) previous).1 holds.2⟩

theorem later_and_elim (left right : IProp Loc Val) :
    later (and left right) ⊢ᵢ and (later left) (later right) := by
  intro heap step holds
  cases step with
  | zero => exact ⟨SProp.zero_mem_later _, SProp.zero_mem_later _⟩
  | succ previous =>
      have previousHolds :=
        (SProp.succ_mem_later_iff ((and left right).holds heap) previous).1 holds
      exact ⟨
        (SProp.succ_mem_later_iff (left.holds heap) previous).2 previousHolds.1,
        (SProp.succ_mem_later_iff (right.holds heap) previous).2 previousHolds.2⟩

theorem later_sep_intro (left right : IProp Loc Val) :
    sep (later left) (later right) ⊢ᵢ later (sep left right) := by
  intro heap step holds
  cases step with
  | zero => exact SProp.zero_mem_later ((sep left right).holds heap)
  | succ previous =>
      obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
      apply (SProp.succ_mem_later_iff ((sep left right).holds heap) previous).2
      exact ⟨leftHeap, rightHeap, disjoint, combined,
        (SProp.succ_mem_later_iff (left.holds leftHeap) previous).1 leftHolds,
        (SProp.succ_mem_later_iff (right.holds rightHeap) previous).1 rightHolds⟩

theorem later_sep_elim (left right : IProp Loc Val) :
    later (sep left right) ⊢ᵢ sep (later left) (later right) := by
  intro heap step holds
  cases step with
  | zero =>
      exact ⟨Heap.empty, heap, Heap.disjoint_empty_left heap, Heap.union_empty_left heap,
        SProp.zero_mem_later _, SProp.zero_mem_later _⟩
  | succ previous =>
      have previousHolds :=
        (SProp.succ_mem_later_iff ((sep left right).holds heap) previous).1 holds
      obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := previousHolds
      exact ⟨leftHeap, rightHeap, disjoint, combined,
        (SProp.succ_mem_later_iff (left.holds leftHeap) previous).2 leftHolds,
        (SProp.succ_mem_later_iff (right.holds rightHeap) previous).2 rightHolds⟩

/-- Exclusive ownership of one location.

```text
(l ↦ v₁) ∗ (l ↦ v₂) ⊢ᵢ False
```
-/
theorem pointsTo_exclusive [DecidableEq Loc] (location : Loc) (leftValue rightValue : Val) :
    sep (pointsTo location leftValue) (pointsTo location rightValue) ⊢ᵢ falsum := by
  intro heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  have leftFound := Heap.singleton_subheap leftHolds
  have rightFound := Heap.singleton_subheap rightHolds
  exact disjoint location leftValue rightValue leftFound rightFound

end MPSL.IProp
