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

theorem pointsTo_exclusive [DecidableEq Loc] (location : Loc) (leftValue rightValue : Val) :
    sep (pointsTo location leftValue) (pointsTo location rightValue) ⊢ᵢ falsum := by
  intro heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  have leftFound := Heap.singleton_subheap leftHolds
  have rightFound := Heap.singleton_subheap rightHolds
  exact disjoint location leftValue rightValue leftFound rightFound

end MPSL.IProp
