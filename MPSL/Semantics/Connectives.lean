import MPSL.Semantics.IProp

set_option autoImplicit false

namespace MPSL.IProp

open scoped Heap

universe u v

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

theorem pointsTo_exclusive [DecidableEq Loc] (location : Loc) (leftValue rightValue : Val) :
    sep (pointsTo location leftValue) (pointsTo location rightValue) ⊢ᵢ falsum := by
  intro heap step holds
  obtain ⟨leftHeap, rightHeap, disjoint, combined, leftHolds, rightHolds⟩ := holds
  have leftFound := Heap.singleton_subheap leftHolds
  have rightFound := Heap.singleton_subheap rightHolds
  exact disjoint location leftValue rightValue leftFound rightFound

end MPSL.IProp
