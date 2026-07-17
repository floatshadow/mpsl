import MPSL.Semantics.OFE

set_option autoImplicit false

namespace MPSL

universe u v

/-- A partial heap from locations to values. -/
abbrev Heap (Loc : Type u) (Val : Type v) := Loc -> Option Val

namespace Heap

variable {Loc : Type u} {Val : Type v}

def empty : Heap Loc Val := fun _ => none

def singleton [DecidableEq Loc] (location : Loc) (value : Val) : Heap Loc Val :=
  fun candidate => if candidate = location then some value else none

/-- Every binding in `smaller` occurs unchanged in `larger`. -/
def Subheap (smaller larger : Heap Loc Val) : Prop :=
  forall location value, smaller location = some value -> larger location = some value

scoped infix:50 " ⊑ " => Subheap

def Disjoint (left right : Heap Loc Val) : Prop :=
  forall location leftValue rightValue,
    left location = some leftValue -> right location = some rightValue -> False

/-- Left-biased union. Under `Disjoint`, the bias is unobservable. -/
def union (left right : Heap Loc Val) : Heap Loc Val := fun location =>
  match left location with
  | some value => some value
  | none => right location

def without (heap removed : Heap Loc Val) : Heap Loc Val := fun location =>
  match removed location with
  | some _ => none
  | none => heap location

instance : OFE (Heap Loc Val) where
  equivAt := fun _ left right => left = right
  refl := by simp
  symm := by intro step left right equivalent; exact equivalent.symm
  trans := by intro step first second third firstSecond secondThird; exact firstSecond.trans secondThird
  mono := by intro smaller larger left right included equivalent; exact equivalent
  eq_of_equivAt := by intro left right equivalent; exact equivalent 0

theorem subheap_refl (heap : Heap Loc Val) : heap ⊑ heap := by
  intro location value found
  exact found

theorem subheap_trans {first second third : Heap Loc Val} :
    first ⊑ second -> second ⊑ third -> first ⊑ third := by
  intro firstSecond secondThird location value found
  exact secondThird location value (firstSecond location value found)

theorem empty_subheap (heap : Heap Loc Val) : empty ⊑ heap := by
  intro location value found
  simp [empty] at found

theorem disjoint_symm {left right : Heap Loc Val} :
    Disjoint left right -> Disjoint right left := by
  intro disjoint location rightValue leftValue rightFound leftFound
  exact disjoint location leftValue rightValue leftFound rightFound

theorem disjoint_empty_left (heap : Heap Loc Val) : Disjoint empty heap := by
  intro location value _ found
  simp [empty] at found

theorem disjoint_empty_right (heap : Heap Loc Val) : Disjoint heap empty :=
  disjoint_symm (disjoint_empty_left heap)

theorem left_subheap_union (left right : Heap Loc Val) : left ⊑ union left right := by
  intro location value found
  simp [union, found]

theorem right_subheap_union {left right : Heap Loc Val} (disjoint : Disjoint left right) :
    right ⊑ union left right := by
  intro location value rightFound
  unfold union
  split
  next leftValue leftFound =>
    exact False.elim (disjoint location leftValue value leftFound rightFound)
  next leftMissing => exact rightFound

theorem union_subheap {left right larger : Heap Loc Val} :
    left ⊑ larger -> right ⊑ larger -> union left right ⊑ larger := by
  intro leftLarger rightLarger location value found
  cases leftFound : left location with
  | none =>
      apply rightLarger location value
      simpa [union, leftFound] using found
  | some leftValue =>
      have sameValue : leftValue = value := by
        simpa [union, leftFound] using found
      subst value
      exact leftLarger location leftValue leftFound

theorem union_empty_left (heap : Heap Loc Val) : union empty heap = heap := by
  funext location
  simp [union, empty]

theorem union_empty_right (heap : Heap Loc Val) : union heap empty = heap := by
  funext location
  cases found : heap location <;> simp [union, empty, found]

theorem union_self {left right : Heap Loc Val} :
    Disjoint left right -> union left right ⊑ union left right := by
  intro _
  exact subheap_refl _

theorem union_mono_left {small large extra : Heap Loc Val}
    (included : small ⊑ large) (disjoint : Disjoint large extra) :
    union small extra ⊑ union large extra := by
  intro location value found
  cases smallFound : small location with
  | some smallValue =>
      have sameValue : smallValue = value := by
        simpa [union, smallFound] using found
      subst value
      have largeFound := included location smallValue smallFound
      simp [union, largeFound]
  | none =>
      have extraFound : extra location = some value := by
        simpa [union, smallFound] using found
      have largeMissing : large location = none := by
        cases largeFound : large location with
        | none => simp at largeFound ⊢
        | some largeValue =>
            exact False.elim
              (disjoint location largeValue value largeFound extraFound)
      simp [union, largeMissing, extraFound]

theorem subheap_of_union_eq_left {left right whole : Heap Loc Val}
    (combined : union left right = whole) : left ⊑ whole := by
  rw [← combined]
  exact left_subheap_union left right

theorem subheap_of_union_eq_right {left right whole : Heap Loc Val}
    (disjoint : Disjoint left right) (combined : union left right = whole) : right ⊑ whole := by
  rw [← combined]
  exact right_subheap_union disjoint

theorem without_disjoint (heap removed : Heap Loc Val) : Disjoint (without heap removed) removed := by
  intro location leftValue rightValue leftFound rightFound
  simp [without, rightFound] at leftFound

theorem union_without {whole removed : Heap Loc Val}
    (removedWhole : removed ⊑ whole) : union (without whole removed) removed = whole := by
  funext location
  cases removedFound : removed location with
  | none =>
      cases wholeFound : whole location <;>
        simp [without, union, removedFound, wholeFound]
  | some removedValue =>
      have wholeFound := removedWhole location removedValue removedFound
      simp [without, union, removedFound, wholeFound]

theorem subheap_without {small whole removed : Heap Loc Val}
    (disjoint : Disjoint small removed) (smallWhole : small ⊑ whole) :
    small ⊑ without whole removed := by
  intro location value smallFound
  cases removedFound : removed location with
  | none =>
      simpa [without, removedFound] using smallWhole location value smallFound
  | some removedValue =>
      exact False.elim
        (disjoint location value removedValue smallFound removedFound)

/-- Extend the left side of an exact disjoint split to cover a larger heap. -/
theorem extend_split {left right whole larger : Heap Loc Val}
    (disjoint : Disjoint left right) (combined : union left right = whole)
    (included : whole ⊑ larger) :
    exists left',
      Disjoint left' right ∧
      union left' right = larger ∧
      left ⊑ left' := by
  have rightWhole : right ⊑ whole := subheap_of_union_eq_right disjoint combined
  have rightLarger : right ⊑ larger := subheap_trans rightWhole included
  refine ⟨without larger right, without_disjoint larger right, ?_, ?_⟩
  · exact union_without rightLarger
  · apply subheap_without disjoint
    exact subheap_trans (subheap_of_union_eq_left combined) included

theorem singleton_subheap [DecidableEq Loc] {location : Loc} {value : Val}
    {heap : Heap Loc Val} : singleton location value ⊑ heap -> heap location = some value := by
  intro included
  apply included location value
  simp [singleton]

theorem singleton_self [DecidableEq Loc] (location : Loc) (value : Val) :
    singleton location value ⊑ singleton location value := subheap_refl _

theorem singleton_not_disjoint_self [DecidableEq Loc] (location : Loc) (value : Val) :
    ¬ Disjoint (singleton location value) (singleton location value) := by
  intro disjoint
  apply disjoint location value value <;> simp [singleton]

end Heap

end MPSL
