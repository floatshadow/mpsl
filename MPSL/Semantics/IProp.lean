import MPSL.Heap
import MPSL.Semantics.SProp

set_option autoImplicit false

namespace MPSL

universe u v

/-- A step-indexed assertion, monotone under extension of its owned heap. -/
structure IProp (Loc : Type u) (Val : Type v) where
  holds : Heap Loc Val -> SProp
  monotone : forall {smaller larger},
    Heap.Subheap smaller larger -> forall {step}, step ∈ holds smaller -> step ∈ holds larger

namespace IProp

variable {Loc : Type u} {Val : Type v}

def Entails (left right : IProp Loc Val) : Prop :=
  forall heap step, step ∈ left.holds heap -> step ∈ right.holds heap

scoped infix:25 " ⊢ᵢ " => Entails

def Equiv (left right : IProp Loc Val) : Prop := Entails left right ∧ Entails right left

theorem entails_refl (proposition : IProp Loc Val) : proposition ⊢ᵢ proposition := by
  intro heap step holds
  exact holds

theorem entails_trans {first second third : IProp Loc Val} :
    first ⊢ᵢ second -> second ⊢ᵢ third -> first ⊢ᵢ third := by
  intro firstSecond secondThird heap step holds
  exact secondThird heap step (firstSecond heap step holds)

def EquivAt (step : Nat) (left right : IProp Loc Val) : Prop :=
  forall heap, SProp.EquivAt step (left.holds heap) (right.holds heap)

theorem equivAt_mono {smaller larger : Nat} {left right : IProp Loc Val} :
    smaller <= larger -> EquivAt larger left right -> EquivAt smaller left right := by
  intro included equivalent heap
  exact SProp.equivAt_mono included (equivalent heap)

instance : OFE (IProp Loc Val) where
  equivAt := EquivAt
  refl := by
    intro step proposition heap
    exact SProp.equivAt_refl step (proposition.holds heap)
  symm := by
    intro step left right equivalent heap
    exact SProp.equivAt_symm (equivalent heap)
  trans := by
    intro step first second third firstSecond secondThird heap
    exact SProp.equivAt_trans (firstSecond heap) (secondThird heap)
  mono := equivAt_mono
  eq_of_equivAt := by
    intro left right equivalent
    cases left with
    | mk leftHolds leftMonotone =>
        cases right with
        | mk rightHolds rightMonotone =>
            have holdsEqual : leftHolds = rightHolds := by
              funext heap
              apply SProp.ext
              intro step
              exact equivalent step heap step (Nat.le_refl step)
            subst rightHolds
            rfl

end IProp

end MPSL
