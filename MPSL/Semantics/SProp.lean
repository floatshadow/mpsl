import Lean.Elab.Tactic.Omega
import MPSL.Semantics.OFE

set_option autoImplicit false

namespace MPSL

/-- A proposition observable for a downward-closed set of step indices. -/
structure SProp where
  steps : Nat -> Prop
  downward : forall {smaller larger}, smaller <= larger -> steps larger -> steps smaller

namespace SProp

instance : Membership Nat SProp where
  mem proposition step := proposition.steps step

@[ext]
theorem ext {left right : SProp}
    (equivalent : forall step, step ∈ left ↔ step ∈ right) : left = right := by
  cases left with
  | mk leftSteps leftDownward =>
      cases right with
      | mk rightSteps rightDownward =>
          have : leftSteps = rightSteps := funext fun step => propext (equivalent step)
          subst rightSteps
          rfl

def bottom : SProp where
  steps := fun _ => False
  downward := by simp

def top : SProp where
  steps := fun _ => True
  downward := by simp

def conj (left right : SProp) : SProp where
  steps := fun step => step ∈ left ∧ step ∈ right
  downward := by
    intro smaller larger included holds
    exact ⟨left.downward included holds.1, right.downward included holds.2⟩

def disj (left right : SProp) : SProp where
  steps := fun step => step ∈ left ∨ step ∈ right
  downward := by
    intro smaller larger included holds
    cases holds with
    | inl leftHolds => exact Or.inl (left.downward included leftHolds)
    | inr rightHolds => exact Or.inr (right.downward included rightHolds)

def later (proposition : SProp) : SProp where
  steps := fun step => step = 0 ∨ exists previous, step = previous + 1 ∧ previous ∈ proposition
  downward := by
    intro smaller larger included holds
    cases smaller with
    | zero => exact Or.inl rfl
    | succ smaller =>
        right
        refine ⟨smaller, rfl, ?_⟩
        cases holds with
        | inl largerZero => omega
        | inr observed =>
            obtain ⟨previous, largerStep, previousHolds⟩ := observed
            have smallerIncluded : smaller <= previous := by omega
            exact proposition.downward smallerIncluded previousHolds

/-- Agreement through the given observation step. -/
def EquivAt (step : Nat) (left right : SProp) : Prop :=
  forall smaller, smaller <= step -> (smaller ∈ left ↔ smaller ∈ right)

theorem equivAt_refl (step : Nat) (proposition : SProp) :
    EquivAt step proposition proposition := by simp [EquivAt]

theorem equivAt_symm {step : Nat} {left right : SProp} :
    EquivAt step left right -> EquivAt step right left := by
  intro equivalent smaller included
  exact (equivalent smaller included).symm

theorem equivAt_trans {step : Nat} {first second third : SProp} :
    EquivAt step first second -> EquivAt step second third -> EquivAt step first third := by
  intro firstSecond secondThird smaller included
  exact (firstSecond smaller included).trans (secondThird smaller included)

theorem equivAt_mono {smaller larger : Nat} {left right : SProp} :
    smaller <= larger -> EquivAt larger left right -> EquivAt smaller left right := by
  intro included equivalent observed observedIncluded
  exact equivalent observed (Nat.le_trans observedIncluded included)

instance : OFE SProp where
  equivAt := EquivAt
  refl := equivAt_refl
  symm := equivAt_symm
  trans := equivAt_trans
  mono := equivAt_mono
  eq_of_equivAt := by
    intro left right equivalent
    apply SProp.ext
    intro step
    exact equivalent step step (Nat.le_refl step)

end SProp

end MPSL
