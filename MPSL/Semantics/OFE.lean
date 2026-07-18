set_option autoImplicit false

namespace MPSL

universe u v w

/-- An ordered family of equivalences indexed by observation steps. -/
class OFE (Carrier : Type u) where
  equivAt : Nat -> Carrier -> Carrier -> Prop
  refl : forall step value, equivAt step value value
  symm : forall {step left right}, equivAt step left right -> equivAt step right left
  trans : forall {step first second third},
    equivAt step first second -> equivAt step second third -> equivAt step first third
  mono : forall {smaller larger left right},
    smaller <= larger -> equivAt larger left right -> equivAt smaller left right
  eq_of_equivAt : forall {left right}, (forall step, equivAt step left right) -> left = right

namespace OFE

variable {A : Type u} {B : Type v} {C : Type w}

def NonExpansive [OFE A] [OFE B] (function : A -> B) : Prop :=
  forall step left right,
    OFE.equivAt step left right -> OFE.equivAt step (function left) (function right)

def NonExpansive₂ [OFE A] [OFE B] [OFE C] (function : A -> B -> C) : Prop :=
  forall step left left' right right',
    OFE.equivAt step left left' -> OFE.equivAt step right right' ->
    OFE.equivAt step (function left right) (function left' right')

theorem nonExpansive_id [OFE A] : NonExpansive (fun value : A => value) := by
  intro step left right equivalent
  exact equivalent

theorem NonExpansive.comp [OFE A] [OFE B] [OFE C]
    {outer : B -> C} {inner : A -> B} :
    NonExpansive outer -> NonExpansive inner -> NonExpansive (fun value => outer (inner value)) := by
  intro outerNE innerNE step left right equivalent
  exact outerNE step (inner left) (inner right) (innerNE step left right equivalent)

end OFE

/-- A carrier bundled with its ordered family of equivalences. -/
structure OFEType where
  Carrier : Type u
  ofe : OFE Carrier

namespace OFEType

instance (model : OFEType) : OFE model.Carrier := model.ofe

end OFEType

variable {A : Type u} {B : Type v} {C : Type w}

/-- A function between OFEs that satisfies Figure 7's `OFE-NONEXP` law. -/
structure NEFun (A : Type u) (B : Type v) [OFE A] [OFE B] where
  toFun : A -> B
  nonexpansive : OFE.NonExpansive toFun

namespace NEFun

instance [OFE A] [OFE B] : CoeFun (NEFun A B) (fun _ => A -> B) where
  coe function := function.toFun

instance [OFE A] [OFE B] : OFE (NEFun A B) where
  equivAt := fun step left right =>
    forall value, OFE.equivAt step (left value) (right value)
  refl := by
    intro step function value
    exact OFE.refl step (function value)
  symm := by
    intro step left right equivalent value
    exact OFE.symm (equivalent value)
  trans := by
    intro step first second third firstSecond secondThird value
    exact OFE.trans (firstSecond value) (secondThird value)
  mono := by
    intro smaller larger left right included equivalent value
    exact OFE.mono included (equivalent value)
  eq_of_equivAt := by
    intro left right equivalent
    rcases left with ⟨leftFunction, leftNE⟩
    rcases right with ⟨rightFunction, rightNE⟩
    have functionsEqual : leftFunction = rightFunction := by
      funext value
      exact OFE.eq_of_equivAt fun step => equivalent step value
    subst rightFunction
    rfl

def id [OFE A] : NEFun A A where
  toFun := fun value => value
  nonexpansive := OFE.nonExpansive_id

def const [OFE A] [OFE B] (value : B) : NEFun A B where
  toFun := fun _ => value
  nonexpansive := by
    intro step left right equivalent
    exact OFE.refl step value

def comp [OFE A] [OFE B] [OFE C] (outer : NEFun B C) (inner : NEFun A B) :
    NEFun A C where
  toFun := fun value => outer (inner value)
  nonexpansive := outer.nonexpansive.comp inner.nonexpansive

end NEFun

instance uliftOFE {A : Type u} : OFE (ULift.{v, u} A) where
  equivAt := fun _ left right => left = right
  refl := by simp
  symm := by intro step left right equivalent; exact equivalent.symm
  trans := by
    intro step first second third firstSecond secondThird
    exact firstSecond.trans secondThird
  mono := by intro smaller larger left right included equivalent; exact equivalent
  eq_of_equivAt := by intro left right equivalent; exact equivalent 0

instance prodOFE [OFE A] [OFE B] : OFE (A × B) where
  equivAt := fun step left right =>
    OFE.equivAt step left.1 right.1 ∧ OFE.equivAt step left.2 right.2
  refl := by
    intro step value
    exact ⟨OFE.refl step value.1, OFE.refl step value.2⟩
  symm := by
    intro step left right equivalent
    exact ⟨OFE.symm equivalent.1, OFE.symm equivalent.2⟩
  trans := by
    intro step first second third firstSecond secondThird
    exact ⟨OFE.trans firstSecond.1 secondThird.1,
      OFE.trans firstSecond.2 secondThird.2⟩
  mono := by
    intro smaller larger left right included equivalent
    exact ⟨OFE.mono included equivalent.1, OFE.mono included equivalent.2⟩
  eq_of_equivAt := by
    intro left right equivalent
    rcases left with ⟨leftFirst, leftSecond⟩
    rcases right with ⟨rightFirst, rightSecond⟩
    have firstEqual : leftFirst = rightFirst :=
      OFE.eq_of_equivAt fun step => (equivalent step).1
    have secondEqual : leftSecond = rightSecond :=
      OFE.eq_of_equivAt fun step => (equivalent step).2
    subst rightFirst
    subst rightSecond
    rfl

private def sumEquivAt [OFE A] [OFE B] (step : Nat) : Sum A B -> Sum A B -> Prop
  | .inl left, .inl right => OFE.equivAt step left right
  | .inr left, .inr right => OFE.equivAt step left right
  | .inl _, .inr _ => False
  | .inr _, .inl _ => False

instance sumOFE [OFE A] [OFE B] : OFE (Sum A B) where
  equivAt := sumEquivAt
  refl := by
    intro step value
    cases value <;> exact OFE.refl step _
  symm := by
    intro step left right equivalent
    cases left <;> cases right
    · exact OFE.symm equivalent
    · exact equivalent.elim
    · exact equivalent.elim
    · exact OFE.symm equivalent
  trans := by
    intro step first second third firstSecond secondThird
    cases first <;> cases second <;> cases third
    · exact OFE.trans firstSecond secondThird
    · exact secondThird.elim
    · exact firstSecond.elim
    · exact firstSecond.elim
    · exact firstSecond.elim
    · exact firstSecond.elim
    · exact secondThird.elim
    · exact OFE.trans firstSecond secondThird
  mono := by
    intro smaller larger left right included equivalent
    cases left <;> cases right
    · exact OFE.mono included equivalent
    · exact equivalent.elim
    · exact equivalent.elim
    · exact OFE.mono included equivalent
  eq_of_equivAt := by
    intro left right equivalent
    cases left <;> cases right
    · congr 1
      exact OFE.eq_of_equivAt fun step => equivalent step
    · exact (equivalent 0).elim
    · exact (equivalent 0).elim
    · congr 1
      exact OFE.eq_of_equivAt fun step => equivalent step

end MPSL
