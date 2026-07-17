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

theorem nonExpansive_id [OFE A] : NonExpansive (fun value : A => value) := by
  intro step left right equivalent
  exact equivalent

theorem NonExpansive.comp [OFE A] [OFE B] [OFE C]
    {outer : B -> C} {inner : A -> B} :
    NonExpansive outer -> NonExpansive inner -> NonExpansive (fun value => outer (inner value)) := by
  intro outerNE innerNE step left right equivalent
  exact outerNE step (inner left) (inner right) (innerNE step left right equivalent)

end OFE

end MPSL
