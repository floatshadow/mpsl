import MPSL
import MPSLTest.Model

set_option autoImplicit false

namespace MPSL.ElabTests

open MPSL.TestModel

def assertionConstant : Formula Location Value := mpsl{ □ True }

example : Formula Location Value := mpsl{ True }

example : Formula Location Value := mpsl{ False -> True }

example : Formula Location Value :=
  mpsl{
    loc(0) |-> val(Value.loc 1) *
    loc(1) |-> val(Value.int (-7)) *
    loc(2) |-> val(Value.string "done")
  }

example : Formula Location Value :=
  mpsl{ loc(0) ↦ val(Value.string "zero") ∗ later (loc(1) ↦ val(Value.string "one")) }

example : Formula Location Value :=
  mpsl{ (True /\ later False) \/ always True }

example : Formula Location Value :=
  mpsl{ (True ∧ ▷ False) ∨ □ True }

example : Formula Location Value :=
  mpsl{ forall location : loc, location |-> val(Value.string "value") }

example : Formula Location Value :=
  mpsl{ ∃ value : val, loc(0) ↦ value }

example : Formula Location Value :=
  mpsl{ ∀ location : loc, ∀ value : val,
    location ↦ value ⇒ location ↦ value }

example : Formula Location Value :=
  mpsl{ forall P : iProp, always P -> later P }

example : Formula Location Value :=
  mpsl{ (fun P : iProp => later P)(True) }

example : Formula Location Value :=
  mpsl{ (loc(0), val(Value.string "value")) =[loc × val] (loc(0), val(Value.string "value")) }

example : Formula Location Value :=
  mpsl{ eq[loc](fst (loc(0), val(Value.string "value")), loc(0)) }

example : Formula Location Value :=
  mpsl{ eq[val](snd (loc(0), val(Value.string "value")), val(Value.string "value")) }

example : Formula Location Value :=
  mpsl{
    case inl[val](loc(0)) of
    | inl location => eq[loc](location, loc(0))
    | inr value => eq[val](value, val(Value.string "value"))
  }

example : Formula Location Value :=
  mpsl{
    case inr[loc](val(Value.string "value")) of
    | inl location => location |-> val(Value.string "left")
    | inr value => loc(0) |-> value
  }

example : Formula Location Value :=
  mpsl{ eq[1]((), ()) }

example : Formula Location Value :=
  mpsl{ forall impossible : 0, False }

example : Formula Location Value :=
  mpsl{ eq[𝟙]((), ()) }

example : Formula Location Value :=
  mpsl{ forall impossible : 𝟘, False }

example : Formula Location Value :=
  mpsl{ (fun P : iProp => P) =[iProp → iProp] (fun Q : iProp => Q) }

example : Formula Location Value :=
  mpsl{ (λ P : iProp, ▷ P)(True) }

example : Formula Location Value :=
  mpsl{ (loc(0), (val(Value.string "value"), ())) =[loc × val × 𝟙]
    (loc(0), (val(Value.string "value"), ())) }

example : Formula Location Value :=
  mpsl{ loc(0) =[loc] loc(0) ∧ True }

example : Formula Location Value :=
  mpsl{ forall P : iProp, (P -* P) ∧ (P ⇒ P) }

example (location : Location) (value : Value) : Formula Location Value :=
  mpsl{ loc(location) |-> val(value) }

example : Formula Location Value :=
  mpsl{ `assertionConstant -> `assertionConstant }

example : Formula Location Value :=
  mpsl{ forall P : iProp, forall Q : iProp, P -> Q -> P }

example : Formula Location Value :=
  mpsl{ forall P : iProp, forall P : iProp, P -> P }

example : Formula Location Value :=
  mpsl{ forall f : iProp -> iProp, forall P : iProp, f(P) -> f(P) }

/--
error: MPSL type mismatch: expected loc, got val
-/
#guard_msgs in
example : Formula Location Value :=
  mpsl{ val(Value.string "not-a-location") |-> val(Value.string "value") }

/--
error: unknown MPSL variable 'P'
-/
#guard_msgs in
example : Formula Location Value := mpsl{ P }

/--
error: MPSL type mismatch: expected iProp, got loc
-/
#guard_msgs in
example : Formula Location Value := mpsl{ loc(0) }

/--
error: MPSL application expects a function, got iProp
-/
#guard_msgs in
example : Formula Location Value := mpsl{ True(True) }

/--
error: MPSL type mismatch: left side has type iProp, right side has type val
-/
#guard_msgs in
example : Formula Location Value :=
  mpsl{
    case inl[val](loc(0)) of
    | inl location => True
    | inr value => value
  }

/--
error: MPSL only supports the type constants 0 and 1
-/
#guard_msgs in
example : Formula Location Value := mpsl{ forall impossible : 2, False }

end MPSL.ElabTests
