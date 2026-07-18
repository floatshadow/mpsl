import MPSL

set_option autoImplicit false

namespace MPSL.Tests

def assertionConstant : Formula Nat String := mpsl{ □ True }

example : Formula Nat String := mpsl{ True }

example : Formula Nat String := mpsl{ False -> True }

example : Formula Nat String :=
  mpsl{ loc(0) |-> val("zero") * loc(1) |-> val("one") }

example : Formula Nat String :=
  mpsl{ loc(0) ↦ val("zero") ∗ later (loc(1) ↦ val("one")) }

example : Formula Nat String :=
  mpsl{ (True /\ later False) \/ always True }

example : Formula Nat String :=
  mpsl{ (True ∧ ▷ False) ∨ □ True }

example : Formula Nat String :=
  mpsl{ forall location : loc, location |-> val("value") }

example : Formula Nat String :=
  mpsl{ ∃ value : val, loc(0) ↦ value }

example : Formula Nat String :=
  mpsl{ ∀ location : loc, ∀ value : val,
    location ↦ value ⇒ location ↦ value }

example : Formula Nat String :=
  mpsl{ forall P : iProp, always P -> later P }

example : Formula Nat String :=
  mpsl{ (fun P : iProp => later P)(True) }

example : Formula Nat String :=
  mpsl{ (loc(0), val("value")) =[loc × val] (loc(0), val("value")) }

example : Formula Nat String :=
  mpsl{ eq[loc](fst (loc(0), val("value")), loc(0)) }

example : Formula Nat String :=
  mpsl{ eq[val](snd (loc(0), val("value")), val("value")) }

example : Formula Nat String :=
  mpsl{
    case inl[val](loc(0)) of
    | inl location => eq[loc](location, loc(0))
    | inr value => eq[val](value, val("value"))
  }

example : Formula Nat String :=
  mpsl{
    case inr[loc](val("value")) of
    | inl location => location |-> val("left")
    | inr value => loc(0) |-> value
  }

example : Formula Nat String :=
  mpsl{ eq[1]((), ()) }

example : Formula Nat String :=
  mpsl{ forall impossible : 0, False }

example : Formula Nat String :=
  mpsl{ eq[𝟙]((), ()) }

example : Formula Nat String :=
  mpsl{ forall impossible : 𝟘, False }

example : Formula Nat String :=
  mpsl{ (fun P : iProp => P) =[iProp → iProp] (fun Q : iProp => Q) }

example : Formula Nat String :=
  mpsl{ (λ P : iProp, ▷ P)(True) }

example : Formula Nat String :=
  mpsl{ (loc(0), (val("value"), ())) =[loc × val × 𝟙]
    (loc(0), (val("value"), ())) }

example : Formula Nat String :=
  mpsl{ loc(0) =[loc] loc(0) ∧ True }

example : Formula Nat String :=
  mpsl{ forall P : iProp, (P -* P) ∧ (P ⇒ P) }

example (location : Nat) (value : String) : Formula Nat String :=
  mpsl{ loc(location) |-> val(value) }

example : Formula Nat String :=
  mpsl{ `assertionConstant -> `assertionConstant }

example : Formula Nat String :=
  mpsl{ forall P : iProp, forall Q : iProp, P -> Q -> P }

example : Formula Nat String :=
  mpsl{ forall P : iProp, forall P : iProp, P -> P }

example : Formula Nat String :=
  mpsl{ forall f : iProp -> iProp, forall P : iProp, f(P) -> f(P) }

/--
error: MPSL type mismatch: expected loc, got val
-/
#guard_msgs in
example : Formula Nat String :=
  mpsl{ val("not-a-location") |-> val("value") }

/--
error: unknown MPSL variable 'P'
-/
#guard_msgs in
example : Formula Nat String := mpsl{ P }

/--
error: MPSL type mismatch: expected iProp, got loc
-/
#guard_msgs in
example : Formula Nat String := mpsl{ loc(0) }

/--
error: MPSL application expects a function, got iProp
-/
#guard_msgs in
example : Formula Nat String := mpsl{ True(True) }

/--
error: MPSL type mismatch: left side has type iProp, right side has type val
-/
#guard_msgs in
example : Formula Nat String :=
  mpsl{
    case inl[val](loc(0)) of
    | inl location => True
    | inr value => value
  }

/--
error: MPSL only supports the type constants 0 and 1
-/
#guard_msgs in
example : Formula Nat String := mpsl{ forall impossible : 2, False }

end MPSL.Tests
