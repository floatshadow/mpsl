import MPSL

set_option autoImplicit false

namespace MPSL.SemanticsTests

open scoped MPSL

example (P Q : Formula Nat String) :
    mpsl{ embed[iProp](P) ∧ embed[iProp](Q) } ⊢ P := by
  mstart h
  mdestruct h as hP hQ
  mexact hP

example (P Q : Formula Nat String) :
    P ⊢ mpsl{ embed[iProp](P) ∨ embed[iProp](Q) } := by
  mstart hP
  mleft
  mexact hP

example (P : Formula Nat String) :
    mpsl{ embed[iProp](P) ∨ embed[iProp](P) } ⊢ P := by
  mstart h
  mdestruct h as hP hP'
  · mexact hP
  · mexact hP'

example (P Q : Formula Nat String) :
    P ⊢ mpsl{ embed[iProp](Q) ⇒ embed[iProp](P) } := by
  mstart hP
  mintro hQ
  mexact hP

example (P Q : Formula Nat String) :
    mpsl{ (embed[iProp](P) ⇒ embed[iProp](Q)) ∧ embed[iProp](P) } ⊢ Q := by
  mstart h
  mdestruct h as himp hP
  mapply

example (P Q : Formula Nat String) :
    mpsl{ embed[iProp](P) ∗ embed[iProp](Q) } ⊢
    mpsl{ embed[iProp](Q) ∗ embed[iProp](P) } := by
  mstart h
  mdestruct h as hP hQ
  msep (swap)
  · mexact hQ
  · mexact hP

example (P Q : Formula Nat String) :
    P ⊢ mpsl{ embed[iProp](Q) -∗
      (embed[iProp](P) ∗ embed[iProp](Q)) } := by
  mstart hP
  mintro hQ
  msep
  · mexact hP
  · mexact hQ

example (P Q : Formula Nat String) :
    mpsl{ (embed[iProp](P) -∗ embed[iProp](Q)) ∗ embed[iProp](P) } ⊢ Q := by
  mstart h
  mdestruct h as hwand hP
  mapply

example :
    mpsl{ (loc(0) ↦ val("left")) ∗ (loc(0) ↦ val("right")) } ⊢
    (mpsl{ False } : Formula Nat String) := by
  exact IProp.pointsTo_exclusive 0 "left" "right"

example : Unit := by
  fail_if_success
    have invalid :
        (mpsl{ loc(0) ↦ val("value") } : Formula Nat String) ⊢
        mpsl{ (loc(0) ↦ val("value")) ∗ (loc(0) ↦ val("value")) } := by
      mstart h
      msep
  exact Unit.unit

example (_P : Formula Nat String) : Unit := by
  fail_if_success
    have invalidName : _P ⊢ _P := by
      mstart hP
      mexact missing
  exact Unit.unit

end MPSL.SemanticsTests
