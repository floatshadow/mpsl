import MPSL
import MPSLTest.Model

set_option autoImplicit false

namespace MPSL.SemanticsTests

open scoped MPSL
open MPSL.TestModel

example (ty : Ty) (left right : Ty.denote Location Value ty)
    (equivalent : forall step, Ty.EquivAt Location Value ty step left right) :
    left = right :=
  Ty.eq_of_equivAt Location Value ty equivalent

example {ctx : List Ty} {ty : Ty} (expression : Expr Location Value ctx ty) :
    OFE.NonExpansive (Expr.denote expression) :=
  Expr.denote_nonexpansive expression

example (function : Ty.denote Location Value (.arr .iprop .iprop)) :
    OFE.NonExpansive function.toFun :=
  function.nonexpansive

example (proposition : IProp Location Value) :
    OFE.NonExpansive proposition.holds :=
  proposition.holds_nonexpansive

example (P Q : Formula Location Value) :
    mpsl{ `P ∧ `Q } ⊢ P := by
  mstart h
  mdestruct h as hP hQ
  mexact hP

example (P Q : Formula Location Value) :
    P ⊢ mpsl{ `P ∨ `Q } := by
  mstart hP
  mleft
  mexact hP

example (P : Formula Location Value) :
    mpsl{ `P ∨ `P } ⊢ P := by
  mstart h
  mdestruct h as hP hP'
  · mexact hP
  · mexact hP'

example (P Q : Formula Location Value) :
    P ⊢ mpsl{ `Q ⇒ `P } := by
  mstart hP
  mintro hQ
  mexact hP

example (P Q : Formula Location Value) :
    mpsl{ (`P ⇒ `Q) ∧ `P } ⊢ Q := by
  mstart h
  mdestruct h as himp hP
  mapply

example (P Q : Formula Location Value) :
    mpsl{ `P ∗ `Q } ⊢
    mpsl{ `Q ∗ `P } := by
  mstart h
  mdestruct h as hP hQ
  msep (swap)
  · mexact hQ
  · mexact hP

example (P Q : Formula Location Value) :
    P ⊢ mpsl{ `Q -∗
      (`P ∗ `Q) } := by
  mstart hP
  mintro hQ
  msep
  · mexact hP
  · mexact hQ

example (P Q : Formula Location Value) :
    mpsl{ (`P -∗ `Q) ∗ `P } ⊢ Q := by
  mstart h
  mdestruct h as hwand hP
  mapply

example (P Q R : Formula Location Value) :
    mpsl{ (`P ∗ `Q) ∗ `R } ⊢
    mpsl{ `P ∗ `Q } := by
  mstart h
  mdestruct h as hPQ hR
  mexact hPQ

example (P Q R : Formula Location Value) :
    mpsl{ (`P ∗ `Q) ∗ `R } ⊢
    mpsl{ (`P ∗ `Q) ∗ True } := by
  mstart h
  mdestruct h as hPQ hR
  mframe hPQ
  mtruth

example (P Q R : Formula Location Value) :
    mpsl{ (`P ∗ `Q) ∗ `R } ⊢ P := by
  mstart h
  mdestruct h as hPQ hR
  mdestruct hPQ as hP hQ
  mexact hP

example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ `Q ∗ `R } ⊢
    mpsl{ (`P ∗ `Q) ∗ True } := by
  mstart h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  mframe [hP, hQ]
  mtruth

example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ `Q ∗ `R } ⊢
    mpsl{ (`Q ∗ `R) ∗ True } := by
  mstart h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  mframe [hQ, hR]
  mtruth

example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ `Q ∗ `R } ⊢
    mpsl{ (`P ∗ `R) ∗ True } := by
  mstart h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  mframe [hP, hR]
  mtruth

example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ `Q ∗ `R } ⊢
    mpsl{ (`R ∗ `P ∗ `Q) ∗ True } := by
  mstart h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  mframe [hR, hP, hQ]
  mtruth

example :
    (mpsl{ True } : Formula Location Value) ⊢ mpsl{ ∃ x : loc, x =[loc] loc(0) } := by
  mstart h
  mexists loc(0)
  mrefl

example :
    (mpsl{ True } : Formula Location Value) ⊢ mpsl{ ∀ x : loc, x =[loc] x } := by
  mstart h
  mforall x
  mrefl

example :
    (mpsl{ ∀ x : loc, x =[loc] x } : Formula Location Value) ⊢
    mpsl{ loc(0) =[loc] loc(0) } := by
  mstart h
  mspecialize h at loc(0) as hzero
  mexact hzero

example :
    (mpsl{ ∃ x : loc, x =[loc] x } : Formula Location Value) ⊢ mpsl{ True } := by
  mstart h
  mopenexists h as x hx
  mtruth

example (P : Formula Location Value) :
    mpsl{ □ `P } ⊢ mpsl{ `P ∗ `P } := by
  mstart h
  mdup h as h1 h2
  mopen h1 as hP1
  mopen h2 as hP2
  msep
  · mexact hP1
  · mexact hP2

example :
    (mpsl{ True } : Formula Location Value) ⊢ mpsl{ □ True } := by
  mstart h
  mclear h
  malways
  mtruth

example (P : Formula Location Value) : P ⊢ mpsl{ ▷ `P } := by
  mstart hP
  mlater
  mexact hP

example (P : Formula Location Value) :
  mpsl{ ▷ `P } ⊢ mpsl{ ▷ `P } := by
  mstart h
  mopenlater h as hP
  mexact hP

example (P : Formula Location Value) :
    mpsl{ False ∧ `P } ⊢ P := by
  mstart h
  mdestruct h as hfalse hP
  mfalse hfalse

example :
    (mpsl{ True } : Formula Location Value) ⊢
    mpsl{ (λ x : iProp, x)(True) } := by
  mstart h
  mnormalize
  exact IProp.entails_refl IProp.truth

example : Unit := by
  fail_if_success
    have invalidFrame :
        (mpsl{ True ∧ False } : Formula Location Value) ⊢
        mpsl{ True ∗ True } := by
      mstart h
      mdestruct h as hP hQ
      mframe hP
  exact Unit.unit

example : Unit := by
  fail_if_success
    have invalidAlways :
        (mpsl{ loc(0) ↦ val(Value.string "value") } : Formula Location Value) ⊢
        mpsl{ □ (loc(0) ↦ val(Value.string "value")) } := by
      mstart hP
      malways
  exact Unit.unit

example :
    mpsl{ (loc(0) ↦ val(Value.string "left")) ∗ (loc(0) ↦ val(Value.string "right")) } ⊢
    (mpsl{ False } : Formula Location Value) := by
  exact IProp.pointsTo_exclusive 0 (Value.string "left") (Value.string "right")

example : Unit := by
  fail_if_success
    have invalid :
        (mpsl{ loc(0) ↦ val(Value.string "value") } : Formula Location Value) ⊢
        mpsl{ (loc(0) ↦ val(Value.string "value")) ∗ (loc(0) ↦ val(Value.string "value")) } := by
      mstart h
      msep
  exact Unit.unit

example (_P : Formula Location Value) : Unit := by
  fail_if_success
    have invalidName : _P ⊢ _P := by
      mstart hP
      mexact missing
  exact Unit.unit

end MPSL.SemanticsTests
