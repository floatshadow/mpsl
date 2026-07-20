import MPSL
import MPSLTest.Model
import MPSLTest.Pretty

set_option autoImplicit false

namespace MPSL.PrettyPrintTests

open scoped MPSL
open MPSL.TestModel
open MPSL.Test

example (P : Formula Location Value) : P ⊢ P := by
  mintro hP
  run_tac assertPretty #[
    "──────────────────────────────────────☐",
    "hP : `P",
    "──────────────────────────────────────∗",
    "`P"]
  mexact hP

example (P Q : Formula Location Value) :
    mpsl{ `P ∗ `Q } ⊢ mpsl{ `Q ∗ `P } := by
  mintro h
  run_tac assertPretty #[
    "──────────────────────────────────────☐",
    "h : (`P ∗ `Q)",
    "──────────────────────────────────────∗",
    "(`Q ∗ `P)"]
  mdestruct h as hP hQ
  msep [hQ]
  · run_tac assertPretty #[
      "──────────────────────────────────────☐",
      "hQ : `Q",
      "──────────────────────────────────────∗",
      "`Q"]
    mexact hQ
  · run_tac assertPretty #[
      "──────────────────────────────────────☐",
      "hP : `P",
      "──────────────────────────────────────∗",
      "`P"]
    mexact hP

example :
    (mpsl{ True } : Formula Location Value) ⊢
      mpsl{ ∀ y : loc, y =[loc] y } := by
  mintro h
  mforall y
  run_tac assertPretty #[
    "──────────────────────────────────────☐",
    "h : True",
    "──────────────────────────────────────∗",
    "y =[loc] y"]
  mrefl

example (P S Q R : Formula Location Value) (x : Nat) (_pureFact : x = x) :
    mpsl{ (□ `P) ∗ ((□ `S) ∗ (`Q ∗ `R)) } ⊢
      mpsl{ `P ∗ (`S ∗ (`Q ∗ `R)) } := by
  mintro h
  mdestruct h as hBoxP hRest
  mdestruct hRest as hBoxS hQR
  mdestruct hQR as hQ hR
  mpersistent hBoxP
  · run_tac assertPretty #["(□ `P) ⊢ᵢ (□ □ `P)"]
    exact IProp.always_idem_intro P.denote
  · mpersistent hBoxS
    · exact IProp.always_idem_intro S.denote
    · mopen hBoxP as hP
      mopen hBoxS as hS
      run_tac assertPretty #[
        "hS : `S",
        "hP : `P",
        "──────────────────────────────────────☐",
        "hQ : `Q",
        "hR : `R",
        "──────────────────────────────────────∗",
        "(`P ∗ (`S ∗ (`Q ∗ `R)))"]
      msep []
      · mexact hP
      · msep []
        · mexact hS
        · msep [hQ]
          · mexact hQ
          · mexact hR

end MPSL.PrettyPrintTests
