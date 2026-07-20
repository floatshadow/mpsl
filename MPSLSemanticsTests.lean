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

-- `mintro` enters proof mode and places the entailment premise in the spatial zone.
example (P : Formula Location Value) : P ⊢ P := by
  mintro hP
  mexact hP

-- Additive splitting retains both proof-mode environments in both goals.
example (P : Formula Location Value) : P ⊢ mpsl{ `P ∧ `P } := by
  mintro hP
  msplit
  · mexact hP
  · mexact hP

-- Separating hypotheses are decomposed into independent spatial resources.
example (P Q : Formula Location Value) :
    mpsl{ `P ∗ `Q } ⊢ mpsl{ `Q ∗ `P } := by
  mintro h
  mdestruct h as hP hQ
  msep [hQ]
  · mexact hQ
  · mexact hP

-- An explicit list selects the spatial hypotheses used by the left branch.
example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ (`Q ∗ `R) } ⊢ mpsl{ (`P ∗ `R) ∗ `Q } := by
  mintro h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  msep [hP, hR]
  · msep [hP]
    · mexact hP
    · mexact hR
  · mexact hQ

-- The right-selecting form keeps the generated goals in left-to-right order.
example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ (`Q ∗ `R) } ⊢ mpsl{ `P ∗ (`R ∗ `Q) } := by
  mintro h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  msepR [hQ, hR]
  · mexact hP
  · msepR [hQ]
    · mexact hR
    · mexact hQ

-- Wand introduction appends its premise to the spatial environment.
example (P Q : Formula Location Value) :
    P ⊢ mpsl{ `Q -∗ (`P ∗ `Q) } := by
  mintro hP
  mintro hQ
  msep [hP]
  · mexact hP
  · mexact hQ

example (P Q : Formula Location Value) :
    mpsl{ (`P ⇒ `Q) ∗ `P } ⊢ Q := by
  mintro h
  mdestruct h as himp hP
  mapply himp hP

example (P Q : Formula Location Value) :
    mpsl{ (`P -∗ `Q) ∗ `P } ⊢ Q := by
  mintro h
  mdestruct h as hwand hP
  mapply hwand hP

-- Disjunction elimination works at a named spatial hypothesis.
example (P Q R : Formula Location Value) :
    mpsl{ (`P ∨ `Q) ∗ `R } ⊢ R := by
  mintro h
  mdestruct h as hChoice hR
  mdestruct hChoice as hP hQ
  · mexact hR
  · mexact hR

-- `mpersistent` exposes its certification obligation, then moves the hypothesis.
-- Persistent hypotheses are copied to both sides of every spatial partition.
example (P Q : Formula Location Value) :
    mpsl{ (□ `P) ∗ `Q } ⊢ mpsl{ `P ∗ (`P ∗ `Q) } := by
  mintro h
  mdestruct h as hBox hQ
  mpersistent hBox
  · exact IProp.always_idem_intro P.denote
  · mopen hBox as hP
    msep []
    · mexact hP
    · msep []
      · mexact hP
      · mexact hQ

-- A persistent left conjunct can be retained while the right conjunct stays spatial.
example (P Q : Formula Location Value) :
    mpsl{ (□ `P) ∧ `Q } ⊢ mpsl{ `P ∗ `Q } := by
  mintro h
  mdestruct h as #hBox hQ
  · exact IProp.always_idem_intro P.denote
  · mopen hBox as hP
    msep []
    · mexact hP
    · mexact hQ

-- The persistent conjunct may appear on either side of the additive conjunction.
example (P Q : Formula Location Value) :
    mpsl{ `P ∧ (□ `Q) } ⊢ mpsl{ `P ∗ `Q } := by
  mintro h
  mdestruct h as hP #hBox
  · exact IProp.always_idem_intro Q.denote
  · mopen hBox as hQ
    msep [hP]
    · mexact hP
    · mexact hQ

-- `#` implication introduction records the premise in the persistent environment.
example :
    (mpsl{ True } : Formula Location Value) ⊢ mpsl{ True ⇒ (True ∗ True) } := by
  mintro hOuter
  mintro #hPersistent
  · exact IProp.always_intro_from_truth (IProp.entails_refl IProp.truth)
  · msep [hOuter]
    · mexact hOuter
    · mexact hPersistent

example (P Q : Formula Location Value) :
    mpsl{ `P ∗ `Q } ⊢ mpsl{ `P ∗ True } := by
  mintro h
  mdestruct h as hP hQ
  mframe hP
  mtruth

example (P Q R : Formula Location Value) :
    mpsl{ `P ∗ (`Q ∗ `R) } ⊢ mpsl{ (`P ∗ `R) ∗ True } := by
  mintro h
  mdestruct h as hP hQR
  mdestruct hQR as hQ hR
  mframe [hP, hR]
  mtruth

example :
    (mpsl{ True } : Formula Location Value) ⊢
      mpsl{ ∃ x : loc, x =[loc] loc(0) } := by
  mintro h
  mexists loc(0)
  mrefl

example :
    (mpsl{ ∀ x : loc, x =[loc] x } : Formula Location Value) ⊢
      mpsl{ loc(0) =[loc] loc(0) } := by
  mintro h
  mspecialize h at loc(0) as hzero
  mexact hzero

-- Existential elimination also focuses a named hypothesis within the spatial list.
example (R : Formula Location Value) :
    mpsl{ (∃ x : loc, x =[loc] x) ∗ `R } ⊢ R := by
  mintro h
  mdestruct h as hExists hR
  mopenexists hExists as x hx
  mexact hR

example :
    (mpsl{ loc(0) =[loc] loc(1) } : Formula Location Value) ⊢
      mpsl{ loc(1) =[loc] loc(0) } := by
  mintro hEq
  msymm hEq

example (P : Formula Location Value) : P ⊢ mpsl{ ▷ `P } := by
  mintro hP
  mlater
  mexact hP

example (P R : Formula Location Value) :
    mpsl{ (▷ `P) ∗ `R } ⊢ mpsl{ ▷ (`P ∗ `R) } := by
  mintro h
  mdestruct h as hLater hR
  mopenlater hLater as hP
  msep [hP]
  · mexact hP
  · mexact hR

example :
    (mpsl{ True } : Formula Location Value) ⊢ mpsl{ □ True } := by
  mintro h
  mclear h
  malways
  mtruth

example {Carrier : Type} [OFE Carrier] (predicate : Carrier -> IProp Location Value)
    (nonexpansive : OFE.NonExpansive predicate) (left right : Carrier) :
    IProp.Entails (IProp.and
      (IProp.equal OFE.equivAt (@OFE.mono Carrier _) left right)
      (predicate left)) (predicate right) :=
  IProp.equal_subst predicate nonexpansive left right

example (P Q : Formula Location Value) :
    mpsl{ ▷ (`P ∨ `Q) } ⊢ mpsl{ (▷ `P) ∨ (▷ `Q) } :=
  IProp.later_or_elim P.denote Q.denote

example (P : Formula Location Value) :
    mpsl{ □ (▷ `P) } ⊢ mpsl{ ▷ (□ `P) } :=
  IProp.always_later_intro P.denote

example :
    mpsl{ (loc(0) ↦ val(Value.string "left")) ∗
      (loc(0) ↦ val(Value.string "right")) } ⊢
      (mpsl{ False } : Formula Location Value) := by
  exact IProp.pointsTo_exclusive 0 (Value.string "left") (Value.string "right")

/-- A spatial additive conjunction cannot be duplicated into two spatial hypotheses. -/
example (P Q : Formula Location Value) : P = P ∧ Q = Q := by
  fail_if_success
    have invalid : mpsl{ `P ∧ `Q } ⊢ P := by
      mintro h
      mdestruct h as hP hQ
      mexact hP
  exact ⟨rfl, rfl⟩

/-- A spatial resource cannot be introduced under `always`. -/
example : Unit := by
  fail_if_success
    have invalid :
        (mpsl{ loc(0) ↦ val(Value.string "value") } : Formula Location Value) ⊢
          mpsl{ □ (loc(0) ↦ val(Value.string "value")) } := by
      mintro h
      malways
  exact Unit.unit

/-- One spatial points-to hypothesis cannot be assigned to both split branches. -/
example : Unit := by
  fail_if_success
    have invalid :
        (mpsl{ loc(0) ↦ val(Value.string "value") } : Formula Location Value) ⊢
          mpsl{ (loc(0) ↦ val(Value.string "value")) ∗
            (loc(0) ↦ val(Value.string "value")) } := by
      mintro h
      msep [h]
      · mexact h
      · mexact h
  exact Unit.unit

/--
error: duplicate proof-mode hypothesis name 'h'
-/
#guard_msgs in
example (P Q : Formula Location Value) : P ⊢ mpsl{ `Q -∗ `P } := by
  mintro h
  mintro h

end MPSL.SemanticsTests
