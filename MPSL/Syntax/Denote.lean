import MPSL.Syntax.Expr
import MPSL.Semantics.Connectives

set_option autoImplicit false

namespace MPSL

universe u v

namespace Ty

/-- The semantic carrier and Figure 7 OFE structure of an object-language type. -/
def model (Loc : Type u) (Val : Type v) : Ty -> OFEType.{max u v}
  | .loc => ⟨ULift.{max u v, u} Loc, inferInstance⟩
  | .val => ⟨ULift.{max u v, v} Val, inferInstance⟩
  | .iprop => ⟨IProp Loc Val, inferInstance⟩
  | .empty => ⟨ULift.{max u v, 0} Empty, inferInstance⟩
  | .unit => ⟨ULift.{max u v, 0} Unit, inferInstance⟩
  | .prod left right =>
      let leftModel := model Loc Val left
      let rightModel := model Loc Val right
      letI : OFE leftModel.Carrier := leftModel.ofe
      letI : OFE rightModel.Carrier := rightModel.ofe
      ⟨leftModel.Carrier × rightModel.Carrier, inferInstance⟩
  | .sum left right =>
      let leftModel := model Loc Val left
      let rightModel := model Loc Val right
      letI : OFE leftModel.Carrier := leftModel.ofe
      letI : OFE rightModel.Carrier := rightModel.ofe
      ⟨Sum leftModel.Carrier rightModel.Carrier, inferInstance⟩
  | .arr domain codomain =>
      let domainModel := model Loc Val domain
      let codomainModel := model Loc Val codomain
      letI : OFE domainModel.Carrier := domainModel.ofe
      letI : OFE codomainModel.Carrier := codomainModel.ofe
      ⟨NEFun domainModel.Carrier codomainModel.Carrier, inferInstance⟩

/-- Semantic carrier of an object-language type. -/
abbrev denote (Loc : Type u) (Val : Type v) (ty : Ty) : Type (max u v) :=
  (model Loc Val ty).Carrier

instance (Loc : Type u) (Val : Type v) (ty : Ty) : OFE (denote Loc Val ty) :=
  (model Loc Val ty).ofe

/-- Indexed equivalence supplied by the type's bundled OFE model. -/
abbrev EquivAt (Loc : Type u) (Val : Type v) (ty : Ty) :=
  @OFE.equivAt (denote Loc Val ty) (inferInstanceAs (OFE (denote Loc Val ty)))

theorem equivAt_mono (Loc : Type u) (Val : Type v) (ty : Ty)
    {smaller larger : Nat} {left right : denote Loc Val ty} :
    smaller <= larger -> EquivAt Loc Val ty larger left right ->
    EquivAt Loc Val ty smaller left right := OFE.mono

theorem equivAt_refl (Loc : Type u) (Val : Type v) (ty : Ty)
    {step : Nat} (value : denote Loc Val ty) : EquivAt Loc Val ty step value value :=
  OFE.refl step value

theorem equivAt_symm (Loc : Type u) (Val : Type v) (ty : Ty)
    {step : Nat} {left right : denote Loc Val ty} :
    EquivAt Loc Val ty step left right -> EquivAt Loc Val ty step right left :=
  OFE.symm

theorem equivAt_trans (Loc : Type u) (Val : Type v) (ty : Ty)
    {step : Nat} {first second third : denote Loc Val ty} :
    EquivAt Loc Val ty step first second ->
    EquivAt Loc Val ty step second third -> EquivAt Loc Val ty step first third :=
  OFE.trans

theorem eq_of_equivAt (Loc : Type u) (Val : Type v) (ty : Ty)
    {left right : denote Loc Val ty} :
    (forall step, EquivAt Loc Val ty step left right) -> left = right :=
  OFE.eq_of_equivAt

end Ty

/-- A semantic environment matching an intrinsic object-language context. -/
inductive Env (Loc : Type u) (Val : Type v) : List Ty -> Type (max u v) where
  | nil : Env Loc Val []
  | cons {ty : Ty} {ctx : List Ty} :
      Ty.denote Loc Val ty -> Env Loc Val ctx -> Env Loc Val (ty :: ctx)

namespace Env

def EquivAt {Loc : Type u} {Val : Type v} {ctx : List Ty} (step : Nat) :
    Env Loc Val ctx -> Env Loc Val ctx -> Prop
  | .nil, .nil => True
  | .cons left leftRest, .cons right rightRest =>
      OFE.equivAt step left right ∧ EquivAt step leftRest rightRest

instance {Loc : Type u} {Val : Type v} {ctx : List Ty} : OFE (Env Loc Val ctx) where
  equivAt := EquivAt
  refl := by
    intro step environment
    induction environment with
    | nil => trivial
    | cons value rest induction => exact ⟨OFE.refl step value, induction⟩
  symm := by
    intro step left right equivalent
    induction left with
    | nil => cases right; trivial
    | cons value rest induction =>
        cases right with
        | cons rightValue rightRest =>
            exact ⟨OFE.symm equivalent.1, induction equivalent.2⟩
  trans := by
    intro step first second third firstSecond secondThird
    induction first with
    | nil => cases second; cases third; trivial
    | cons value rest induction =>
        cases second with
        | cons secondValue secondRest =>
            cases third with
            | cons thirdValue thirdRest =>
                exact ⟨OFE.trans firstSecond.1 secondThird.1,
                  induction firstSecond.2 secondThird.2⟩
  mono := by
    intro smaller larger left right included equivalent
    induction left with
    | nil => cases right; trivial
    | cons value rest induction =>
        cases right with
        | cons rightValue rightRest =>
            exact ⟨OFE.mono included equivalent.1, induction equivalent.2⟩
  eq_of_equivAt := by
    intro left right equivalent
    induction left with
    | nil => cases right; rfl
    | cons value rest induction =>
        cases right with
        | cons rightValue rightRest =>
            have valueEqual : value = rightValue :=
              OFE.eq_of_equivAt fun step => (equivalent step).1
            have restEqual : rest = rightRest :=
              induction fun step => (equivalent step).2
            subst rightValue
            subst rightRest
            rfl

end Env

namespace Var

def denote {Loc : Type u} {Val : Type v} {ctx : List Ty} {ty : Ty} :
    Var ctx ty -> Env Loc Val ctx -> Ty.denote Loc Val ty
  | .here, .cons value _ => value
  | .there boundVar, .cons _ rest => denote boundVar rest

theorem denote_nonexpansive {Loc : Type u} {Val : Type v} {ctx : List Ty} {ty : Ty}
    (boundVariable : Var ctx ty) :
    OFE.NonExpansive (@denote Loc Val ctx ty boundVariable) := by
  intro step left right equivalent
  induction boundVariable with
  | here =>
      cases left with
      | cons leftValue leftRest =>
          cases right with
          | cons rightValue rightRest => exact equivalent.1
  | there previousVariable inductionHyp =>
      cases left with
      | cons leftValue leftRest =>
          cases right with
          | cons rightValue rightRest =>
              exact inductionHyp leftRest rightRest equivalent.2

end Var

namespace Expr

variable {Loc : Type u} {Val : Type v}

/-- Interpret an expression as a non-expansive map from environments to values. -/
def denoteNE [DecidableEq Loc] {ctx : List Ty} {ty : Ty} :
    Expr Loc Val ctx ty -> NEFun (Env Loc Val ctx) (Ty.denote Loc Val ty)
  | .var boundVar =>
      ⟨boundVar.denote, boundVar.denote_nonexpansive⟩
  | .embed expression => NEFun.const (denoteNE expression .nil)
  | .loc location => NEFun.const (ULift.up location)
  | .val value => NEFun.const (ULift.up value)
  | .unit => NEFun.const (ULift.up ())
  | .lam body =>
      let bodyDenote := denoteNE body
      { toFun := fun environment =>
          { toFun := fun argument => bodyDenote (.cons argument environment)
            nonexpansive := by
              intro step left right equivalent
              exact bodyDenote.nonexpansive step _ _
                ⟨equivalent, OFE.refl step environment⟩ }
        nonexpansive := by
          intro step left right equivalent argument
          exact bodyDenote.nonexpansive step _ _
            ⟨OFE.refl step argument, equivalent⟩ }
  | .app function argument =>
      let functionDenote := denoteNE function
      let argumentDenote := denoteNE argument
      { toFun := fun environment =>
          (functionDenote environment).toFun (argumentDenote environment)
        nonexpansive := by
          intro step left right equivalent
          exact OFE.trans
            ((functionDenote left).nonexpansive step _ _
              (argumentDenote.nonexpansive step left right equivalent))
            (functionDenote.nonexpansive step left right equivalent (argumentDenote right)) }
  | .pair left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment => (leftDenote environment, rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact ⟨leftDenote.nonexpansive step first second equivalent,
            rightDenote.nonexpansive step first second equivalent⟩ }
  | .fst product =>
      let productDenote := denoteNE product
      { toFun := fun environment => (productDenote environment).1
        nonexpansive := by
          intro step left right equivalent
          exact (productDenote.nonexpansive step left right equivalent).1 }
  | .snd product =>
      let productDenote := denoteNE product
      { toFun := fun environment => (productDenote environment).2
        nonexpansive := by
          intro step left right equivalent
          exact (productDenote.nonexpansive step left right equivalent).2 }
  | .inl _ value =>
      let valueDenote := denoteNE value
      { toFun := fun environment => Sum.inl (valueDenote environment)
        nonexpansive := by
          intro step left right equivalent
          exact valueDenote.nonexpansive step left right equivalent }
  | .inr _ value =>
      let valueDenote := denoteNE value
      { toFun := fun environment => Sum.inr (valueDenote environment)
        nonexpansive := by
          intro step left right equivalent
          exact valueDenote.nonexpansive step left right equivalent }
  | .case scrutinee leftBranch rightBranch =>
      let scrutineeDenote := denoteNE scrutinee
      let leftDenote := denoteNE leftBranch
      let rightDenote := denoteNE rightBranch
      { toFun := fun environment =>
          match scrutineeDenote environment with
          | .inl value => leftDenote (.cons value environment)
          | .inr value => rightDenote (.cons value environment)
        nonexpansive := by
          intro step leftEnvironment rightEnvironment environmentsEquivalent
          have scrutineesEquivalent :=
            scrutineeDenote.nonexpansive step leftEnvironment rightEnvironment
              environmentsEquivalent
          generalize leftResultEq : scrutineeDenote leftEnvironment = leftResult
          generalize rightResultEq : scrutineeDenote rightEnvironment = rightResult
          cases leftResult with
          | inl leftValue =>
              cases rightResult with
              | inl rightValue =>
                  simp only [leftResultEq, rightResultEq] at scrutineesEquivalent ⊢
                  apply leftDenote.nonexpansive step
                  exact ⟨scrutineesEquivalent, environmentsEquivalent⟩
              | inr rightValue =>
                  simp only [leftResultEq, rightResultEq] at scrutineesEquivalent
                  exact False.elim scrutineesEquivalent
          | inr leftValue =>
              cases rightResult with
              | inl rightValue =>
                  simp only [leftResultEq, rightResultEq] at scrutineesEquivalent
                  exact False.elim scrutineesEquivalent
              | inr rightValue =>
                  simp only [leftResultEq, rightResultEq] at scrutineesEquivalent ⊢
                  apply rightDenote.nonexpansive step
                  exact ⟨scrutineesEquivalent, environmentsEquivalent⟩ }
  | .falsum => NEFun.const IProp.falsum
  | .truth => NEFun.const IProp.truth
  | @Expr.eq _ _ _ comparedTy left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment =>
          IProp.equal (Ty.EquivAt Loc Val comparedTy)
            (Ty.equivAt_mono Loc Val comparedTy)
            (leftDenote environment) (rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact IProp.equal_nonexpansive
            (leftDenote.nonexpansive step first second equivalent)
            (rightDenote.nonexpansive step first second equivalent) }
  | .imp left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment => IProp.imp (leftDenote environment) (rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact IProp.imp_nonexpansive step _ _ _ _
            (leftDenote.nonexpansive step first second equivalent)
            (rightDenote.nonexpansive step first second equivalent) }
  | .and left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment => IProp.and (leftDenote environment) (rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact IProp.and_nonexpansive step _ _ _ _
            (leftDenote.nonexpansive step first second equivalent)
            (rightDenote.nonexpansive step first second equivalent) }
  | .or left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment => IProp.or (leftDenote environment) (rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact IProp.or_nonexpansive step _ _ _ _
            (leftDenote.nonexpansive step first second equivalent)
            (rightDenote.nonexpansive step first second equivalent) }
  | .sep left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment => IProp.sep (leftDenote environment) (rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact IProp.sep_nonexpansive step _ _ _ _
            (leftDenote.nonexpansive step first second equivalent)
            (rightDenote.nonexpansive step first second equivalent) }
  | .wand left right =>
      let leftDenote := denoteNE left
      let rightDenote := denoteNE right
      { toFun := fun environment => IProp.wand (leftDenote environment) (rightDenote environment)
        nonexpansive := by
          intro step first second equivalent
          exact IProp.wand_nonexpansive step _ _ _ _
            (leftDenote.nonexpansive step first second equivalent)
            (rightDenote.nonexpansive step first second equivalent) }
  | .ex body =>
      let bodyDenote := denoteNE body
      { toFun := fun environment =>
          IProp.exists_ fun witness => bodyDenote (.cons witness environment)
        nonexpansive := by
          intro step left right equivalent
          exact IProp.exists_nonexpansive fun witness =>
            bodyDenote.nonexpansive step _ _
              ⟨OFE.refl step witness, equivalent⟩ }
  | .all body =>
      let bodyDenote := denoteNE body
      { toFun := fun environment =>
          IProp.forall_ fun witness => bodyDenote (.cons witness environment)
        nonexpansive := by
          intro step left right equivalent
          exact IProp.forall_nonexpansive fun witness =>
            bodyDenote.nonexpansive step _ _
              ⟨OFE.refl step witness, equivalent⟩ }
  | .pointsTo location value =>
      let locationDenote := denoteNE location
      let valueDenote := denoteNE value
      { toFun := fun environment =>
          IProp.pointsTo (locationDenote environment).down (valueDenote environment).down
        nonexpansive := by
          intro step left right equivalent
          have locationsEqual := locationDenote.nonexpansive step left right equivalent
          have valuesEqual := valueDenote.nonexpansive step left right equivalent
          exact IProp.pointsTo_nonexpansive step _ _ _ _ locationsEqual valuesEqual }
  | .always proposition =>
      let propositionDenote := denoteNE proposition
      { toFun := fun environment => IProp.always (propositionDenote environment)
        nonexpansive := by
          intro step left right equivalent
          exact IProp.always_nonexpansive step _ _
            (propositionDenote.nonexpansive step left right equivalent) }
  | .later proposition =>
      let propositionDenote := denoteNE proposition
      { toFun := fun environment => IProp.later (propositionDenote environment)
        nonexpansive := by
          intro step left right equivalent
          exact IProp.later_nonexpansive step _ _
            (propositionDenote.nonexpansive step left right equivalent) }

/-- Evaluate a typed expression in a semantic environment. -/
def denote [DecidableEq Loc] {ctx : List Ty} {ty : Ty}
    (expression : Expr Loc Val ctx ty) (environment : Env Loc Val ctx) :
    Ty.denote Loc Val ty :=
  denoteNE expression environment

theorem denote_nonexpansive [DecidableEq Loc] {ctx : List Ty} {ty : Ty}
    (expression : Expr Loc Val ctx ty) : OFE.NonExpansive (denote expression) :=
  (denoteNE expression).nonexpansive

end Expr

namespace Formula

variable {Loc : Type u} {Val : Type v}

def denote [DecidableEq Loc] (formula : Formula Loc Val) : IProp Loc Val :=
  Expr.denote formula .nil

def Entails [DecidableEq Loc] (left right : Formula Loc Val) : Prop :=
  IProp.Entails left.denote right.denote

end Formula

scoped infix:25 " ⊢ " => Formula.Entails

end MPSL
