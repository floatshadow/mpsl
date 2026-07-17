import MPSL.Syntax.Expr
import MPSL.Semantics.Connectives

set_option autoImplicit false

namespace MPSL

universe u v

namespace Ty

/-- Semantic carrier of an object-language type. -/
def denote (Loc : Type u) (Val : Type v) : Ty -> Type (max u v)
  | .loc => ULift.{max u v, u} Loc
  | .val => ULift.{max u v, v} Val
  | .iprop => IProp Loc Val
  | .empty => ULift.{max u v, 0} Empty
  | .unit => ULift.{max u v, 0} Unit
  | .prod left right => denote Loc Val left × denote Loc Val right
  | .sum left right => Sum (denote Loc Val left) (denote Loc Val right)
  | .arr domain codomain => denote Loc Val domain -> denote Loc Val codomain

/-- Indexed equivalence on values of each object-language type. -/
def EquivAt (Loc : Type u) (Val : Type v) :
    (ty : Ty) -> Nat -> denote Loc Val ty -> denote Loc Val ty -> Prop
  | .loc, _, left, right => left = right
  | .val, _, left, right => left = right
  | .iprop, step, left, right => IProp.EquivAt step left right
  | .empty, _, left, _ => nomatch left.down
  | .unit, _, _, _ => True
  | .prod leftTy rightTy, step, left, right =>
      EquivAt Loc Val leftTy step left.1 right.1 ∧
      EquivAt Loc Val rightTy step left.2 right.2
  | .sum leftTy _, step, .inl left, .inl right => EquivAt Loc Val leftTy step left right
  | .sum _ rightTy, step, .inr left, .inr right => EquivAt Loc Val rightTy step left right
  | .sum _ _, _, .inl _, .inr _ => False
  | .sum _ _, _, .inr _, .inl _ => False
  | .arr _ codomain, step, left, right =>
      forall value, EquivAt Loc Val codomain step (left value) (right value)

theorem equivAt_mono (Loc : Type u) (Val : Type v) (ty : Ty)
    {smaller larger : Nat} {left right : denote Loc Val ty} :
    smaller <= larger ->
    EquivAt Loc Val ty larger left right ->
    EquivAt Loc Val ty smaller left right := by
  intro included equivalent
  induction ty with
  | loc => exact equivalent
  | val => exact equivalent
  | iprop => exact IProp.equivAt_mono included equivalent
  | empty => exact Empty.elim left.down
  | unit => trivial
  | prod leftTy rightTy leftIH rightIH =>
      exact ⟨leftIH equivalent.1, rightIH equivalent.2⟩
  | sum leftTy rightTy leftIH rightIH =>
      cases left <;> cases right
      · exact leftIH equivalent
      · exact equivalent
      · exact equivalent
      · exact rightIH equivalent
  | arr domain codomain domainIH codomainIH =>
      intro value
      exact codomainIH (equivalent value)

theorem equivAt_refl (Loc : Type u) (Val : Type v) (ty : Ty)
    {step : Nat} (value : denote Loc Val ty) : EquivAt Loc Val ty step value value := by
  induction ty with
  | loc => rfl
  | val => rfl
  | iprop =>
      intro heap
      exact SProp.equivAt_refl step (value.holds heap)
  | empty => exact Empty.elim value.down
  | unit => trivial
  | prod left right leftIH rightIH => exact ⟨leftIH value.1, rightIH value.2⟩
  | sum left right leftIH rightIH =>
      cases value with
      | inl value => exact leftIH value
      | inr value => exact rightIH value
  | arr domain codomain domainIH codomainIH =>
      intro argument
      exact codomainIH (value argument)

theorem equivAt_symm (Loc : Type u) (Val : Type v) (ty : Ty)
    {step : Nat} {left right : denote Loc Val ty} :
    EquivAt Loc Val ty step left right -> EquivAt Loc Val ty step right left := by
  intro equivalent
  induction ty with
  | loc => exact equivalent.symm
  | val => exact equivalent.symm
  | iprop => intro heap; exact SProp.equivAt_symm (equivalent heap)
  | empty => exact Empty.elim left.down
  | unit => trivial
  | prod leftTy rightTy leftIH rightIH => exact ⟨leftIH equivalent.1, rightIH equivalent.2⟩
  | sum leftTy rightTy leftIH rightIH =>
      cases left <;> cases right
      · exact leftIH equivalent
      · exact equivalent
      · exact equivalent
      · exact rightIH equivalent
  | arr domain codomain domainIH codomainIH =>
      intro argument
      exact codomainIH (equivalent argument)

theorem equivAt_trans (Loc : Type u) (Val : Type v) (ty : Ty)
    {step : Nat} {first second third : denote Loc Val ty} :
    EquivAt Loc Val ty step first second ->
    EquivAt Loc Val ty step second third ->
    EquivAt Loc Val ty step first third := by
  intro firstSecond secondThird
  induction ty with
  | loc => exact firstSecond.trans secondThird
  | val => exact firstSecond.trans secondThird
  | iprop =>
      intro heap
      exact SProp.equivAt_trans (firstSecond heap) (secondThird heap)
  | empty => exact Empty.elim first.down
  | unit => trivial
  | prod leftTy rightTy leftIH rightIH =>
      exact ⟨leftIH firstSecond.1 secondThird.1, rightIH firstSecond.2 secondThird.2⟩
  | sum leftTy rightTy leftIH rightIH =>
      cases first <;> cases second <;> cases third
      · exact leftIH firstSecond secondThird
      · exact False.elim secondThird
      · exact False.elim firstSecond
      · exact False.elim firstSecond
      · exact False.elim firstSecond
      · exact False.elim firstSecond
      · exact False.elim secondThird
      · exact rightIH firstSecond secondThird
  | arr domain codomain domainIH codomainIH =>
      intro argument
      exact codomainIH (firstSecond argument) (secondThird argument)

end Ty

/-- A semantic environment matching an intrinsic object-language context. -/
inductive Env (Loc : Type u) (Val : Type v) : List Ty -> Type (max u v) where
  | nil : Env Loc Val []
  | cons {ty : Ty} {ctx : List Ty} :
      Ty.denote Loc Val ty -> Env Loc Val ctx -> Env Loc Val (ty :: ctx)

namespace Var

def denote {Loc : Type u} {Val : Type v} {ctx : List Ty} {ty : Ty} :
    Var ctx ty -> Env Loc Val ctx -> Ty.denote Loc Val ty
  | .here, .cons value _ => value
  | .there boundVar, .cons _ rest => denote boundVar rest

end Var

namespace Expr

variable {Loc : Type u} {Val : Type v}

/-- Interpret a typed expression in the fixed step-indexed heap model. -/
def denote [DecidableEq Loc] {ctx : List Ty} {ty : Ty} :
    Expr Loc Val ctx ty -> Env Loc Val ctx -> Ty.denote Loc Val ty
  | .var boundVar, environment => boundVar.denote environment
  | .embed expression, _ => denote expression .nil
  | .loc location, _ => ULift.up location
  | .val value, _ => ULift.up value
  | .unit, _ => ULift.up ()
  | .lam body, environment => fun argument => denote body (.cons argument environment)
  | .app function argument, environment =>
      denote function environment (denote argument environment)
  | .pair left right, environment => (denote left environment, denote right environment)
  | .fst product, environment => (denote product environment).1
  | .snd product, environment => (denote product environment).2
  | .inl _ value, environment => Sum.inl (denote value environment)
  | .inr _ value, environment => Sum.inr (denote value environment)
  | .case scrutinee leftBranch rightBranch, environment =>
      match denote scrutinee environment with
      | .inl value => denote leftBranch (.cons value environment)
      | .inr value => denote rightBranch (.cons value environment)
  | .falsum, _ => IProp.falsum
  | .truth, _ => IProp.truth
  | @Expr.eq _ _ _ comparedTy left right, environment =>
      let leftValue := denote left environment
      let rightValue := denote right environment
      IProp.equal (Ty.EquivAt Loc Val comparedTy)
        (Ty.equivAt_mono Loc Val comparedTy) leftValue rightValue
  | .imp left right, environment => IProp.imp (denote left environment) (denote right environment)
  | .and left right, environment => IProp.and (denote left environment) (denote right environment)
  | .or left right, environment => IProp.or (denote left environment) (denote right environment)
  | .sep left right, environment => IProp.sep (denote left environment) (denote right environment)
  | .wand left right, environment => IProp.wand (denote left environment) (denote right environment)
  | .ex body, environment =>
      IProp.exists_ fun witness => denote body (.cons witness environment)
  | .all body, environment =>
      IProp.forall_ fun witness => denote body (.cons witness environment)
  | .pointsTo location value, environment =>
      IProp.pointsTo (denote location environment).down (denote value environment).down
  | .always proposition, environment => IProp.always (denote proposition environment)
  | .later proposition, environment => IProp.later (denote proposition environment)

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
