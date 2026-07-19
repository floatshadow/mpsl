import Lean.PrettyPrinter.Delaborator
import MPSL.Elab
import MPSL.ProofMode.Bunch

set_option autoImplicit false

namespace MPSL.ProofMode

open Lean Lean.Meta PrettyPrinter Delaborator SubExpr
open MPSL.Elab

/-
The syntax in this section is display-only.  In particular, a context entry
(`h : P`) is not an MPSL term and should not be fed back to the elaborator.
Keeping it in its own syntax category lets the InfoView show the logical
shape without changing the kernel representation of a proof-mode goal.
-/
declare_syntax_cat mpslDisplayContext
syntax ident " : " mpslTerm : mpslDisplayContext
syntax "∅" : mpslDisplayContext
syntax "(" mpslDisplayContext ")" " ∧ " "(" mpslDisplayContext ")" : mpslDisplayContext
syntax "(" mpslDisplayContext ")" " ∗ " "(" mpslDisplayContext ")" : mpslDisplayContext
declare_syntax_cat mpslDisplayGoal
syntax ppDedent(ppLine mpslDisplayContext) ppDedent(ppLine "⊢ " mpslTerm) : mpslDisplayGoal

private def tailArg? (expression : Lean.Expr) (offset : Nat := 0) : Option Lean.Expr :=
  let arguments := expression.getAppArgs
  if arguments.size > offset then some arguments[arguments.size - offset - 1]! else none

private def isApp (expression : Lean.Expr) (name : Name) : Bool :=
  expression.getAppFn.isConstOf name

private partial def varIndex? : Lean.Expr -> Option Nat
  | expression =>
      if isApp expression ``MPSL.Var.here then
        some 0
      else if isApp expression ``MPSL.Var.there then
        match tailArg? expression with
        | some argument => varIndex? argument |>.map (· + 1)
        | none => none
      else
        none

private partial def delabTy (expression : Lean.Expr) : DelabM
    (TSyntax `mpslTy) := do
  let name := expression.getAppFn.constName?
  match name with
  | some ``MPSL.Ty.loc => `(mpslTy| loc)
  | some ``MPSL.Ty.val => `(mpslTy| val)
  | some ``MPSL.Ty.iprop => `(mpslTy| iProp)
  | some ``MPSL.Ty.empty => `(mpslTy| 𝟘)
  | some ``MPSL.Ty.unit => `(mpslTy| 𝟙)
  | some ``MPSL.Ty.prod =>
      let args := expression.getAppArgs
      guard (args.size >= 2)
      let left ← delabTy args[args.size - 2]!
      let right ← delabTy args[args.size - 1]!
      `(mpslTy| ($left × $right))
  | some ``MPSL.Ty.sum =>
      let args := expression.getAppArgs
      guard (args.size >= 2)
      let left ← delabTy args[args.size - 2]!
      let right ← delabTy args[args.size - 1]!
      `(mpslTy| ($left + $right))
  | some ``MPSL.Ty.arr =>
      let args := expression.getAppArgs
      guard (args.size >= 2)
      let domain ← delabTy args[args.size - 2]!
      let codomain ← delabTy args[args.size - 1]!
      `(mpslTy| ($domain → $codomain))
  | _ => failure

private inductive BinaryOp where
  | and
  | or
  | sep
  | wand
  | imp
  | pointsTo

private partial def delabExpr (bound : Array String := #[]) : DelabM
    (TSyntax `mpslTerm) := do
  let expression ← getExpr
  let name := expression.getAppFn.constName?
  let arguments := expression.getAppArgs
  let binary (operator : BinaryOp) : DelabM (TSyntax `mpslTerm) := do
    guard (arguments.size >= 2)
    let left ← withNaryArg (arguments.size - 2) (delabExpr bound)
    let right ← withNaryArg (arguments.size - 1) (delabExpr bound)
    match operator with
    | .and => `(mpslTerm| ($left ∧ $right))
    | .or => `(mpslTerm| ($left ∨ $right))
    | .sep => `(mpslTerm| ($left ∗ $right))
    | .wand => `(mpslTerm| ($left -∗ $right))
    | .imp => `(mpslTerm| ($left ⇒ $right))
    | .pointsTo => `(mpslTerm| ($left ↦ $right))
  match name with
  | some ``MPSL.Expr.truth => `(mpslTerm| True)
  | some ``MPSL.Expr.falsum => `(mpslTerm| False)
  | some ``MPSL.Expr.unit => `(mpslTerm| ())
  | some ``MPSL.Expr.embed => do
      guard (arguments.size >= 1)
      let value ← withNaryArg (arguments.size - 1) delab
      `(mpslTerm| `$(value))
  | some ``MPSL.Expr.loc => do
      guard (arguments.size >= 1)
      let value ← withNaryArg (arguments.size - 1) delab
      `(mpslTerm| loc($(value)))
  | some ``MPSL.Expr.val => do
      guard (arguments.size >= 1)
      let value ← withNaryArg (arguments.size - 1) delab
      `(mpslTerm| val($(value)))
  | some ``MPSL.Expr.var => do
      guard (arguments.size >= 1)
      let some argument := tailArg? expression
        | failure
      let some index := varIndex? argument
        | failure
      let some name := if h : index < bound.size then some bound[index] else none
        | failure
      return ⟨mkIdent (Name.mkSimple name)⟩
  | some ``MPSL.Expr.and => binary .and
  | some ``MPSL.Expr.or => binary .or
  | some ``MPSL.Expr.sep => binary .sep
  | some ``MPSL.Expr.wand => binary .wand
  | some ``MPSL.Expr.imp => binary .imp
  | some ``MPSL.Expr.always => do
      guard (arguments.size >= 1)
      let body ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| □ $body)
  | some ``MPSL.Expr.later => do
      guard (arguments.size >= 1)
      let body ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| ▷ $body)
  | some ``MPSL.Expr.pointsTo => binary .pointsTo
  | some ``MPSL.Expr.eq => do
      guard (arguments.size >= 2)
      let left ← withNaryArg (arguments.size - 2) (delabExpr bound)
      let right ← withNaryArg (arguments.size - 1) (delabExpr bound)
      let ty ← delabTy arguments[arguments.size - 3]!
      `(mpslTerm| eq[$ty]($left, $right))
  | some ``MPSL.Expr.pair => do
      guard (arguments.size >= 2)
      let left ← withNaryArg (arguments.size - 2) (delabExpr bound)
      let right ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| ($left, $right))
  | some ``MPSL.Expr.app => do
      guard (arguments.size >= 2)
      let function ← withNaryArg (arguments.size - 2) (delabExpr bound)
      let argument ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| $function($argument))
  | some ``MPSL.Expr.lam => do
      guard (arguments.size >= 2)
      let ty ← delabTy arguments[arguments.size - 2]!
      let name := "x" ++ bound.size.repr
      let nameStx := mkIdent (Name.mkSimple name)
      let body ← withNaryArg (arguments.size - 1) (delabExpr (bound.insertIdx 0 name))
      `(mpslTerm| λ $nameStx : $ty, $body)
  | some ``MPSL.Expr.inl => do
      guard (arguments.size >= 2)
      let rightTy ← delabTy arguments[arguments.size - 2]!
      let value ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| inl[$rightTy]($value))
  | some ``MPSL.Expr.inr => do
      guard (arguments.size >= 2)
      let leftTy ← delabTy arguments[arguments.size - 2]!
      let value ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| inr[$leftTy]($value))
  | some ``MPSL.Expr.fst => do
      let value ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| fst $value)
  | some ``MPSL.Expr.snd => do
      let value ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| snd $value)
  | some ``MPSL.Expr.case => do
      guard (arguments.size >= 3)
      let scrutinee ← withNaryArg (arguments.size - 3) (delabExpr bound)
      let leftName := "inl" ++ bound.size.repr
      let rightName := "inr" ++ bound.size.repr
      let leftNameStx := mkIdent (Name.mkSimple leftName)
      let rightNameStx := mkIdent (Name.mkSimple rightName)
      let leftBody ← withNaryArg (arguments.size - 2)
        (delabExpr (bound.insertIdx 0 leftName))
      let rightBody ← withNaryArg (arguments.size - 1)
        (delabExpr (bound.insertIdx 0 rightName))
      `(mpslTerm| case $scrutinee of
        | inl $leftNameStx => $leftBody
        | inr $rightNameStx => $rightBody)
  | some ``MPSL.Expr.all => do
      guard (arguments.size >= 2)
      let ty ← delabTy arguments[arguments.size - 2]!
      let name := "x" ++ bound.size.repr
      let body ← withNaryArg (arguments.size - 1) (delabExpr (bound.insertIdx 0 name))
      let nameStx : TSyntax `ident := ⟨mkIdent (Name.mkSimple name)⟩
      `(mpslTerm| ∀ $nameStx : $ty, $body)
  | some ``MPSL.Expr.ex => do
      guard (arguments.size >= 2)
      let ty ← delabTy arguments[arguments.size - 2]!
      let name := "x" ++ bound.size.repr
      let body ← withNaryArg (arguments.size - 1) (delabExpr (bound.insertIdx 0 name))
      let nameStx := mkIdent (Name.mkSimple name)
      `(mpslTerm| ∃ $nameStx : $ty, $body)
  | _ => failure

private partial def delabFormula : DelabM
    (TSyntax `mpslTerm) := do
  let expression ← getExpr
  let arguments := expression.getAppArgs
  if isApp expression ``MPSL.Formula.denote then
    guard (arguments.size >= 1)
    return ← withNaryArg (arguments.size - 1) delabExpr
  if isApp expression ``MPSL.Expr.denote then
    guard (arguments.size >= 2)
    return ← withNaryArg (arguments.size - 2) delabExpr
  if isApp expression ``MPSL.NEFun.toFun then
    guard (arguments.size >= 2)
    let function := arguments[arguments.size - 2]!
    if isApp function ``MPSL.Expr.denoteNE then
      let functionArgs := function.getAppArgs
      guard (functionArgs.size >= 1)
      return ← withNaryArg (arguments.size - 2) <| withNaryArg
        (functionArgs.size - 1) delabExpr
  failure

private partial def delabContext : DelabM
    (TSyntax `mpslDisplayContext) := do
  let expression ← getExpr
  let arguments := expression.getAppArgs
  let name := expression.getAppFn.constName?
  match name with
  | some ``MPSL.ProofMode.Bunch.empty => `(mpslDisplayContext| ∅)
  | some ``MPSL.ProofMode.Bunch.hyp => do
      guard (arguments.size >= 2)
      let nameExpression := arguments[arguments.size - 2]!
      let .lit (.strVal name) := nameExpression
        | failure
      let assertion ← withNaryArg (arguments.size - 1) delabFormula
      let nameStx := mkIdent (Name.mkSimple name)
      `(mpslDisplayContext| $nameStx:ident : $assertion:mpslTerm)
  | some ``MPSL.ProofMode.Bunch.additive => do
      guard (arguments.size >= 2)
      let left ← withNaryArg (arguments.size - 2) delabContext
      let right ← withNaryArg (arguments.size - 1) delabContext
      `(mpslDisplayContext| ($left:mpslDisplayContext) ∧ ($right:mpslDisplayContext))
  | some ``MPSL.ProofMode.Bunch.multiplicative => do
      guard (arguments.size >= 2)
      let left ← withNaryArg (arguments.size - 2) delabContext
      let right ← withNaryArg (arguments.size - 1) delabContext
      `(mpslDisplayContext| ($left:mpslDisplayContext) ∗ ($right:mpslDisplayContext))
  | _ => failure

@[app_delab MPSL.ProofMode.Valid]
private partial def delabValid : Delab := do
  guard !(← getPPOption getPPAll)
  guard (← getPPOption getPPNotation)
  let expression ← getExpr
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  let context ← withNaryArg (arguments.size - 2) delabContext
  let goal ← withNaryArg (arguments.size - 1) delabFormula
  return ⟨← `(mpslDisplayGoal| $context:mpslDisplayContext ⊢ $goal:mpslTerm)⟩

end MPSL.ProofMode
