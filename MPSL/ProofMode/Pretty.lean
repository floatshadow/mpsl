import Lean.PrettyPrinter.Delaborator
import MPSL.Elab
import MPSL.ProofMode.Context

set_option autoImplicit false

namespace MPSL.ProofMode

open Lean Lean.Meta PrettyPrinter Delaborator SubExpr
open MPSL.Elab

syntax:max "$!" term:max : mpslTerm

/- The pure context is Lean's local context, which InfoView prints immediately
above this display-only rendering of the object-logic proof state. -/
declare_syntax_cat mpslDisplayHypothesis
syntax ident " : " mpslTerm : mpslDisplayHypothesis

declare_syntax_cat mpslDisplayEnvironment
syntax "∅" : mpslDisplayEnvironment
syntax mpslDisplayHypothesis : mpslDisplayEnvironment
syntax mpslDisplayHypothesis
  ppDedent(ppLine mpslDisplayEnvironment) : mpslDisplayEnvironment

declare_syntax_cat mpslDisplayGoal
syntax
  ppDedent(ppLine mpslDisplayEnvironment)
  ppDedent(ppLine "──────────────────────────────────────☐")
  ppDedent(ppLine mpslDisplayEnvironment)
  ppDedent(ppLine "──────────────────────────────────────∗")
  ppDedent(ppLine mpslTerm) : mpslDisplayGoal

declare_syntax_cat mpslDisplayEntailment
syntax "(" mpslTerm ")" ppSpace "⊢ᵢ" ppSpace "(" mpslTerm ")" : mpslDisplayEntailment
syntax
  ppDedent(ppLine "──────────────────────────────────────☐")
  ppDedent(ppLine mpslDisplayEnvironment)
  ppDedent(ppLine "──────────────────────────────────────∗")
  ppDedent(ppLine mpslTerm) : mpslDisplayGoal
syntax
  ppDedent(ppLine mpslDisplayEnvironment)
  ppDedent(ppLine "──────────────────────────────────────☐")
  ppDedent(ppLine "──────────────────────────────────────∗")
  ppDedent(ppLine mpslTerm) : mpslDisplayGoal
syntax
  ppDedent(ppLine "──────────────────────────────────────☐")
  ppDedent(ppLine "──────────────────────────────────────∗")
  ppDedent(ppLine mpslTerm) : mpslDisplayGoal

private def tailArg? (expression : Lean.Expr) (offset : Nat := 0) : Option Lean.Expr :=
  let arguments := expression.getAppArgs
  if arguments.size > offset then some arguments[arguments.size - offset - 1]! else none

private def isApp (expression : Lean.Expr) (name : Name) : Bool :=
  expression.getAppFn.isConstOf name

private def withExpression {α : Type} (expression : Lean.Expr) (action : DelabM α) : DelabM α :=
  withTheReader Lean.SubExpr (fun state => { state with expr := expression }) action

/-- Remove proof-mode record projections while preserving semantic connective heads. -/
private partial def reduceDisplayProjections (expression : Lean.Expr) : MetaM Lean.Expr := do
  if isApp expression ``MPSL.ProofMode.Hypothesis.assertion then
    let some hypothesis := tailArg? expression | return expression
    let hypothesis ← whnf hypothesis
    if isApp hypothesis ``MPSL.ProofMode.Hypothesis.mk then
      let some assertion := tailArg? hypothesis | return expression
      return ← reduceDisplayProjections assertion
  if let some reduced ← reduceProj? expression then
    return ← reduceDisplayProjections reduced
  match expression with
  | .mdata _ body => reduceDisplayProjections body
  | _ => return expression

private partial def delabSemanticEnvironment (expression : Lean.Expr) :
    DelabM (Array (TSyntax `mpslTerm)) := do
  let expression ← whnf expression
  let arguments := expression.getAppArgs
  if expression.getAppFn.isConstOf ``MPSL.Env.nil then
    return #[]
  if expression.getAppFn.isConstOf ``MPSL.Env.cons then
    guard (arguments.size >= 2)
    let value ← withExpression arguments[arguments.size - 2]! delab
    let displayed : TSyntax `mpslTerm ←
      if value.raw.isIdent then pure ⟨value.raw⟩ else `(mpslTerm| $! $value:term)
    let rest ← delabSemanticEnvironment arguments[arguments.size - 1]!
    return #[displayed] ++ rest
  failure

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

private partial def delabTy (expression : Lean.Expr) : DelabM (TSyntax `mpslTy) := do
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

private partial def delabExpr (bound : Array (TSyntax `mpslTerm) := #[]) :
    DelabM (TSyntax `mpslTerm) := do
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
      let some argument := tailArg? expression | failure
      let some index := varIndex? argument | failure
      let some boundValue := if h : index < bound.size then some bound[index] else none | failure
      return boundValue
  | some ``MPSL.Expr.and => binary .and
  | some ``MPSL.Expr.or => binary .or
  | some ``MPSL.Expr.sep => binary .sep
  | some ``MPSL.Expr.wand => binary .wand
  | some ``MPSL.Expr.imp => binary .imp
  | some ``MPSL.Expr.always => do
      let body ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| □ $body)
  | some ``MPSL.Expr.later => do
      let body ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| ▷ $body)
  | some ``MPSL.Expr.pointsTo => binary .pointsTo
  | some ``MPSL.Expr.eq => do
      guard (arguments.size >= 3)
      let ty ← delabTy arguments[arguments.size - 3]!
      let left ← withNaryArg (arguments.size - 2) (delabExpr bound)
      let right ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| $left =[$ty] $right)
  | some ``MPSL.Expr.pair => do
      let left ← withNaryArg (arguments.size - 2) (delabExpr bound)
      let right ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| ($left, $right))
  | some ``MPSL.Expr.app => do
      let function ← withNaryArg (arguments.size - 2) (delabExpr bound)
      let argument ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| $function($argument))
  | some ``MPSL.Expr.lam => do
      let ty ← delabTy arguments[arguments.size - 2]!
      let name := "x" ++ bound.size.repr
      let nameStx := mkIdent (Name.mkSimple name)
      let boundValue : TSyntax `mpslTerm := ⟨nameStx⟩
      let body ← withNaryArg (arguments.size - 1)
        (delabExpr (bound.insertIdx 0 boundValue))
      `(mpslTerm| λ $nameStx : $ty, $body)
  | some ``MPSL.Expr.inl => do
      let rightTy ← delabTy arguments[arguments.size - 2]!
      let value ← withNaryArg (arguments.size - 1) (delabExpr bound)
      `(mpslTerm| inl[$rightTy]($value))
  | some ``MPSL.Expr.inr => do
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
      let scrutinee ← withNaryArg (arguments.size - 3) (delabExpr bound)
      let leftName := "inl" ++ bound.size.repr
      let rightName := "inr" ++ bound.size.repr
      let leftNameStx := mkIdent (Name.mkSimple leftName)
      let rightNameStx := mkIdent (Name.mkSimple rightName)
      let leftVariable : TSyntax `mpslTerm := ⟨leftNameStx⟩
      let rightVariable : TSyntax `mpslTerm := ⟨rightNameStx⟩
      let leftBody ← withNaryArg (arguments.size - 2)
        (delabExpr (bound.insertIdx 0 leftVariable))
      let rightBody ← withNaryArg (arguments.size - 1)
        (delabExpr (bound.insertIdx 0 rightVariable))
      `(mpslTerm| case $scrutinee of
        | inl $leftNameStx => $leftBody
        | inr $rightNameStx => $rightBody)
  | some ``MPSL.Expr.all => do
      let ty ← delabTy arguments[arguments.size - 2]!
      let name := "x" ++ bound.size.repr
      let nameStx := mkIdent (Name.mkSimple name)
      let boundValue : TSyntax `mpslTerm := ⟨nameStx⟩
      let body ← withNaryArg (arguments.size - 1)
        (delabExpr (bound.insertIdx 0 boundValue))
      `(mpslTerm| ∀ $nameStx : $ty, $body)
  | some ``MPSL.Expr.ex => do
      let ty ← delabTy arguments[arguments.size - 2]!
      let name := "x" ++ bound.size.repr
      let nameStx := mkIdent (Name.mkSimple name)
      let boundValue : TSyntax `mpslTerm := ⟨nameStx⟩
      let body ← withNaryArg (arguments.size - 1)
        (delabExpr (bound.insertIdx 0 boundValue))
      `(mpslTerm| ∃ $nameStx : $ty, $body)
  | _ => failure

private partial def delabFormula : DelabM (TSyntax `mpslTerm) := do
  let expression ← reduceDisplayProjections (← getExpr)
  let arguments := expression.getAppArgs
  if isApp expression ``MPSL.Formula.denote then
    guard (arguments.size >= 1)
    let formula := arguments[arguments.size - 1]!
    if formula.getAppFn.isFVar then
      let value ← withExpression formula delab
      return ← `(mpslTerm| `$(value))
    return ← withExpression formula delabExpr
  if isApp expression ``MPSL.Expr.denote then
    guard (arguments.size >= 2)
    return ← withExpression arguments[arguments.size - 2]! delabExpr
  if isApp expression ``MPSL.NEFun.toFun then
    guard (arguments.size >= 2)
    let function := arguments[arguments.size - 2]!
    if isApp function ``MPSL.Expr.denoteNE then
      let functionArgs := function.getAppArgs
      guard (functionArgs.size >= 1)
      let bound ← delabSemanticEnvironment arguments[arguments.size - 1]!
      return ← withExpression functionArgs[functionArgs.size - 1]! (delabExpr bound)
  failure

private partial def delabIProp : DelabM (TSyntax `mpslTerm) := do
  let expression ← reduceDisplayProjections (← getExpr)
  let arguments := expression.getAppArgs
  let unary (constructor : TSyntax `mpslTerm -> DelabM (TSyntax `mpslTerm)) := do
    guard (arguments.size >= 1)
    let body ← withExpression arguments[arguments.size - 1]! delabIProp
    constructor body
  if isApp expression ``MPSL.IProp.always then
    return ← unary fun body => `(mpslTerm| □ $body)
  if isApp expression ``MPSL.IProp.later then
    return ← unary fun body => `(mpslTerm| ▷ $body)
  withExpression expression delabFormula

@[app_delab MPSL.IProp.Entails]
private def delabEntails : Delab := do
  guard !(← getPPOption getPPAll)
  guard (← getPPOption getPPNotation)
  let expression ← getExpr
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  let left ← withNaryArg (arguments.size - 2) delabIProp
  let right ← withNaryArg (arguments.size - 1) delabIProp
  return ⟨← `(mpslDisplayEntailment| ($left:mpslTerm) ⊢ᵢ ($right:mpslTerm))⟩

private def delabHypothesis (expression : Lean.Expr) :
    DelabM (TSyntax `mpslDisplayHypothesis) := do
  let expression ← whnf expression
  guard (expression.getAppFn.isConstOf ``MPSL.ProofMode.Hypothesis.mk)
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  let .lit (.strVal name) := arguments[arguments.size - 2]! | failure
  let assertion ← withExpression arguments[arguments.size - 1]! delabFormula
  let nameStx := mkIdent (Name.mkSimple name)
  `(mpslDisplayHypothesis| $nameStx:ident : $assertion:mpslTerm)

private partial def delabEnvironment (expression : Lean.Expr) :
    DelabM (Array (TSyntax `mpslDisplayHypothesis)) := do
  let expression ← whnf expression
  let arguments := expression.getAppArgs
  if expression.getAppFn.isConstOf ``List.nil then
    return #[]
  if expression.getAppFn.isConstOf ``List.cons then
    guard (arguments.size >= 2)
    let head ← delabHypothesis arguments[arguments.size - 2]!
    let tail ← delabEnvironment arguments[arguments.size - 1]!
    return #[head] ++ tail
  failure

private def environmentSyntax (hypotheses : Array (TSyntax `mpslDisplayHypothesis)) :
    DelabM (TSyntax `mpslDisplayEnvironment) := do
  if hypotheses.isEmpty then
    return ← `(mpslDisplayEnvironment| ∅)
  let last := hypotheses[hypotheses.size - 1]!
  let mut result ← `(mpslDisplayEnvironment| $last:mpslDisplayHypothesis)
  for index in (List.range (hypotheses.size - 1)).reverse do
    let hypothesis := hypotheses[index]!
    result ← `(mpslDisplayEnvironment|
      $hypothesis:mpslDisplayHypothesis
      $result:mpslDisplayEnvironment)
  return result

private def delabContext (expression : Lean.Expr) : DelabM
    (Array (TSyntax `mpslDisplayHypothesis) ×
      Array (TSyntax `mpslDisplayHypothesis)) := do
  let expression ← whnf expression
  guard (expression.getAppFn.isConstOf ``MPSL.ProofMode.Context.mk)
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  let persistent ← delabEnvironment arguments[arguments.size - 2]!
  let spatial ← delabEnvironment arguments[arguments.size - 1]!
  return (persistent, spatial)

@[app_delab MPSL.ProofMode.Valid]
private def delabValid : Delab := do
  guard !(← getPPOption getPPAll)
  guard (← getPPOption getPPNotation)
  let expression ← getExpr
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  let (persistent, spatial) ← delabContext arguments[arguments.size - 2]!
  let goal ← withNaryArg (arguments.size - 1) delabFormula
  if persistent.isEmpty then
    if spatial.isEmpty then
      return ⟨← `(mpslDisplayGoal|
        ──────────────────────────────────────☐
        ──────────────────────────────────────∗
        $goal:mpslTerm)⟩
    else
      let spatial ← environmentSyntax spatial
      return ⟨← `(mpslDisplayGoal|
        ──────────────────────────────────────☐
        $spatial:mpslDisplayEnvironment
        ──────────────────────────────────────∗
        $goal:mpslTerm)⟩
  else
    let persistent ← environmentSyntax persistent
    if spatial.isEmpty then
      return ⟨← `(mpslDisplayGoal|
        $persistent:mpslDisplayEnvironment
        ──────────────────────────────────────☐
        ──────────────────────────────────────∗
        $goal:mpslTerm)⟩
    else
      let spatial ← environmentSyntax spatial
      return ⟨← `(mpslDisplayGoal|
        $persistent:mpslDisplayEnvironment
        ──────────────────────────────────────☐
        $spatial:mpslDisplayEnvironment
        ──────────────────────────────────────∗
        $goal:mpslTerm)⟩

end MPSL.ProofMode
