import MPSL
import MPSLTest.Model

set_option autoImplicit false

namespace MPSL.PrettyPrintTests

open scoped MPSL
open MPSL.TestModel

private def assertPretty (included : Array String) : Lean.Elab.Tactic.TacticM Unit :=
    Lean.Elab.Tactic.withMainContext do
  let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  let output := (← Lean.Meta.ppExpr target).pretty
  for expected in included do
    unless output.contains expected do
      throwError "pretty-printed goal does not contain '{expected}':\n{output}"
  for internal in #["ProofMode.Valid", "Formula.denote", "Expr.denoteNE"] do
    if output.contains internal then
      throwError "pretty-printed goal exposes '{internal}':\n{output}"

/- These checks exercise the same expression printer used by Lean's InfoView.
   They cover both the initial `Formula.denote` representation and the
   `Expr.denoteNE` representation produced by proof-mode rules. -/
example (P Q R : Formula Location Value) :
    mpsl{ (`P ∗ `Q) ∗ `R } ⊢
      mpsl{ (`P ∗ `Q) ∗ True } := by
  mstart h
  run_tac assertPretty #["h :", "`P ∗ `Q", "⊢", "True"]
  mdestruct h as hPQ hR
  run_tac assertPretty #["hPQ :", "hR :", "∗"]
  mframe hPQ
  run_tac assertPretty #["∅", "hR :", "⊢ True"]
  mtruth

example (P : Formula Location Value) :
    mpsl{ (∃ x : loc, x =[loc] x) ∗ `P } ⊢
      mpsl{ True } := by
  mstart h
  run_tac assertPretty #["∃ x0 : loc", "eq[loc](x0, x0)", "`P"]
  mtruth

example :
    (mpsl{ (λ P : iProp, P ∗ P)(True) } : Formula Location Value) ⊢
      mpsl{ True } := by
  mstart h
  run_tac assertPretty #["λ x0 : iProp", "x0 ∗ x0", "⊢ True"]
  mtruth

end MPSL.PrettyPrintTests
