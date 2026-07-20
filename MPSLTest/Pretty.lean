import MPSL

set_option autoImplicit false

namespace MPSL.Test

/-- Assert the user-facing rendering of the current MPSL proof-mode goal. -/
def assertPretty (expected : Array String) : Lean.Elab.Tactic.TacticM Unit :=
    Lean.Elab.Tactic.withMainContext do
  let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  let output := (← Lean.Meta.ppExpr target).pretty
  let actual := output.splitOn "\n" |>.filter (· != "") |>.toArray
  unless actual == expected do
    throwError "unexpected pretty-printed goal:\n{output}"
  for internal in #["ProofMode.Valid", "Hypothesis.assertion", "Context.denote",
      "Environment.andDenote", "Environment.sepDenote", "IProp.Entails",
      "Expr.denoteNE", "NEFun.toFun"] do
    if output.contains internal then
      throwError "pretty-printed goal exposes folded/internal form '{internal}':\n{output}"

end MPSL.Test
