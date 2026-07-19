import Lean.Elab.Tactic
import MPSL.Elab
import MPSL.ProofMode.Rules

syntax (name := mstart) "mstart " ident : tactic
syntax (name := mexact) "mexact " ident : tactic
syntax (name := mintro) "mintro " ident : tactic
syntax (name := mdestruct) "mdestruct " ident " as " ident ident : tactic
syntax (name := msplit) "msplit" : tactic
syntax (name := mleft) "mleft" : tactic
syntax (name := mright) "mright" : tactic
syntax (name := msep) "msep" : tactic
syntax (name := msepSwap) "msep" "(" "swap" ")" : tactic
syntax (name := msepPartition) "msep" " [" ident,+ "]" : tactic
syntax (name := mapply) "mapply" : tactic
syntax (name := mapplyNamed) "mapply " ident ident : tactic
syntax (name := massumption) "massumption" : tactic
syntax (name := mtruth) "mtruth" : tactic
syntax (name := mfalse) "mfalse " ident : tactic
syntax (name := mrefl) "mrefl" : tactic
syntax (name := msymm) "msymm " ident : tactic
syntax (name := mtrans) "mtrans " ident ident : tactic
syntax (name := mexistsDsl) "mexists " mpslTerm : tactic
syntax (name := mforall) "mforall " ident : tactic
syntax (name := mopenExists) "mopenexists " ident " as " ident ident : tactic
syntax (name := mspecializeDsl) "mspecialize " ident " at " mpslTerm " as " ident : tactic
syntax (name := malways) "malways" : tactic
syntax (name := mopenAlways) "mopen " ident " as " ident : tactic
syntax (name := mdup) "mdup " ident " as " ident ident : tactic
syntax (name := mlater) "mlater" : tactic
syntax (name := mopenLater) "mopenlater " ident " as " ident : tactic
syntax (name := mclear) "mclear " ident : tactic
syntax (name := mframe) "mframe " ident : tactic
syntax (name := mframeMany) "mframe" " [" ident,+ "]" : tactic
syntax (name := mnormalize) "mnormalize" : tactic
syntax (name := mstop) "mstop" : tactic
syntax (name := mguardFresh) "_mpsl_guard_fresh" " [" ident,* "]" : tactic
syntax (name := mguardReplace) "_mpsl_guard_replace " ident " [" ident,* "]" : tactic

namespace MPSL.ProofMode.Tactic

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

private structure NamedAssertion where
  name : String
  assertion : Lean.Expr

private def validTarget : TacticM (Lean.Expr × Lean.Expr) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.getAppFn.isConstOf ``MPSL.ProofMode.Valid do
    throwError "MPSL proof-mode tactic requires a Valid context goal"
  let arguments := target.getAppArgs
  if arguments.size < 2 then
    throwError "malformed MPSL proof-mode goal"
  return (arguments[arguments.size - 2]!, arguments[arguments.size - 1]!)

private def stringValue (expression : Lean.Expr) : MetaM String := do
  let expression ← instantiateMVars expression
  match expression with
  | .lit (.strVal value) => return value
  | _ => throwError "MPSL hypothesis name is not a string literal"

private partial def assertions (context : Lean.Expr) : MetaM (Array NamedAssertion) := do
  let context ← whnf (← instantiateMVars context)
  let function := context.getAppFn
  let arguments := context.getAppArgs
  if function.isConstOf ``MPSL.ProofMode.Bunch.empty then
    return #[]
  else if function.isConstOf ``MPSL.ProofMode.Bunch.hyp then
    return #[⟨← stringValue arguments[arguments.size - 2]!,
      arguments[arguments.size - 1]!⟩]
  else if function.isConstOf ``MPSL.ProofMode.Bunch.additive ||
      function.isConstOf ``MPSL.ProofMode.Bunch.multiplicative then
    let left ← assertions arguments[arguments.size - 2]!
    let right ← assertions arguments[arguments.size - 1]!
    return left ++ right
  else
    throwError "MPSL proof-mode context is not reducible to a bunch"

private def guardNames (removed : Option String) (newNames : Array String) : TacticM Unit :=
    withMainContext do
  let (context, _) ← validTarget
  let existing ← assertions context
  let mut seen : Array String := #[]
  for hypothesis in existing do
    if removed != some hypothesis.name then
      seen := seen.push hypothesis.name
  for name in newNames do
    if seen.contains name then
      throwError "duplicate proof-mode hypothesis name '{name}'"
    seen := seen.push name

private def findMatching (candidates : Array NamedAssertion) (target : Lean.Expr) :
    MetaM (Option NamedAssertion) := do
  for candidate in candidates do
    if ← isDefEq candidate.assertion target then
      return some candidate
  return none

elab_rules (kind := mguardFresh) : tactic
  | `(tactic| _mpsl_guard_fresh [$names:ident,*]) => do
      guardNames none (names.getElems.map (·.getId.toString))

elab_rules (kind := mguardReplace) : tactic
  | `(tactic| _mpsl_guard_replace $source:ident [$names:ident,*]) => do
      guardNames (some source.getId.toString) (names.getElems.map (·.getId.toString))

elab_rules (kind := massumption) : tactic
  | `(tactic| massumption) => withMainContext do
      let (context, goal) ← validTarget
      let some candidate ← findMatching (← assertions context) goal
        | throwError "massumption found no definitionally matching hypothesis"
      let label := Lean.quote (k := `term) candidate.name
      evalTactic (← `(tactic|
        exact MPSL.ProofMode.exactNamed $label (by rfl) (by rfl)))

end MPSL.ProofMode.Tactic

macro_rules (kind := mstart)
  | `(tactic| mstart $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.start $label)

macro_rules (kind := mexact)
  | `(tactic| mexact $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| exact MPSL.ProofMode.exactNamed $label (by rfl) (by rfl))

macro_rules (kind := mintro)
  | `(tactic| mintro $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_fresh [$name]; first
        | apply MPSL.ProofMode.impIntro $label
        | apply MPSL.ProofMode.wandIntro $label)

macro_rules (kind := mdestruct)
  | `(tactic| mdestruct $source:ident as $left:ident $right:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let leftLabel := Lean.quote left.getId.toString
      let rightLabel := Lean.quote right.getId.toString
      `(tactic| _mpsl_guard_replace $source [$left, $right]; first
        | apply MPSL.ProofMode.andDestruct $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.sepDestruct $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.orDestructAt $sourceLabel $leftLabel $rightLabel (by rfl))

macro_rules (kind := msplit)
  | `(tactic| msplit) => `(tactic| apply MPSL.ProofMode.andIntro)

macro_rules (kind := mleft)
  | `(tactic| mleft) => `(tactic| apply MPSL.ProofMode.orIntroLeft)

macro_rules (kind := mright)
  | `(tactic| mright) => `(tactic| apply MPSL.ProofMode.orIntroRight)

macro_rules (kind := msep)
  | `(tactic| msep) => `(tactic| apply MPSL.ProofMode.sepIntro)

macro_rules (kind := msepSwap)
  | `(tactic| msep (swap)) => `(tactic| apply MPSL.ProofMode.sepIntroSwap)

macro_rules (kind := msepPartition)
  | `(tactic| msep [$names:ident,*]) => do
      let labels : Array (Lean.TSyntax `term) :=
        names.getElems.map fun name => Lean.quote (k := `term) name.getId.toString
      `(tactic| apply MPSL.ProofMode.sepIntroPartition [$[$labels],*] (by rfl))

macro_rules (kind := mapply)
  | `(tactic| mapply) =>
      `(tactic| first
        | exact MPSL.ProofMode.impApply
        | exact MPSL.ProofMode.impApplySwap
        | exact MPSL.ProofMode.wandApply
        | exact MPSL.ProofMode.wandApplySwap)

macro_rules (kind := mapplyNamed)
  | `(tactic| mapply $function:ident $argument:ident) => do
      let functionLabel := Lean.quote function.getId.toString
      let argumentLabel := Lean.quote argument.getId.toString
      `(tactic| first
        | exact MPSL.ProofMode.impApplyNamed $functionLabel $argumentLabel (by rfl) (by rfl)
        | exact MPSL.ProofMode.wandApplyNamed $functionLabel $argumentLabel (by rfl))

macro_rules (kind := mtruth)
  | `(tactic| mtruth) => `(tactic| exact MPSL.ProofMode.truthIntro)

macro_rules (kind := mfalse)
  | `(tactic| mfalse $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| exact MPSL.ProofMode.falsumElim $label (by rfl))

macro_rules (kind := mrefl)
  | `(tactic| mrefl) => `(tactic| exact MPSL.ProofMode.eqRefl)

macro_rules (kind := msymm)
  | `(tactic| msymm $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| exact MPSL.ProofMode.eqSymmNamed $label (by rfl))

macro_rules (kind := mtrans)
  | `(tactic| mtrans $first:ident $second:ident) => do
      let firstLabel := Lean.quote first.getId.toString
      let secondLabel := Lean.quote second.getId.toString
      `(tactic| exact MPSL.ProofMode.eqTransNamed $firstLabel $secondLabel (by rfl) (by rfl))

macro_rules (kind := mexistsDsl)
  | `(tactic| mexists $witness:mpslTerm) =>
      `(tactic| apply MPSL.ProofMode.existsIntro
        (MPSL.Expr.denote mpsl{ $witness } MPSL.Env.nil))

macro_rules (kind := mforall)
  | `(tactic| mforall $name:ident) =>
      `(tactic| apply MPSL.ProofMode.forallIntro; intro $(name):ident)

macro_rules (kind := mopenExists)
  | `(tactic| mopenexists $source:ident as $witness:ident $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name];
        apply MPSL.ProofMode.existsElimAt $sourceLabel $label (by rfl);
        intro $(witness):ident)

macro_rules (kind := mspecializeDsl)
  | `(tactic| mspecialize $source:ident at $witness:mpslTerm as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name];
        apply MPSL.ProofMode.forallElim $sourceLabel $label
        (MPSL.Expr.denote mpsl{ $witness } MPSL.Env.nil) (by rfl))

macro_rules (kind := malways)
  | `(tactic| malways) =>
      `(tactic| first
        | apply MPSL.ProofMode.alwaysIntro
        | apply MPSL.ProofMode.alwaysIntroBoxed (by repeat constructor))

macro_rules (kind := mopenAlways)
  | `(tactic| mopen $source:ident as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name];
        apply MPSL.ProofMode.alwaysElim $sourceLabel $label (by rfl))

macro_rules (kind := mdup)
  | `(tactic| mdup $source:ident as $left:ident $right:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let leftLabel := Lean.quote left.getId.toString
      let rightLabel := Lean.quote right.getId.toString
      `(tactic| _mpsl_guard_replace $source [$left, $right];
        apply MPSL.ProofMode.alwaysDup $sourceLabel $leftLabel $rightLabel (by rfl))

macro_rules (kind := mlater)
  | `(tactic| mlater) => `(tactic| apply MPSL.ProofMode.laterIntro)

macro_rules (kind := mopenLater)
  | `(tactic| mopenlater $source:ident as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name];
        apply MPSL.ProofMode.laterMonoAt $sourceLabel $label (by rfl))

macro_rules (kind := mclear)
  | `(tactic| mclear $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.clear $label (by rfl))

macro_rules (kind := mframe)
  | `(tactic| mframe $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| first
        | apply MPSL.ProofMode.frame $label (by rfl)
        | apply MPSL.ProofMode.frameRight $label (by rfl))

macro_rules (kind := mframeMany)
  | `(tactic| mframe [$names:ident,*]) => do
      let labels : Array (Lean.TSyntax `term) :=
        names.getElems.map fun name => Lean.quote (k := `term) name.getId.toString
      `(tactic| apply MPSL.ProofMode.frameMany [$[$labels],*] (by rfl))

macro_rules (kind := mnormalize)
  | `(tactic| mnormalize) =>
      `(tactic| simp only [MPSL.ProofMode.Valid, MPSL.ProofMode.Bunch.denote,
        MPSL.Formula.denote, MPSL.Expr.denote, MPSL.Var.denote])

macro_rules (kind := mstop)
  | `(tactic| mstop) => `(tactic| unfold MPSL.ProofMode.Valid)
