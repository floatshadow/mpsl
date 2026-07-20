import Lean.Elab.Tactic
import MPSL.Elab
import MPSL.ProofMode.Rules

syntax (name := mexact) "mexact " ident : tactic
syntax (name := mintro) "mintro " ident : tactic
syntax (name := mintroPersistent) "mintro" "#" ident : tactic
syntax (name := mpersistent) "mpersistent " ident : tactic
syntax (name := mdestruct) "mdestruct" ident "as" ident ident : tactic
syntax (name := mdestructPersistentLeft) "mdestruct" ident "as" "#" ident ident : tactic
syntax (name := mdestructPersistentRight) "mdestruct" ident "as" ident "#" ident : tactic
syntax (name := msplit) "msplit" : tactic
syntax (name := mleft) "mleft" : tactic
syntax (name := mright) "mright" : tactic
syntax (name := msep) "msep" : tactic
syntax (name := msepLeft) "msep" "[" ident,* "]" : tactic
syntax (name := msepRight) "msepR" "[" ident,* "]" : tactic
syntax (name := mapplyNamed) "mapply " ident ident : tactic
syntax (name := massumption) "massumption" : tactic
syntax (name := mtruth) "mtruth" : tactic
syntax (name := mfalse) "mfalse " ident : tactic
syntax (name := mrefl) "mrefl" : tactic
syntax (name := msymm) "msymm " ident : tactic
syntax (name := mtrans) "mtrans " ident ident : tactic
syntax (name := mexistsDsl) "mexists " mpslTerm : tactic
syntax (name := mforall) "mforall " ident : tactic
syntax (name := mopenExists) "mopenexists" ident "as" ident ident : tactic
syntax (name := mspecializeDsl) "mspecialize " ident " at " mpslTerm " as " ident : tactic
syntax (name := malways) "malways" : tactic
syntax (name := mopenAlways) "mopen" ident "as" ident : tactic
syntax (name := mlater) "mlater" : tactic
syntax (name := mopenLater) "mopenlater" ident "as" ident : tactic
syntax (name := mclear) "mclear " ident : tactic
syntax (name := mframe) "mframe " ident : tactic
syntax (name := mframeMany) "mframe" "[" ident,+ "]" : tactic
syntax (name := mnormalize) "mnormalize" : tactic
syntax (name := mstop) "mstop" : tactic
syntax (name := mguardFresh) "_mpsl_guard_fresh " ident : tactic
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
  match ← whnf (← instantiateMVars expression) with
  | .lit (.strVal value) => return value
  | _ => throwError "MPSL hypothesis name is not a string literal"

private def hypothesisValue (expression : Lean.Expr) : MetaM NamedAssertion := do
  let expression ← whnf (← instantiateMVars expression)
  unless expression.getAppFn.isConstOf ``MPSL.ProofMode.Hypothesis.mk do
    throwError "malformed MPSL proof-mode hypothesis"
  let arguments := expression.getAppArgs
  return ⟨← stringValue arguments[arguments.size - 2]!, arguments[arguments.size - 1]!⟩

private partial def environmentAssertions (environment : Lean.Expr) :
    MetaM (Array NamedAssertion) := do
  let environment ← whnf (← instantiateMVars environment)
  let function := environment.getAppFn
  let arguments := environment.getAppArgs
  if function.isConstOf ``List.nil then
    return #[]
  else if function.isConstOf ``List.cons then
    let head ← hypothesisValue arguments[arguments.size - 2]!
    let tail ← environmentAssertions arguments[arguments.size - 1]!
    return #[head] ++ tail
  else
    throwError "MPSL proof-mode environment is not reducible to a hypothesis list"

private def assertions (context : Lean.Expr) : MetaM (Array NamedAssertion) := do
  let context ← whnf (← instantiateMVars context)
  unless context.getAppFn.isConstOf ``MPSL.ProofMode.Context.mk do
    throwError "MPSL proof-mode context is not reducible to a flat context"
  let arguments := context.getAppArgs
  let persistent ← environmentAssertions arguments[arguments.size - 2]!
  let spatial ← environmentAssertions arguments[arguments.size - 1]!
  return persistent ++ spatial

private def guardFresh (name : String) : TacticM Unit := withMainContext do
  let (context, _) ← validTarget
  for hypothesis in ← assertions context do
    if hypothesis.name = name then
      throwError "duplicate proof-mode hypothesis name '{name}'"

private def guardFreshOrOuter (name : String) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  if target.getAppFn.isConstOf ``MPSL.ProofMode.Valid then
    guardFresh name

private def guardReplace (removed : String) (newNames : Array String) : TacticM Unit :=
    withMainContext do
  let (context, _) ← validTarget
  let existing ← assertions context
  let mut seen : Array String := #[]
  for hypothesis in existing do
    if hypothesis.name != removed then
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
  | `(tactic| _mpsl_guard_fresh $name:ident) => guardFreshOrOuter name.getId.toString

elab_rules (kind := mguardReplace) : tactic
  | `(tactic| _mpsl_guard_replace $source:ident [$names:ident,*]) =>
      guardReplace source.getId.toString (names.getElems.map (·.getId.toString))

elab_rules (kind := massumption) : tactic
  | `(tactic| massumption) => withMainContext do
      let (context, goal) ← validTarget
      let some candidate ← findMatching (← assertions context) goal
        | throwError "massumption found no definitionally matching hypothesis"
      let label := Lean.quote (k := `term) candidate.name
      evalTactic (← `(tactic|
        exact MPSL.ProofMode.exactNamed $label (by rfl) (by rfl)))

end MPSL.ProofMode.Tactic

macro_rules (kind := mexact)
  | `(tactic| mexact $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| exact MPSL.ProofMode.exactNamed $label (by rfl) (by rfl))

macro_rules (kind := mintro)
  | `(tactic| mintro $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_fresh $name; first
        | apply MPSL.ProofMode.wandIntroSpatial $label
        | apply MPSL.ProofMode.impIntroSpatial $label
        | (apply MPSL.ProofMode.start;
           apply MPSL.ProofMode.wandIntroSpatial $label))

macro_rules (kind := mintroPersistent)
  | `(tactic| mintro #$name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_fresh $name;
        apply MPSL.ProofMode.impIntroPersistent $label)

macro_rules (kind := mpersistent)
  | `(tactic| mpersistent $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.persistent $label (by rfl))

macro_rules (kind := mdestruct)
  | `(tactic| mdestruct $source:ident as $firstName:ident $secondName:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let leftLabel := Lean.quote firstName.getId.toString
      let rightLabel := Lean.quote secondName.getId.toString
      `(tactic| _mpsl_guard_replace $source [$firstName, $secondName]; first
        | apply MPSL.ProofMode.sepDestructSpatial
            $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.sepDestructPersistent
            $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.andDestructPersistent
            $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.orDestructSpatial
            $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.orDestructPersistent
            $sourceLabel $leftLabel $rightLabel (by rfl))

macro_rules (kind := mdestructPersistentLeft)
  | `(tactic| mdestruct $source:ident as #$persistentName:ident $spatialName:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let persistentLabel := Lean.quote persistentName.getId.toString
      let spatialLabel := Lean.quote spatialName.getId.toString
      `(tactic| _mpsl_guard_replace $source [$persistentName, $spatialName];
        apply MPSL.ProofMode.andDestructSpatialPersistentLeft
          $sourceLabel $persistentLabel $spatialLabel (by rfl))

macro_rules (kind := mdestructPersistentRight)
  | `(tactic| mdestruct $source:ident as $spatialName:ident #$persistentName:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let spatialLabel := Lean.quote spatialName.getId.toString
      let persistentLabel := Lean.quote persistentName.getId.toString
      `(tactic| _mpsl_guard_replace $source [$spatialName, $persistentName];
        apply MPSL.ProofMode.andDestructSpatialPersistentRight
          $sourceLabel $spatialLabel $persistentLabel (by rfl))

macro_rules (kind := msplit)
  | `(tactic| msplit) => `(tactic| apply MPSL.ProofMode.andIntro)

macro_rules (kind := mleft)
  | `(tactic| mleft) => `(tactic| apply MPSL.ProofMode.orIntroLeft)

macro_rules (kind := mright)
  | `(tactic| mright) => `(tactic| apply MPSL.ProofMode.orIntroRight)

macro_rules (kind := msep)
  | `(tactic| msep) => `(tactic| first
      | apply MPSL.ProofMode.sepIntroPersistentLeft
      | apply MPSL.ProofMode.sepIntroPersistentRight)

macro_rules (kind := msepLeft)
  | `(tactic| msep [$names:ident,*]) => do
      let labels : Array (Lean.TSyntax `term) :=
        names.getElems.map fun name => Lean.quote (k := `term) name.getId.toString
      `(tactic| apply MPSL.ProofMode.sepIntroLeft [$[$labels],*] (by rfl))

macro_rules (kind := msepRight)
  | `(tactic| msepR [$names:ident,*]) => do
      let labels : Array (Lean.TSyntax `term) :=
        names.getElems.map fun name => Lean.quote (k := `term) name.getId.toString
      `(tactic| apply MPSL.ProofMode.sepIntroRight [$[$labels],*] (by rfl))

macro_rules (kind := mapplyNamed)
  | `(tactic| mapply $function:ident $argument:ident) => do
      let functionLabel := Lean.quote function.getId.toString
      let argumentLabel := Lean.quote argument.getId.toString
      `(tactic| first
        | exact MPSL.ProofMode.impApplyNamed $functionLabel $argumentLabel (by rfl) (by rfl)
        | exact MPSL.ProofMode.wandApplyNamed $functionLabel $argumentLabel (by rfl) (by rfl))

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
      `(tactic| _mpsl_guard_replace $source [$name]; first
        | (apply MPSL.ProofMode.existsDestructSpatial
            $sourceLabel $label (by rfl); intro $(witness):ident)
        | (apply MPSL.ProofMode.existsDestructPersistent
            $sourceLabel $label (by rfl); intro $(witness):ident))

macro_rules (kind := mspecializeDsl)
  | `(tactic| mspecialize $source:ident at $witness:mpslTerm as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name]; first
        | apply MPSL.ProofMode.forallElimPersistent $sourceLabel $label
            (MPSL.Expr.denote mpsl{ $witness } MPSL.Env.nil) (by rfl)
        | apply MPSL.ProofMode.forallElimSpatial $sourceLabel $label
            (MPSL.Expr.denote mpsl{ $witness } MPSL.Env.nil) (by rfl))

macro_rules (kind := malways)
  | `(tactic| malways) => `(tactic| apply MPSL.ProofMode.alwaysIntro)

macro_rules (kind := mopenAlways)
  | `(tactic| mopen $source:ident as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name];
        apply MPSL.ProofMode.alwaysElimPersistent $sourceLabel $label (by rfl))

macro_rules (kind := mlater)
  | `(tactic| mlater) => `(tactic| apply MPSL.ProofMode.laterIntro)

macro_rules (kind := mopenLater)
  | `(tactic| mopenlater $source:ident as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| _mpsl_guard_replace $source [$name];
        apply MPSL.ProofMode.laterMonoSpatial $sourceLabel $label (by rfl))

macro_rules (kind := mclear)
  | `(tactic| mclear $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| first
        | apply MPSL.ProofMode.clearPersistent $label (by rfl)
        | apply MPSL.ProofMode.clearSpatial $label (by rfl))

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
      `(tactic| simp only [MPSL.ProofMode.Valid, MPSL.ProofMode.Context.denote,
        MPSL.ProofMode.Environment.andDenote, MPSL.ProofMode.Environment.sepDenote,
        MPSL.Formula.denote, MPSL.Expr.denote, MPSL.Var.denote])

macro_rules (kind := mstop)
  | `(tactic| mstop) => `(tactic| unfold MPSL.ProofMode.Valid)
