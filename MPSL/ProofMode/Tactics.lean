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
syntax (name := mapply) "mapply" : tactic
syntax (name := mtruth) "mtruth" : tactic
syntax (name := mfalse) "mfalse " ident : tactic
syntax (name := mrefl) "mrefl" : tactic
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
      `(tactic| first
        | apply MPSL.ProofMode.impIntro $label
        | apply MPSL.ProofMode.wandIntro $label)

macro_rules (kind := mdestruct)
  | `(tactic| mdestruct $source:ident as $left:ident $right:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let leftLabel := Lean.quote left.getId.toString
      let rightLabel := Lean.quote right.getId.toString
      `(tactic| first
        | apply MPSL.ProofMode.andDestruct $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.sepDestruct $sourceLabel $leftLabel $rightLabel (by rfl)
        | apply MPSL.ProofMode.orDestruct $sourceLabel $leftLabel $rightLabel)

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

macro_rules (kind := mapply)
  | `(tactic| mapply) =>
      `(tactic| first
        | exact MPSL.ProofMode.impApply
        | exact MPSL.ProofMode.impApplySwap
        | exact MPSL.ProofMode.wandApply
        | exact MPSL.ProofMode.wandApplySwap)

macro_rules (kind := mtruth)
  | `(tactic| mtruth) => `(tactic| exact MPSL.ProofMode.truthIntro)

macro_rules (kind := mfalse)
  | `(tactic| mfalse $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| exact MPSL.ProofMode.falsumElim $label (by rfl))

macro_rules (kind := mrefl)
  | `(tactic| mrefl) => `(tactic| exact MPSL.ProofMode.eqRefl)

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
      `(tactic| apply MPSL.ProofMode.existsElim $sourceLabel $label; intro $(witness):ident)

macro_rules (kind := mspecializeDsl)
  | `(tactic| mspecialize $source:ident at $witness:mpslTerm as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.forallElim $sourceLabel $label
        (MPSL.Expr.denote mpsl{ $witness } MPSL.Env.nil) (by rfl))

macro_rules (kind := malways)
  | `(tactic| malways) => `(tactic| apply MPSL.ProofMode.alwaysIntro)

macro_rules (kind := mopenAlways)
  | `(tactic| mopen $source:ident as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.alwaysElim $sourceLabel $label (by rfl))

macro_rules (kind := mdup)
  | `(tactic| mdup $source:ident as $left:ident $right:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let leftLabel := Lean.quote left.getId.toString
      let rightLabel := Lean.quote right.getId.toString
      `(tactic| apply MPSL.ProofMode.alwaysDup $sourceLabel $leftLabel $rightLabel (by rfl))

macro_rules (kind := mlater)
  | `(tactic| mlater) => `(tactic| apply MPSL.ProofMode.laterIntro)

macro_rules (kind := mopenLater)
  | `(tactic| mopenlater $source:ident as $name:ident) => do
      let sourceLabel := Lean.quote source.getId.toString
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.laterMono $sourceLabel $label)

macro_rules (kind := mclear)
  | `(tactic| mclear $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.clear $label (by rfl))

macro_rules (kind := mframe)
  | `(tactic| mframe $name:ident) => do
      let label := Lean.quote name.getId.toString
      `(tactic| apply MPSL.ProofMode.frame $label (by rfl))

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
