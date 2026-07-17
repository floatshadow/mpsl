import Lean.Elab.Tactic
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
        | apply MPSL.ProofMode.andDestruct $sourceLabel $leftLabel $rightLabel
        | apply MPSL.ProofMode.sepDestruct $sourceLabel $leftLabel $rightLabel
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
