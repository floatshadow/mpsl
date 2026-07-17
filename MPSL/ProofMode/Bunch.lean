import MPSL.Syntax.Denote

set_option autoImplicit false

namespace MPSL.ProofMode

universe u v

/-- Additive and multiplicative composition of proof-mode hypotheses. -/
inductive Bunch (Loc : Type u) (Val : Type v) : Type (max u v) where
  | empty
  | hyp (name : String) (assertion : Formula Loc Val)
  | additive (left right : Bunch Loc Val)
  | multiplicative (left right : Bunch Loc Val)

namespace Bunch

variable {Loc : Type u} {Val : Type v}

def denote [DecidableEq Loc] : Bunch Loc Val -> IProp Loc Val
  | .empty => IProp.truth
  | .hyp _ assertion => assertion.denote
  | .additive left right => IProp.and left.denote right.denote
  | .multiplicative left right => IProp.sep left.denote right.denote

def lookup (name : String) : Bunch Loc Val -> Option (Formula Loc Val)
  | .empty => none
  | .hyp candidate assertion => if candidate = name then some assertion else none
  | .additive left right
  | .multiplicative left right =>
      match left.lookup name with
      | some assertion => some assertion
      | none => right.lookup name

theorem lookup_sound [DecidableEq Loc] {context : Bunch Loc Val}
    {name : String} {goal : Formula Loc Val} :
    context.lookup name = some goal -> IProp.Entails context.denote goal.denote := by
  intro found
  induction context generalizing goal with
  | empty => simp [lookup] at found
  | hyp candidate assertion =>
      by_cases same : candidate = name
      · simp [lookup, same] at found
        subst goal
        exact IProp.entails_refl assertion.denote
      · simp [lookup, same] at found
  | additive left right leftIH rightIH =>
      cases leftFound : left.lookup name with
      | some leftGoal =>
          have sameGoal : leftGoal = goal := by
            simpa [lookup, leftFound] using found
          subst goal
          exact IProp.entails_trans
            (IProp.and_elim_left left.denote right.denote)
            (leftIH leftFound)
      | none =>
          have rightFound : right.lookup name = some goal := by
            simpa [lookup, leftFound] using found
          exact IProp.entails_trans
            (IProp.and_elim_right left.denote right.denote)
            (rightIH rightFound)
  | multiplicative left right leftIH rightIH =>
      cases leftFound : left.lookup name with
      | some leftGoal =>
          have sameGoal : leftGoal = goal := by
            simpa [lookup, leftFound] using found
          subst goal
          exact IProp.entails_trans
            (IProp.sep_elim_left left.denote right.denote)
            (leftIH leftFound)
      | none =>
          have rightFound : right.lookup name = some goal := by
            simpa [lookup, leftFound] using found
          exact IProp.entails_trans
            (IProp.sep_elim_right left.denote right.denote)
            (rightIH rightFound)

end Bunch

variable {Loc : Type u} {Val : Type v}

/-- Semantic validity of a proof-mode goal. -/
def Valid [DecidableEq Loc] (context : Bunch Loc Val) (goal : Formula Loc Val) : Prop :=
  IProp.Entails context.denote goal.denote

end MPSL.ProofMode
