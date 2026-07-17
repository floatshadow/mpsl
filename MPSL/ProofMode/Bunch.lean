import MPSL.Syntax.Denote

set_option autoImplicit false

namespace MPSL.ProofMode

universe u v

/-- Additive and multiplicative composition of proof-mode hypotheses. -/
inductive Bunch (Loc : Type u) (Val : Type v) : Type (max u v) where
  | empty
  | hyp (name : String) (assertion : IProp Loc Val)
  | additive (left right : Bunch Loc Val)
  | multiplicative (left right : Bunch Loc Val)

namespace Bunch

variable {Loc : Type u} {Val : Type v}

def denote : Bunch Loc Val -> IProp Loc Val
  | .empty => IProp.truth
  | .hyp _ assertion => assertion
  | .additive left right => IProp.and left.denote right.denote
  | .multiplicative left right => IProp.sep left.denote right.denote

def lookup (name : String) : Bunch Loc Val -> Option (IProp Loc Val)
  | .empty => none
  | .hyp candidate assertion => if candidate = name then some assertion else none
  | .additive left right
  | .multiplicative left right =>
      match left.lookup name with
      | some assertion => some assertion
      | none => right.lookup name

/-- Replace the first named hypothesis and return its previous assertion. -/
def replace (name : String) (replacement : Bunch Loc Val) :
    Bunch Loc Val -> Option (IProp Loc Val × Bunch Loc Val)
  | .empty => none
  | .hyp candidate assertion =>
      if candidate = name then some (assertion, replacement) else none
  | .additive left right =>
      match replace name replacement left with
      | some (assertion, updated) => some (assertion, .additive updated right)
      | none =>
          match replace name replacement right with
          | some (assertion, updated) => some (assertion, .additive left updated)
          | none => none
  | .multiplicative left right =>
      match replace name replacement left with
      | some (assertion, updated) => some (assertion, .multiplicative updated right)
      | none =>
          match replace name replacement right with
          | some (assertion, updated) => some (assertion, .multiplicative left updated)
          | none => none

/-- Extract a hypothesis reachable only through multiplicative nodes. -/
def extract (name : String) : Bunch Loc Val -> Option (IProp Loc Val × Bunch Loc Val)
  | .empty => none
  | .hyp candidate assertion =>
      if candidate = name then some (assertion, .empty) else none
  | .additive _ _ => none
  | .multiplicative left right =>
      match extract name left with
      | some (assertion, updated) => some (assertion, .multiplicative updated right)
      | none =>
          match extract name right with
          | some (assertion, updated) => some (assertion, .multiplicative left updated)
          | none => none

/-- Extract a nonempty ordered list of hypotheses through multiplicative nodes. -/
def extractMany : List String -> Bunch Loc Val -> Option (IProp Loc Val × Bunch Loc Val)
  | [], _ => none
  | [name], context => extract name context
  | name :: next :: rest, context => do
      let (assertion, afterFirst) ← extract name context
      let (remainingAssertions, remaining) ← extractMany (next :: rest) afterFirst
      pure (IProp.sep assertion remainingAssertions, remaining)

theorem lookup_sound {context : Bunch Loc Val}
    {name : String} {goal : IProp Loc Val} :
    context.lookup name = some goal -> IProp.Entails context.denote goal := by
  intro found
  induction context generalizing goal with
  | empty => simp [lookup] at found
  | hyp candidate assertion =>
      by_cases same : candidate = name
      · simp [lookup, same] at found
        subst goal
        exact IProp.entails_refl assertion
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

theorem replace_sound {context replacement updated : Bunch Loc Val}
    {name : String} {source : IProp Loc Val} :
    replace name replacement context = some (source, updated) ->
    IProp.Entails source replacement.denote ->
    IProp.Entails context.denote updated.denote := by
  intro replaced sourceRule
  induction context generalizing source updated with
  | empty => simp [replace] at replaced
  | hyp candidate assertion =>
      by_cases same : candidate = name
      · simp [replace, same] at replaced
        obtain ⟨rfl, rfl⟩ := replaced
        exact sourceRule
      · simp [replace, same] at replaced
  | additive left right leftIH rightIH =>
      cases leftReplaced : replace name replacement left with
      | some result =>
          obtain ⟨leftSource, leftUpdated⟩ := result
          have resultEqual : (leftSource, .additive leftUpdated right) = (source, updated) := by
            simpa [replace, leftReplaced] using replaced
          cases resultEqual
          exact IProp.and_mono (leftIH leftReplaced sourceRule)
            (IProp.entails_refl right.denote)
      | none =>
          cases rightReplaced : replace name replacement right with
          | none => simp [replace, leftReplaced, rightReplaced] at replaced
          | some result =>
              obtain ⟨rightSource, rightUpdated⟩ := result
              have resultEqual : (rightSource, .additive left rightUpdated) = (source, updated) := by
                simpa [replace, leftReplaced, rightReplaced] using replaced
              cases resultEqual
              exact IProp.and_mono (IProp.entails_refl left.denote)
                (rightIH rightReplaced sourceRule)
  | multiplicative left right leftIH rightIH =>
      cases leftReplaced : replace name replacement left with
      | some result =>
          obtain ⟨leftSource, leftUpdated⟩ := result
          have resultEqual : (leftSource, .multiplicative leftUpdated right) = (source, updated) := by
            simpa [replace, leftReplaced] using replaced
          cases resultEqual
          exact IProp.sep_mono (leftIH leftReplaced sourceRule)
            (IProp.entails_refl right.denote)
      | none =>
          cases rightReplaced : replace name replacement right with
          | none => simp [replace, leftReplaced, rightReplaced] at replaced
          | some result =>
              obtain ⟨rightSource, rightUpdated⟩ := result
              have resultEqual : (rightSource, .multiplicative left rightUpdated) = (source, updated) := by
                simpa [replace, leftReplaced, rightReplaced] using replaced
              cases resultEqual
              exact IProp.sep_mono (IProp.entails_refl left.denote)
                (rightIH rightReplaced sourceRule)

theorem extract_sound {context remaining : Bunch Loc Val}
    {name : String} {frame : IProp Loc Val} :
    extract name context = some (frame, remaining) ->
    IProp.Entails context.denote (IProp.sep frame remaining.denote) := by
  intro extracted
  induction context generalizing frame remaining with
  | empty => simp [extract] at extracted
  | hyp candidate assertion =>
      by_cases same : candidate = name
      · simp [extract, same] at extracted
        obtain ⟨rfl, rfl⟩ := extracted
        exact IProp.sep_truth_intro_right assertion
      · simp [extract, same] at extracted
  | additive left right leftIH rightIH => simp [extract] at extracted
  | multiplicative left right leftIH rightIH =>
      cases leftExtracted : extract name left with
      | some result =>
          obtain ⟨leftFrame, leftRemaining⟩ := result
          have resultEqual :
              (leftFrame, .multiplicative leftRemaining right) = (frame, remaining) := by
            simpa [extract, leftExtracted] using extracted
          cases resultEqual
          exact IProp.entails_trans
            (IProp.sep_mono (leftIH leftExtracted) (IProp.entails_refl right.denote))
            (IProp.sep_assoc_left frame leftRemaining.denote right.denote)
      | none =>
          cases rightExtracted : extract name right with
          | none => simp [extract, leftExtracted, rightExtracted] at extracted
          | some result =>
              obtain ⟨rightFrame, rightRemaining⟩ := result
              have resultEqual :
                  (rightFrame, .multiplicative left rightRemaining) = (frame, remaining) := by
                simpa [extract, leftExtracted, rightExtracted] using extracted
              cases resultEqual
              apply IProp.entails_trans
                (IProp.sep_mono (IProp.entails_refl left.denote) (rightIH rightExtracted))
              apply IProp.entails_trans
                (IProp.sep_assoc_right left.denote frame rightRemaining.denote)
              apply IProp.entails_trans
                (IProp.sep_mono (IProp.sep_comm left.denote frame)
                  (IProp.entails_refl rightRemaining.denote))
              exact IProp.sep_assoc_left frame left.denote rightRemaining.denote

theorem extractMany_sound {names : List String} {context remaining : Bunch Loc Val}
    {frame : IProp Loc Val} :
    extractMany names context = some (frame, remaining) ->
    IProp.Entails context.denote (IProp.sep frame remaining.denote) := by
  induction names generalizing context frame remaining with
  | nil => simp [extractMany]
  | cons name names induction =>
      cases names with
      | nil =>
          simpa [extractMany] using
            (extract_sound (context := context) (remaining := remaining)
              (name := name) (frame := frame))
      | cons next rest =>
          intro extracted
          simp only [extractMany] at extracted
          cases firstExtracted : extract name context with
          | none => simp [firstExtracted] at extracted
          | some firstResult =>
              obtain ⟨assertion, afterFirst⟩ := firstResult
              cases restExtracted : extractMany (next :: rest) afterFirst with
              | none => simp [firstExtracted, restExtracted] at extracted
              | some restResult =>
                  obtain ⟨remainingAssertions, finalContext⟩ := restResult
                  simp [firstExtracted, restExtracted] at extracted
                  obtain ⟨rfl, rfl⟩ := extracted
                  apply IProp.entails_trans (extract_sound firstExtracted)
                  apply IProp.entails_trans
                    (IProp.sep_mono (IProp.entails_refl assertion)
                      (induction restExtracted))
                  exact IProp.sep_assoc_right assertion remainingAssertions finalContext.denote

end Bunch

variable {Loc : Type u} {Val : Type v}

/-- Semantic validity of a proof-mode goal. -/
def Valid (context : Bunch Loc Val) (goal : IProp Loc Val) : Prop :=
  IProp.Entails context.denote goal

end MPSL.ProofMode
