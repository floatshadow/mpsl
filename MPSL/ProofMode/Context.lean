import MPSL.Syntax.Denote

set_option autoImplicit false

namespace MPSL.ProofMode

universe u v

/-- A named object-logic assertion in a proof-mode environment. -/
structure Hypothesis (Loc : Type u) (Val : Type v) where
  name : String
  assertion : IProp Loc Val

abbrev Environment (Loc : Type u) (Val : Type v) := List (Hypothesis Loc Val)

namespace Environment

variable {Loc : Type u} {Val : Type v}

def names (environment : Environment Loc Val) : List String :=
  environment.map (·.name)

def lookup (name : String) : Environment Loc Val -> Option (IProp Loc Val)
  | [] => none
  | hypothesis :: rest =>
      if hypothesis.name = name then some hypothesis.assertion else lookup name rest

def erase (name : String) :
    Environment Loc Val -> Option (IProp Loc Val × Environment Loc Val)
  | [] => none
  | hypothesis :: rest =>
      if hypothesis.name = name then some (hypothesis.assertion, rest)
      else do
        let (assertion, remaining) ← erase name rest
        pure (assertion, hypothesis :: remaining)

def replace (name : String) (replacement : Environment Loc Val) :
    Environment Loc Val -> Option (IProp Loc Val × Environment Loc Val)
  | [] => none
  | hypothesis :: rest =>
      if hypothesis.name = name then some (hypothesis.assertion, replacement ++ rest)
      else do
        let (assertion, updated) ← replace name replacement rest
        pure (assertion, hypothesis :: updated)

/-- Decompose an environment around its first hypothesis with the given name. -/
def focus (name : String) : Environment Loc Val ->
    Option (Environment Loc Val × IProp Loc Val × Environment Loc Val)
  | [] => none
  | hypothesis :: rest =>
      if hypothesis.name = name then some ([], hypothesis.assertion, rest)
      else do
        let (front, assertion, suffix) ← focus name rest
        pure (hypothesis :: front, assertion, suffix)

def partition : List String -> Environment Loc Val ->
    Option (Environment Loc Val × Environment Loc Val)
  | [], environment => some ([], environment)
  | name :: names, environment => do
      let (assertion, afterFirst) ← erase name environment
      let (selected, remaining) ← partition names afterFirst
      pure (⟨name, assertion⟩ :: selected, remaining)

def andDenote : Environment Loc Val -> IProp Loc Val
  | [] => IProp.truth
  | hypothesis :: rest => IProp.and hypothesis.assertion (andDenote rest)

def sepDenote : Environment Loc Val -> IProp Loc Val
  | [] => IProp.truth
  | hypothesis :: rest => IProp.sep hypothesis.assertion (sepDenote rest)

theorem and_lookup_sound {environment : Environment Loc Val}
    {name : String} {assertion : IProp Loc Val} :
    lookup name environment = some assertion ->
    IProp.Entails environment.andDenote assertion := by
  intro found
  induction environment with
  | nil => simp [lookup] at found
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [lookup, same] at found
        subst assertion
        exact IProp.and_elim_left _ _
      · simp [lookup, same] at found
        exact IProp.entails_trans (IProp.and_elim_right _ _) (induction found)

theorem sep_lookup_sound {environment : Environment Loc Val}
    {name : String} {assertion : IProp Loc Val} :
    lookup name environment = some assertion ->
    IProp.Entails environment.sepDenote assertion := by
  intro found
  induction environment with
  | nil => simp [lookup] at found
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [lookup, same] at found
        subst assertion
        exact IProp.sep_elim_left _ _
      · simp [lookup, same] at found
        exact IProp.entails_trans (IProp.sep_elim_right _ _) (induction found)

theorem and_append_intro (front suffix : Environment Loc Val) :
    IProp.Entails (IProp.and front.andDenote suffix.andDenote)
      (front ++ suffix).andDenote := by
  induction front with
  | nil => exact IProp.and_elim_right _ _
  | cons hypothesis rest induction =>
      intro heap step holds
      exact ⟨holds.1.1, induction heap step ⟨holds.1.2, holds.2⟩⟩

theorem sep_append_intro (front suffix : Environment Loc Val) :
    IProp.Entails (IProp.sep front.sepDenote suffix.sepDenote)
      (front ++ suffix).sepDenote := by
  induction front with
  | nil => exact IProp.sep_truth_left _
  | cons hypothesis rest induction =>
      exact IProp.entails_trans
        (IProp.sep_assoc_left hypothesis.assertion (sepDenote rest) suffix.sepDenote)
        (IProp.sep_mono (IProp.entails_refl _) induction)

theorem and_replace_sound {environment replacement updated : Environment Loc Val}
    {name : String} {old : IProp Loc Val}
    (replaced : replace name replacement environment = some (old, updated))
    (replacementSound : IProp.Entails old replacement.andDenote) :
    IProp.Entails environment.andDenote updated.andDenote := by
  induction environment generalizing old updated with
  | nil => simp [replace] at replaced
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [replace, same] at replaced
        obtain ⟨rfl, rfl⟩ := replaced
        exact IProp.entails_trans
          (IProp.and_mono replacementSound (IProp.entails_refl _))
          (and_append_intro replacement rest)
      · simp [replace, same] at replaced
        cases recursive : replace name replacement rest with
        | none => simp [recursive] at replaced
        | some result =>
            obtain ⟨found, changed⟩ := result
            simp [recursive] at replaced
            obtain ⟨rfl, rfl⟩ := replaced
            exact IProp.and_mono (IProp.entails_refl _)
              (induction recursive replacementSound)

theorem sep_replace_sound {environment replacement updated : Environment Loc Val}
    {name : String} {old : IProp Loc Val}
    (replaced : replace name replacement environment = some (old, updated))
    (replacementSound : IProp.Entails old replacement.sepDenote) :
    IProp.Entails environment.sepDenote updated.sepDenote := by
  induction environment generalizing old updated with
  | nil => simp [replace] at replaced
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [replace, same] at replaced
        obtain ⟨rfl, rfl⟩ := replaced
        exact IProp.entails_trans
          (IProp.sep_mono replacementSound (IProp.entails_refl _))
          (sep_append_intro replacement rest)
      · simp [replace, same] at replaced
        cases recursive : replace name replacement rest with
        | none => simp [recursive] at replaced
        | some result =>
            obtain ⟨found, changed⟩ := result
            simp [recursive] at replaced
            obtain ⟨rfl, rfl⟩ := replaced
            exact IProp.sep_mono (IProp.entails_refl _)
              (induction recursive replacementSound)

theorem and_focus_sound {environment front suffix : Environment Loc Val}
    {name : String} {assertion : IProp Loc Val}
    (focused : focus name environment = some (front, assertion, suffix)) :
    IProp.Entails environment.andDenote
      (IProp.and front.andDenote (IProp.and assertion suffix.andDenote)) := by
  induction environment generalizing front assertion suffix with
  | nil => simp [focus] at focused
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [focus, same] at focused
        obtain ⟨rfl, rfl, rfl⟩ := focused
        intro heap step holds
        exact ⟨True.intro, holds⟩
      · simp [focus, same] at focused
        cases recursive : focus name rest with
        | none => simp [recursive] at focused
        | some result =>
            obtain ⟨restPrefix, found, restSuffix⟩ := result
            simp [recursive] at focused
            obtain ⟨rfl, rfl, rfl⟩ := focused
            intro heap step holds
            have restFocused := induction recursive heap step holds.2
            exact ⟨⟨holds.1, restFocused.1⟩, restFocused.2⟩

theorem sep_focus_sound {environment front suffix : Environment Loc Val}
    {name : String} {assertion : IProp Loc Val}
    (focused : focus name environment = some (front, assertion, suffix)) :
    IProp.Entails environment.sepDenote
      (IProp.sep front.sepDenote (IProp.sep assertion suffix.sepDenote)) := by
  induction environment generalizing front assertion suffix with
  | nil => simp [focus] at focused
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [focus, same] at focused
        obtain ⟨rfl, rfl, rfl⟩ := focused
        exact IProp.sep_truth_intro_left _
      · simp [focus, same] at focused
        cases recursive : focus name rest with
        | none => simp [recursive] at focused
        | some result =>
            obtain ⟨restPrefix, found, restSuffix⟩ := result
            simp [recursive] at focused
            obtain ⟨rfl, rfl, rfl⟩ := focused
            exact IProp.entails_trans
              (IProp.sep_mono (IProp.entails_refl _) (induction recursive))
              (IProp.sep_assoc_right _ _ _)

theorem and_focus_replace_intro (front suffix : Environment Loc Val)
    (hypothesis : Hypothesis Loc Val) :
    IProp.Entails
      (IProp.and front.andDenote
        (IProp.and hypothesis.assertion suffix.andDenote))
      (front ++ hypothesis :: suffix).andDenote := by
  simpa [Environment.andDenote, List.append_assoc] using
    (and_append_intro front (hypothesis :: suffix))

theorem sep_focus_replace_intro (front suffix : Environment Loc Val)
    (hypothesis : Hypothesis Loc Val) :
    IProp.Entails
      (IProp.sep front.sepDenote
        (IProp.sep hypothesis.assertion suffix.sepDenote))
      (front ++ hypothesis :: suffix).sepDenote := by
  simpa [Environment.sepDenote, List.append_assoc] using
    (sep_append_intro front (hypothesis :: suffix))

theorem later_focus_replace_sound {environment front suffix : Environment Loc Val}
    {source name : String} {assertion : IProp Loc Val}
    (focused : focus source environment =
      some (front, IProp.later assertion, suffix)) :
    IProp.Entails environment.sepDenote
      (IProp.later (front ++ ⟨name, assertion⟩ :: suffix).sepDenote) := by
  apply IProp.entails_trans (sep_focus_sound focused)
  apply IProp.entails_trans
    (IProp.sep_mono (IProp.later_intro front.sepDenote)
      (IProp.sep_mono (IProp.entails_refl _)
        (IProp.later_intro suffix.sepDenote)))
  apply IProp.entails_trans
    (IProp.sep_mono (IProp.entails_refl _)
      (IProp.later_sep_intro assertion suffix.sepDenote))
  apply IProp.entails_trans
    (IProp.later_sep_intro front.sepDenote
      (IProp.sep assertion suffix.sepDenote))
  exact IProp.later_mono (sep_focus_replace_intro front suffix ⟨name, assertion⟩)

theorem sep_erase_sound {environment remaining : Environment Loc Val}
    {name : String} {assertion : IProp Loc Val}
    (erased : erase name environment = some (assertion, remaining)) :
    IProp.Entails environment.sepDenote
      (IProp.sep assertion remaining.sepDenote) := by
  induction environment generalizing assertion remaining with
  | nil => simp [erase] at erased
  | cons hypothesis rest induction =>
      by_cases same : hypothesis.name = name
      · simp [erase, same] at erased
        obtain ⟨rfl, rfl⟩ := erased
        exact IProp.entails_refl _
      · simp [erase, same] at erased
        cases recursive : erase name rest with
        | none => simp [recursive] at erased
        | some result =>
            obtain ⟨found, changed⟩ := result
            simp [recursive] at erased
            obtain ⟨rfl, rfl⟩ := erased
            apply IProp.entails_trans
              (IProp.sep_mono (IProp.entails_refl _) (induction recursive))
            apply IProp.entails_trans (IProp.sep_comm _ _)
            apply IProp.entails_trans (IProp.sep_assoc_left _ _ _)
            exact IProp.sep_mono (IProp.entails_refl _) (IProp.sep_comm _ _)

theorem partition_sound {names : List String} {environment selected remaining : Environment Loc Val}
    (partitioned : partition names environment = some (selected, remaining)) :
    IProp.Entails environment.sepDenote
      (IProp.sep selected.sepDenote remaining.sepDenote) := by
  induction names generalizing environment selected remaining with
  | nil =>
      simp [partition] at partitioned
      obtain ⟨rfl, rfl⟩ := partitioned
      exact IProp.sep_truth_intro_left _
  | cons name names induction =>
      simp only [partition] at partitioned
      cases erased : erase name environment with
      | none => simp [erased] at partitioned
      | some erasedResult =>
          obtain ⟨assertion, afterFirst⟩ := erasedResult
          cases restPartitioned : partition names afterFirst with
          | none => simp [erased, restPartitioned] at partitioned
          | some partitionResult =>
              obtain ⟨selectedRest, finalRemaining⟩ := partitionResult
              simp [erased, restPartitioned] at partitioned
              obtain ⟨rfl, rfl⟩ := partitioned
              exact IProp.entails_trans (sep_erase_sound erased)
                (IProp.entails_trans
                  (IProp.sep_mono (IProp.entails_refl _)
                    (induction restPartitioned))
                  (IProp.sep_assoc_right _ _ _))

end Environment

inductive Zone where
  | persistent
  | spatial
  deriving DecidableEq, Repr

/-- Iris-style object-logic context with reusable and resource-owning zones.

Lean local variables and `Prop` hypotheses form the pure context. They are
deliberately not stored here and have no contribution to `denote`.
-/
structure Context (Loc : Type u) (Val : Type v) where
  persistent : Environment Loc Val
  spatial : Environment Loc Val

namespace Context

variable {Loc : Type u} {Val : Type v}

def empty : Context Loc Val := ⟨[], []⟩

def names (context : Context Loc Val) : List String :=
  context.persistent.names ++ context.spatial.names

def lookup (name : String) (context : Context Loc Val) :
    Option (Zone × IProp Loc Val) :=
  match context.persistent.lookup name with
  | some assertion => some (.persistent, assertion)
  | none => context.spatial.lookup name |>.map (fun assertion => (.spatial, assertion))

def snoc (zone : Zone) (name : String) (assertion : IProp Loc Val)
    (context : Context Loc Val) : Context Loc Val :=
  match zone with
  | .persistent => { context with persistent := ⟨name, assertion⟩ :: context.persistent }
  | .spatial => { context with spatial := ⟨name, assertion⟩ :: context.spatial }

def replace (name : String) (replacement : Environment Loc Val)
    (context : Context Loc Val) : Option (Zone × IProp Loc Val × Context Loc Val) :=
  match Environment.replace name replacement context.persistent with
  | some (assertion, updated) =>
      some (.persistent, assertion, { context with persistent := updated })
  | none => do
      let (assertion, updated) ← Environment.replace name replacement context.spatial
      pure (.spatial, assertion, { context with spatial := updated })

def extract (name : String) (context : Context Loc Val) :
    Option (Zone × IProp Loc Val × Context Loc Val) :=
  match context.persistent.lookup name with
  | some assertion => some (.persistent, assertion, context)
  | none => do
      let (assertion, remaining) ← context.spatial.erase name
      pure (.spatial, assertion, { context with spatial := remaining })

def extractMany : List String -> Context Loc Val -> Option (IProp Loc Val × Context Loc Val)
  | [], _ => none
  | [name], context => do
      let (_, assertion, remaining) ← context.extract name
      pure (assertion, remaining)
  | name :: next :: rest, context => do
      let (_, assertion, afterFirst) ← context.extract name
      let (selected, remaining) ← extractMany (next :: rest) afterFirst
      pure (IProp.sep assertion selected, remaining)

def moveToPersistent (name : String) (context : Context Loc Val) :
    Option (IProp Loc Val × Context Loc Val) := do
  let (assertion, remaining) ← context.spatial.erase name
  pure (assertion,
    { persistent := ⟨name, assertion⟩ :: context.persistent, spatial := remaining })

def partition (names : List String) (context : Context Loc Val) :
    Option (Context Loc Val × Context Loc Val) := do
  let (selected, remaining) ← context.spatial.partition names
  pure (⟨context.persistent, selected⟩, ⟨context.persistent, remaining⟩)

def denote (context : Context Loc Val) : IProp Loc Val :=
  IProp.sep (IProp.always context.persistent.andDenote) context.spatial.sepDenote

theorem lookup_sound {context : Context Loc Val} {name : String}
    {zone : Zone} {assertion : IProp Loc Val}
    (found : lookup name context = some (zone, assertion)) :
    IProp.Entails context.denote assertion := by
  unfold lookup at found
  cases persistentFound : context.persistent.lookup name with
  | some persistentAssertion =>
      simp [persistentFound] at found
      obtain ⟨rfl, rfl⟩ := found
      exact IProp.entails_trans (IProp.sep_elim_left _ _)
        (IProp.entails_trans (IProp.always_elim _)
          (Environment.and_lookup_sound persistentFound))
  | none =>
      simp [persistentFound] at found
      cases spatialFound : context.spatial.lookup name with
      | none => simp [spatialFound] at found
      | some spatialAssertion =>
          simp [spatialFound] at found
          obtain ⟨rfl, rfl⟩ := found
          exact IProp.entails_trans (IProp.sep_elim_right _ _)
            (Environment.sep_lookup_sound spatialFound)

theorem replacePersistent_sound {context updated : Context Loc Val}
    {name : String} {old : IProp Loc Val}
    {replacement : Environment Loc Val}
    (replaced : replace name replacement context = some (.persistent, old, updated))
    (replacementSound : IProp.Entails old replacement.andDenote) :
    IProp.Entails context.denote updated.denote := by
  unfold replace at replaced
  cases persistentChanged : Environment.replace name replacement context.persistent with
  | some result =>
      obtain ⟨assertion, changed⟩ := result
      simp [persistentChanged] at replaced
      obtain ⟨rfl, rfl, rfl⟩ := replaced
      have changedSound : IProp.Entails context.persistent.andDenote changed.andDenote :=
        Environment.and_replace_sound (name := name) persistentChanged replacementSound
      simpa [Context.denote] using
        (IProp.sep_mono (IProp.always_mono changedSound) (IProp.entails_refl _))
  | none =>
      simp [persistentChanged] at replaced
      cases spatialChanged : Environment.replace name replacement context.spatial with
      | none => simp [spatialChanged] at replaced
      | some result =>
          obtain ⟨assertion, changed⟩ := result
          simp [spatialChanged] at replaced

theorem replaceSpatial_sound {context updated : Context Loc Val}
    {name : String} {old : IProp Loc Val}
    {replacement : Environment Loc Val}
    (replaced : replace name replacement context = some (.spatial, old, updated))
    (replacementSound : IProp.Entails old replacement.sepDenote) :
    IProp.Entails context.denote updated.denote := by
  unfold replace at replaced
  cases persistentChanged : Environment.replace name replacement context.persistent with
  | some result =>
      obtain ⟨assertion, changed⟩ := result
      simp [persistentChanged] at replaced
  | none =>
      simp [persistentChanged] at replaced
      cases spatialChanged : Environment.replace name replacement context.spatial with
      | none => simp [spatialChanged] at replaced
      | some result =>
          obtain ⟨assertion, changed⟩ := result
          simp [spatialChanged] at replaced
          obtain ⟨rfl, rfl⟩ := replaced
          have changedSound : IProp.Entails context.spatial.sepDenote changed.sepDenote :=
            Environment.sep_replace_sound (name := name) spatialChanged replacementSound
          simpa [Context.denote] using
            (IProp.sep_mono (IProp.entails_refl _) changedSound)

private theorem interleave (persistent selected remaining : IProp Loc Val) :
    IProp.Entails
      (IProp.sep (IProp.sep persistent persistent) (IProp.sep selected remaining))
      (IProp.sep (IProp.sep persistent selected) (IProp.sep persistent remaining)) := by
  apply IProp.entails_trans (IProp.sep_assoc_left _ _ _)
  apply IProp.entails_trans
    (IProp.sep_mono (IProp.entails_refl _)
      (IProp.entails_trans (IProp.sep_assoc_right _ _ _)
        (IProp.entails_trans
          (IProp.sep_mono (IProp.sep_comm _ _) (IProp.entails_refl _))
          (IProp.sep_assoc_left _ _ _))))
  exact IProp.sep_assoc_right _ _ _

theorem partition_sound {names : List String}
    {context selected remaining : Context Loc Val}
    (partitioned : partition names context = some (selected, remaining)) :
    IProp.Entails context.denote (IProp.sep selected.denote remaining.denote) := by
  unfold partition at partitioned
  cases spatialPartition : context.spatial.partition names with
  | none => simp [spatialPartition] at partitioned
  | some result =>
      obtain ⟨selectedSpatial, remainingSpatial⟩ := result
      simp [spatialPartition] at partitioned
      obtain ⟨rfl, rfl⟩ := partitioned
      exact IProp.entails_trans
        (IProp.sep_mono (IProp.always_dup _)
          (Environment.partition_sound spatialPartition))
        (interleave _ _ _)

theorem extract_sound {name : String} {context remaining : Context Loc Val}
    {zone : Zone} {assertion : IProp Loc Val}
    (extracted : extract name context = some (zone, assertion, remaining)) :
    IProp.Entails context.denote (IProp.sep assertion remaining.denote) := by
  unfold extract at extracted
  cases persistentFound : context.persistent.lookup name with
  | some persistentAssertion =>
      simp [persistentFound] at extracted
      obtain ⟨rfl, rfl, rfl⟩ := extracted
      apply IProp.entails_trans
        (IProp.sep_mono (IProp.always_dup _) (IProp.entails_refl _))
      apply IProp.entails_trans (IProp.sep_assoc_left _ _ _)
      exact IProp.sep_mono
        (IProp.entails_trans (IProp.always_elim _)
          (Environment.and_lookup_sound persistentFound))
        (IProp.entails_refl _)
  | none =>
      simp [persistentFound] at extracted
      cases spatialErased : context.spatial.erase name with
      | none => simp [spatialErased] at extracted
      | some result =>
          obtain ⟨found, spatialRemaining⟩ := result
          simp [spatialErased] at extracted
          obtain ⟨rfl, rfl, rfl⟩ := extracted
          apply IProp.entails_trans
            (IProp.sep_mono (IProp.entails_refl _)
              (Environment.sep_erase_sound spatialErased))
          apply IProp.entails_trans (IProp.sep_comm _ _)
          apply IProp.entails_trans (IProp.sep_assoc_left _ _ _)
          exact IProp.sep_mono (IProp.entails_refl _) (IProp.sep_comm _ _)

theorem extractMany_sound {names : List String} {context remaining : Context Loc Val}
    {selected : IProp Loc Val}
    (extracted : extractMany names context = some (selected, remaining)) :
    IProp.Entails context.denote (IProp.sep selected remaining.denote) := by
  induction names generalizing context selected remaining with
  | nil => simp [extractMany] at extracted
  | cons name names induction =>
      cases names with
      | nil =>
          simp only [extractMany] at extracted
          cases first : context.extract name with
          | none => simp [first] at extracted
          | some result =>
              obtain ⟨zone, assertion, afterFirst⟩ := result
              simp [first] at extracted
              obtain ⟨rfl, rfl⟩ := extracted
              exact extract_sound first
      | cons next rest =>
          simp only [extractMany] at extracted
          cases first : context.extract name with
          | none => simp [first] at extracted
          | some result =>
              obtain ⟨zone, assertion, afterFirst⟩ := result
              cases remainingExtracted : extractMany (next :: rest) afterFirst with
              | none => simp [first, remainingExtracted] at extracted
              | some remainingResult =>
                  obtain ⟨restSelected, finalRemaining⟩ := remainingResult
                  simp [first, remainingExtracted] at extracted
                  obtain ⟨rfl, rfl⟩ := extracted
                  exact IProp.entails_trans (extract_sound first)
                    (IProp.entails_trans
                      (IProp.sep_mono (IProp.entails_refl _)
                        (induction remainingExtracted))
                      (IProp.sep_assoc_right _ _ _))

theorem moveToPersistent_sound {name : String} {context updated : Context Loc Val}
    {assertion : IProp Loc Val}
    (moved : moveToPersistent name context = some (assertion, updated))
    (persistent : IProp.Entails assertion (IProp.always assertion)) :
    IProp.Entails context.denote updated.denote := by
  unfold moveToPersistent at moved
  cases erased : context.spatial.erase name with
  | none => simp [erased] at moved
  | some result =>
      obtain ⟨found, remaining⟩ := result
      simp [erased] at moved
      obtain ⟨rfl, rfl⟩ := moved
      apply IProp.entails_trans
        (IProp.sep_mono (IProp.entails_refl _)
          (IProp.entails_trans (Environment.sep_erase_sound erased)
            (IProp.sep_mono persistent (IProp.entails_refl _))))
      apply IProp.entails_trans (IProp.sep_assoc_right _ _ _)
      exact IProp.sep_mono
        (IProp.entails_trans
          (IProp.and_intro (IProp.sep_elim_right _ _) (IProp.sep_elim_left _ _))
          (by simpa [Environment.andDenote] using
            (IProp.always_and_intro found context.persistent.andDenote)))
        (IProp.entails_refl _)

end Context

variable {Loc : Type u} {Val : Type v}

/-- Semantic validity of a flat proof-mode goal. -/
def Valid (context : Context Loc Val) (goal : IProp Loc Val) : Prop :=
  IProp.Entails context.denote goal

end MPSL.ProofMode
