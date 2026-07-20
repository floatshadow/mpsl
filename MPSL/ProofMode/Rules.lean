import MPSL.ProofMode.Context

set_option autoImplicit false

namespace MPSL.ProofMode

universe u v w

variable {Loc : Type u} {Val : Type v}

private theorem truthToEmpty :
    IProp.Entails (IProp.truth : IProp Loc Val) Context.empty.denote := by
  apply IProp.entails_trans
    (IProp.always_intro_from_truth (IProp.entails_refl IProp.truth))
  simpa [Context.empty, Context.denote, Environment.andDenote,
    Environment.sepDenote] using
    (IProp.sep_truth_intro_right (IProp.always (IProp.truth : IProp Loc Val)))

/-- Enter the flat proof mode by turning the outer entailment into a wand. -/
theorem start [DecidableEq Loc] {premise goal : Formula Loc Val} :
    Valid Context.empty (IProp.wand premise.denote goal.denote) -> premise ⊢ goal := by
  intro valid
  apply IProp.entails_trans (IProp.sep_truth_intro_left premise.denote)
  apply IProp.entails_trans
    (IProp.sep_mono (IProp.entails_trans truthToEmpty valid)
      (IProp.entails_refl premise.denote))
  exact IProp.wand_elim premise.denote goal.denote

theorem exactNamed {context : Context Loc Val} {zone : Zone} {found goal : IProp Loc Val}
    (name : String) (lookupFound : context.lookup name = some (zone, found))
    (sameDenotation : found = goal) : Valid context goal := by
  subst goal
  exact Context.lookup_sound lookupFound

/-- Wand introduction always appends its premise to the spatial environment. -/
theorem wandIntroSpatial (name : String) {context : Context Loc Val}
    {premise conclusion : IProp Loc Val} :
    Valid (context.snoc .spatial name premise) conclusion ->
    Valid context (IProp.wand premise conclusion) := by
  intro valid
  apply IProp.wand_intro
  apply IProp.entails_trans (IProp.sep_assoc_left _ _ _)
  apply IProp.entails_trans
    (IProp.sep_mono (IProp.entails_refl _) (IProp.sep_comm _ _))
  simpa [Valid, Context.snoc, Context.denote, Environment.sepDenote] using valid

/-- A nonpersistent implication premise may be spatial when the spatial context is empty. -/
theorem impIntroSpatial (name : String) {persistent : Environment Loc Val}
    {premise conclusion : IProp Loc Val} :
    Valid ((Context.mk persistent []).snoc .spatial name premise) conclusion ->
    Valid (Context.mk persistent []) (IProp.imp premise conclusion) := by
  intro valid
  apply IProp.imp_intro
  apply IProp.entails_trans _ valid
  intro heap step holds
  have persistentHolds :=
    IProp.sep_elim_left (IProp.always persistent.andDenote) IProp.truth
      heap step holds.1
  exact ⟨Heap.empty, heap, Heap.disjoint_empty_left heap, Heap.union_empty_left heap,
    persistentHolds,
    heap, Heap.empty, Heap.disjoint_empty_right heap, Heap.union_empty_right heap,
    holds.2, True.intro⟩

/-- Persistent implication introduction, corresponding to Iris's `#` pattern.

```text
P ⊢ □ P    P, Γp ; Γs ⊢ Q
──────────────────────────
      Γp ; Γs ⊢ P ⇒ Q
```
-/
theorem impIntroPersistent (name : String) {context : Context Loc Val}
    {premise conclusion : IProp Loc Val}
    (persistent : IProp.Entails premise (IProp.always premise)) :
    Valid (context.snoc .persistent name premise) conclusion ->
    Valid context (IProp.imp premise conclusion) := by
  intro valid
  apply IProp.imp_intro
  apply IProp.entails_trans _ valid
  intro heap step holds
  have boxedPremise := persistent heap step holds.2
  have boxedContext := IProp.sep_elim_left _ _ heap step holds.1
  have spatialContext := IProp.sep_elim_right _ _ heap step holds.1
  have boxedCombined :=
    IProp.always_and_intro premise context.persistent.andDenote
      heap step ⟨boxedPremise, boxedContext⟩
  exact ⟨Heap.empty, heap, Heap.disjoint_empty_left heap, Heap.union_empty_left heap,
    boxedCombined, spatialContext⟩

/-- Move a spatial hypothesis into the persistent environment.

```text
P ⊢ □ P    Γp, h : P ; Γs ⊢ R
──────────────────────────────
      Γp ; h : P, Γs ⊢ R
```
-/
theorem persistent (name : String) {context updated : Context Loc Val}
    {assertion goal : IProp Loc Val}
    (moved : context.moveToPersistent name = some (assertion, updated))
    (isPersistent : IProp.Entails assertion (IProp.always assertion)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans (Context.moveToPersistent_sound moved isPersistent) valid

/-- Split a spatial separating hypothesis into two spatial hypotheses.

```text
Γp ; h : P ∗ Q, Γs ⊢ R
─────────────────────────
 Γp ; h₁ : P, h₂ : Q, Γs ⊢ R
```
-/
theorem sepDestructSpatial (source leftName rightName : String)
    {context updated : Context Loc Val} {left right goal : IProp Loc Val}
    (replaced : context.replace source [⟨leftName, left⟩, ⟨rightName, right⟩] =
      some (.spatial, IProp.sep left right, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  have replacementSound : IProp.Entails (IProp.sep left right)
      (Environment.sepDenote [⟨leftName, left⟩, ⟨rightName, right⟩]) :=
    IProp.sep_mono (IProp.entails_refl left) (IProp.sep_truth_intro_right right)
  exact IProp.entails_trans
    (Context.replaceSpatial_sound replaced replacementSound) valid

/-- A persistent separating hypothesis may be exposed as two reusable hypotheses. -/
theorem sepDestructPersistent (source leftName rightName : String)
    {context updated : Context Loc Val} {left right goal : IProp Loc Val}
    (replaced : context.replace source [⟨leftName, left⟩, ⟨rightName, right⟩] =
      some (.persistent, IProp.sep left right, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  have replacementSound : IProp.Entails (IProp.sep left right)
      (Environment.andDenote [⟨leftName, left⟩, ⟨rightName, right⟩]) :=
    IProp.and_intro (IProp.sep_elim_left left right)
      (IProp.and_intro (IProp.sep_elim_right left right)
        (IProp.truth_intro (IProp.sep left right)))
  exact IProp.entails_trans
    (Context.replacePersistent_sound replaced replacementSound) valid

/-- Additive conjunction can be decomposed only in the persistent zone. -/
theorem andDestructPersistent (source leftName rightName : String)
    {context updated : Context Loc Val} {left right goal : IProp Loc Val}
    (replaced : context.replace source [⟨leftName, left⟩, ⟨rightName, right⟩] =
      some (.persistent, IProp.and left right, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  have replacementSound : IProp.Entails (IProp.and left right)
      (Environment.andDenote [⟨leftName, left⟩, ⟨rightName, right⟩]) :=
    IProp.and_intro (IProp.and_elim_left left right)
      (IProp.and_intro (IProp.and_elim_right left right)
        (IProp.truth_intro (IProp.and left right)))
  exact IProp.entails_trans
    (Context.replacePersistent_sound replaced replacementSound) valid

/-- Destruct a spatial additive conjunction when its left conjunct is persistent.

```text
P ⊢ □ P    Γp, h₁ : P ; h₂ : Q, Γs ⊢ R
────────────────────────────────────────
          Γp ; h : P ∧ Q, Γs ⊢ R
```
-/
theorem andDestructSpatialPersistentLeft (source persistentName spatialName : String)
    {context : Context Loc Val} {remaining : Environment Loc Val}
    {left right goal : IProp Loc Val}
    (erased : context.spatial.erase source =
      some (IProp.and left right, remaining))
    (isPersistent : IProp.Entails left (IProp.always left)) :
    Valid ⟨⟨persistentName, left⟩ :: context.persistent,
      ⟨spatialName, right⟩ :: remaining⟩ goal ->
    Valid context goal := by
  intro valid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union, persistentHolds, spatialHolds⟩ := holds
  have extracted := Environment.sep_erase_sound erased spatialHeap step spatialHolds
  obtain ⟨sourceHeap, remainingHeap, sourceDisjoint, sourceUnion,
    sourceHolds, remainingHolds⟩ := extracted
  have boxedLeft := isPersistent sourceHeap step sourceHolds.1
  have combinedPersistent :=
    IProp.always_and_intro left context.persistent.andDenote
      persistentHeap step ⟨boxedLeft, persistentHolds⟩
  apply valid heap step
  exact ⟨persistentHeap, spatialHeap, disjoint, union, combinedPersistent,
    sourceHeap, remainingHeap, sourceDisjoint, sourceUnion,
    sourceHolds.2, remainingHolds⟩

/-- Symmetric spatial conjunction destruction with a persistent right conjunct. -/
theorem andDestructSpatialPersistentRight (source spatialName persistentName : String)
    {context : Context Loc Val} {remaining : Environment Loc Val}
    {left right goal : IProp Loc Val}
    (erased : context.spatial.erase source =
      some (IProp.and left right, remaining))
    (isPersistent : IProp.Entails right (IProp.always right)) :
    Valid ⟨⟨persistentName, right⟩ :: context.persistent,
      ⟨spatialName, left⟩ :: remaining⟩ goal ->
    Valid context goal := by
  intro valid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union, persistentHolds, spatialHolds⟩ := holds
  have extracted := Environment.sep_erase_sound erased spatialHeap step spatialHolds
  obtain ⟨sourceHeap, remainingHeap, sourceDisjoint, sourceUnion,
    sourceHolds, remainingHolds⟩ := extracted
  have boxedRight := isPersistent sourceHeap step sourceHolds.2
  have combinedPersistent :=
    IProp.always_and_intro right context.persistent.andDenote
      persistentHeap step ⟨boxedRight, persistentHolds⟩
  apply valid heap step
  exact ⟨persistentHeap, spatialHeap, disjoint, union, combinedPersistent,
    sourceHeap, remainingHeap, sourceDisjoint, sourceUnion,
    sourceHolds.1, remainingHolds⟩

theorem andIntro {context : Context Loc Val} {left right : IProp Loc Val} :
    Valid context left -> Valid context right -> Valid context (IProp.and left right) :=
  IProp.and_intro

theorem orIntroLeft {context : Context Loc Val} {left right : IProp Loc Val} :
    Valid context left -> Valid context (IProp.or left right) := by
  intro valid
  exact IProp.entails_trans valid (IProp.or_intro_left left right)

theorem orIntroRight {context : Context Loc Val} {left right : IProp Loc Val} :
    Valid context right -> Valid context (IProp.or left right) := by
  intro valid
  exact IProp.entails_trans valid (IProp.or_intro_right left right)

/-- Eliminate a disjunction at a named spatial hypothesis. -/
theorem orDestructSpatial (source leftName rightName : String)
    {context : Context Loc Val} {front suffix : Environment Loc Val}
    {left right goal : IProp Loc Val}
    (focused : context.spatial.focus source =
      some (front, IProp.or left right, suffix)) :
    Valid ⟨context.persistent, front ++ ⟨leftName, left⟩ :: suffix⟩ goal ->
    Valid ⟨context.persistent, front ++ ⟨rightName, right⟩ :: suffix⟩ goal ->
    Valid context goal := by
  intro leftValid rightValid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union,
    persistentHolds, spatialHolds⟩ := holds
  have focusedHolds := Environment.sep_focus_sound focused spatialHeap step spatialHolds
  obtain ⟨frontHeap, sourceSuffixHeap, frontDisjoint, frontUnion,
    frontHolds, sourceSuffixHolds⟩ := focusedHolds
  obtain ⟨sourceHeap, suffixHeap, sourceDisjoint, sourceUnion,
    sourceHolds, suffixHolds⟩ := sourceSuffixHolds
  cases sourceHolds with
  | inl leftHolds =>
      have updatedSpatial :=
        Environment.sep_focus_replace_intro front suffix ⟨leftName, left⟩
          spatialHeap step
          ⟨frontHeap, sourceSuffixHeap, frontDisjoint, frontUnion, frontHolds,
            sourceHeap, suffixHeap, sourceDisjoint, sourceUnion, leftHolds, suffixHolds⟩
      exact leftValid heap step
        ⟨persistentHeap, spatialHeap, disjoint, union, persistentHolds, updatedSpatial⟩
  | inr rightHolds =>
      have updatedSpatial :=
        Environment.sep_focus_replace_intro front suffix ⟨rightName, right⟩
          spatialHeap step
          ⟨frontHeap, sourceSuffixHeap, frontDisjoint, frontUnion, frontHolds,
            sourceHeap, suffixHeap, sourceDisjoint, sourceUnion, rightHolds, suffixHolds⟩
      exact rightValid heap step
        ⟨persistentHeap, spatialHeap, disjoint, union, persistentHolds, updatedSpatial⟩

/-- Eliminate a disjunction at a named persistent hypothesis. -/
theorem orDestructPersistent (source leftName rightName : String)
    {context : Context Loc Val} {front suffix : Environment Loc Val}
    {left right goal : IProp Loc Val}
    (focused : context.persistent.focus source =
      some (front, IProp.or left right, suffix)) :
    Valid ⟨front ++ ⟨leftName, left⟩ :: suffix, context.spatial⟩ goal ->
    Valid ⟨front ++ ⟨rightName, right⟩ :: suffix, context.spatial⟩ goal ->
    Valid context goal := by
  intro leftValid rightValid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union,
    persistentHolds, spatialHolds⟩ := holds
  have focusedHolds :=
    Environment.and_focus_sound focused Heap.empty step persistentHolds
  cases focusedHolds.2.1 with
  | inl leftHolds =>
      have updatedPersistent :=
        Environment.and_focus_replace_intro front suffix ⟨leftName, left⟩
          Heap.empty step ⟨focusedHolds.1, leftHolds, focusedHolds.2.2⟩
      exact leftValid heap step
        ⟨persistentHeap, spatialHeap, disjoint, union, updatedPersistent, spatialHolds⟩
  | inr rightHolds =>
      have updatedPersistent :=
        Environment.and_focus_replace_intro front suffix ⟨rightName, right⟩
          Heap.empty step ⟨focusedHolds.1, rightHolds, focusedHolds.2.2⟩
      exact rightValid heap step
        ⟨persistentHeap, spatialHeap, disjoint, union, updatedPersistent, spatialHolds⟩

/-- Spatial split with the named hypotheses assigned to the left goal. -/
theorem sepIntroLeft (names : List String)
    {context leftContext rightContext : Context Loc Val} {left right : IProp Loc Val}
    (partitioned : context.partition names = some (leftContext, rightContext)) :
    Valid leftContext left -> Valid rightContext right ->
    Valid context (IProp.sep left right) := by
  intro leftValid rightValid
  exact IProp.entails_trans (Context.partition_sound partitioned)
    (IProp.sep_mono leftValid rightValid)

/-- Spatial split with the named hypotheses assigned to the right goal. -/
theorem sepIntroRight (names : List String)
    {context rightContext leftContext : Context Loc Val} {left right : IProp Loc Val}
    (partitioned : context.partition names = some (rightContext, leftContext)) :
    Valid leftContext left -> Valid rightContext right ->
    Valid context (IProp.sep left right) := by
  intro leftValid rightValid
  exact IProp.entails_trans (Context.partition_sound partitioned)
    (IProp.entails_trans (IProp.sep_mono rightValid leftValid) (IProp.sep_comm _ _))

/-- Split a separating goal without partitioning when its left operand is persistent. -/
theorem sepIntroPersistentLeft {context : Context Loc Val} {left right : IProp Loc Val}
    (persistentLeft : IProp.Entails left (IProp.always left)) :
    Valid context left -> Valid context right -> Valid context (IProp.sep left right) := by
  intro leftValid rightValid heap step contextHolds
  have boxedLeft := persistentLeft heap step (leftValid heap step contextHolds)
  exact ⟨Heap.empty, heap, Heap.disjoint_empty_left heap, Heap.union_empty_left heap,
    boxedLeft, rightValid heap step contextHolds⟩

/-- Symmetric persistent-operand split. -/
theorem sepIntroPersistentRight {context : Context Loc Val} {left right : IProp Loc Val}
    (persistentRight : IProp.Entails right (IProp.always right)) :
    Valid context left -> Valid context right -> Valid context (IProp.sep left right) := by
  intro leftValid rightValid heap step contextHolds
  have boxedRight := persistentRight heap step (rightValid heap step contextHolds)
  exact ⟨heap, Heap.empty, Heap.disjoint_empty_right heap, Heap.union_empty_right heap,
    leftValid heap step contextHolds, boxedRight⟩

theorem impApplyNamed (implicationName premiseName : String)
    {context : Context Loc Val} {implicationZone premiseZone : Zone}
    {premise conclusion : IProp Loc Val}
    (implicationFound : context.lookup implicationName =
      some (implicationZone, IProp.imp premise conclusion))
    (premiseFound : context.lookup premiseName = some (premiseZone, premise)) :
    Valid context conclusion := by
  exact IProp.entails_trans
    (IProp.and_intro (Context.lookup_sound implicationFound)
      (Context.lookup_sound premiseFound))
    (IProp.imp_elim premise conclusion)

theorem wandApplyNamed (wandName premiseName : String)
    {context afterWand remaining : Context Loc Val} {wandZone premiseZone : Zone}
    {premise conclusion : IProp Loc Val}
    (wandExtracted : context.extract wandName =
      some (wandZone, IProp.wand premise conclusion, afterWand))
    (premiseExtracted : afterWand.extract premiseName =
      some (premiseZone, premise, remaining)) :
    Valid context conclusion := by
  apply IProp.entails_trans (Context.extract_sound wandExtracted)
  apply IProp.entails_trans
    (IProp.sep_mono (IProp.entails_refl _) (Context.extract_sound premiseExtracted))
  apply IProp.entails_trans (IProp.sep_assoc_right _ _ _)
  exact IProp.entails_trans
    (IProp.sep_mono (IProp.wand_elim premise conclusion) (IProp.entails_refl _))
    (IProp.sep_elim_left _ _)

theorem truthIntro {context : Context Loc Val} : Valid context IProp.truth :=
  IProp.truth_intro context.denote

theorem falsumElim (name : String) {context : Context Loc Val} {zone : Zone}
    {goal : IProp Loc Val}
    (found : context.lookup name = some (zone, IProp.falsum)) : Valid context goal :=
  IProp.entails_trans (Context.lookup_sound found) (IProp.falsum_elim goal)

theorem eqRefl {context : Context Loc Val} {ty : Ty} {term : Ty.denote Loc Val ty} :
    Valid context (IProp.equal (Ty.EquivAt Loc Val ty)
      (Ty.equivAt_mono Loc Val ty) term term) := by
  exact IProp.entails_trans (IProp.truth_intro context.denote)
    (IProp.equal_refl (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty)
      (fun step value => Ty.equivAt_refl Loc Val ty value) term)

theorem eqSymmNamed (name : String) {context : Context Loc Val} {zone : Zone} {ty : Ty}
    {left right : Ty.denote Loc Val ty}
    (found : context.lookup name = some (zone,
      IProp.equal (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty) left right)) :
    Valid context
      (IProp.equal (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty) right left) := by
  exact IProp.entails_trans (Context.lookup_sound found)
    (IProp.equal_symm (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty)
      (Ty.equivAt_symm Loc Val ty) left right)

theorem eqTransNamed (firstName secondName : String)
    {context : Context Loc Val} {firstZone secondZone : Zone} {ty : Ty}
    {first second third : Ty.denote Loc Val ty}
    (firstFound : context.lookup firstName = some (firstZone,
      IProp.equal (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty) first second))
    (secondFound : context.lookup secondName = some (secondZone,
      IProp.equal (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty) second third)) :
    Valid context
      (IProp.equal (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty) first third) := by
  exact IProp.entails_trans
    (IProp.and_intro (Context.lookup_sound firstFound) (Context.lookup_sound secondFound))
    (IProp.equal_trans (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty)
      (Ty.equivAt_trans Loc Val ty) first second third)

theorem existsIntro {Witness : Type w} {context : Context Loc Val}
    {body : Witness -> IProp Loc Val} (witness : Witness) :
    Valid context (body witness) -> Valid context (IProp.exists_ body) := by
  intro valid
  exact IProp.entails_trans valid (IProp.exists_intro body witness)

/-- Eliminate an existential at a named spatial hypothesis. -/
theorem existsDestructSpatial (source name : String) {Witness : Type w}
    {context : Context Loc Val} {front suffix : Environment Loc Val}
    {body : Witness -> IProp Loc Val} {goal : IProp Loc Val}
    (focused : context.spatial.focus source =
      some (front, IProp.exists_ body, suffix)) :
    (forall witness,
      Valid ⟨context.persistent, front ++ ⟨name, body witness⟩ :: suffix⟩ goal) ->
    Valid context goal := by
  intro valid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union,
    persistentHolds, spatialHolds⟩ := holds
  have focusedHolds := Environment.sep_focus_sound focused spatialHeap step spatialHolds
  obtain ⟨frontHeap, sourceSuffixHeap, frontDisjoint, frontUnion,
    frontHolds, sourceSuffixHolds⟩ := focusedHolds
  obtain ⟨sourceHeap, suffixHeap, sourceDisjoint, sourceUnion,
    ⟨witness, witnessHolds⟩, suffixHolds⟩ := sourceSuffixHolds
  have updatedSpatial :=
    Environment.sep_focus_replace_intro front suffix ⟨name, body witness⟩
      spatialHeap step
      ⟨frontHeap, sourceSuffixHeap, frontDisjoint, frontUnion, frontHolds,
        sourceHeap, suffixHeap, sourceDisjoint, sourceUnion, witnessHolds, suffixHolds⟩
  exact valid witness heap step
    ⟨persistentHeap, spatialHeap, disjoint, union, persistentHolds, updatedSpatial⟩

/-- Eliminate an existential at a named persistent hypothesis. -/
theorem existsDestructPersistent (source name : String) {Witness : Type w}
    {context : Context Loc Val} {front suffix : Environment Loc Val}
    {body : Witness -> IProp Loc Val} {goal : IProp Loc Val}
    (focused : context.persistent.focus source =
      some (front, IProp.exists_ body, suffix)) :
    (forall witness,
      Valid ⟨front ++ ⟨name, body witness⟩ :: suffix, context.spatial⟩ goal) ->
    Valid context goal := by
  intro valid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union,
    persistentHolds, spatialHolds⟩ := holds
  have focusedHolds :=
    Environment.and_focus_sound focused Heap.empty step persistentHolds
  obtain ⟨witness, witnessHolds⟩ := focusedHolds.2.1
  have updatedPersistent :=
    Environment.and_focus_replace_intro front suffix ⟨name, body witness⟩
      Heap.empty step ⟨focusedHolds.1, witnessHolds, focusedHolds.2.2⟩
  exact valid witness heap step
    ⟨persistentHeap, spatialHeap, disjoint, union, updatedPersistent, spatialHolds⟩

theorem forallIntro {Witness : Type w} {context : Context Loc Val}
    {body : Witness -> IProp Loc Val} :
    (forall witness, Valid context (body witness)) -> Valid context (IProp.forall_ body) :=
  IProp.forall_intro

/-- Specializing a persistent universal retains the general specification.

```text
Γp, H : ∀ x, Φ x, Ht : Φ t ; Γs ⊢ R
──────────────────────────────────────
       Γp, H : ∀ x, Φ x ; Γs ⊢ R
```
-/
theorem forallElimPersistent (source specializedName : String) {Witness : Type w}
    (witness : Witness) {context : Context Loc Val}
    {body : Witness -> IProp Loc Val} {goal : IProp Loc Val}
    (found : context.persistent.lookup source = some (IProp.forall_ body)) :
    Valid (context.snoc .persistent specializedName (body witness)) goal ->
    Valid context goal := by
  intro valid heap step holds
  obtain ⟨persistentHeap, spatialHeap, disjoint, union,
    persistentHolds, spatialHolds⟩ := holds
  have universalHolds :=
    Environment.and_lookup_sound found Heap.empty step persistentHolds
  have instanceHolds := universalHolds witness
  have updatedPersistent :=
    IProp.always_and_intro (body witness) context.persistent.andDenote
      persistentHeap step ⟨instanceHolds, persistentHolds⟩
  exact valid heap step
    ⟨persistentHeap, spatialHeap, disjoint, union, updatedPersistent, spatialHolds⟩

theorem forallElimSpatial (source specializedName : String) {Witness : Type w}
    (witness : Witness) {context updated : Context Loc Val}
    {body : Witness -> IProp Loc Val} {goal : IProp Loc Val}
    (replaced : context.replace source [⟨specializedName, body witness⟩] =
      some (.spatial, IProp.forall_ body, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  have replacementSound : IProp.Entails (IProp.forall_ body)
      (Environment.sepDenote [⟨specializedName, body witness⟩]) :=
    IProp.entails_trans (IProp.forall_elim body witness)
      (IProp.sep_truth_intro_right _)
  exact IProp.entails_trans
    (Context.replaceSpatial_sound replaced replacementSound) valid

/-- Eliminate `□ P` after it has entered the persistent environment. -/
theorem alwaysElimPersistent (source name : String) {context updated : Context Loc Val}
    {assertion goal : IProp Loc Val}
    (replaced : context.replace source [⟨name, assertion⟩] =
      some (.persistent, IProp.always assertion, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  have replacementSound : IProp.Entails (IProp.always assertion)
      (Environment.andDenote [⟨name, assertion⟩]) :=
    IProp.and_intro (IProp.always_elim assertion)
      (IProp.truth_intro (IProp.always assertion))
  exact IProp.entails_trans
    (Context.replacePersistent_sound replaced replacementSound) valid

theorem alwaysIntro {persistent : Environment Loc Val} {goal : IProp Loc Val} :
    Valid (Context.mk persistent []) goal ->
    Valid (Context.mk persistent []) (IProp.always goal) := by
  intro valid
  apply IProp.entails_trans _ (IProp.always_mono valid)
  intro heap step holds
  have boxed := IProp.sep_elim_left _ _ heap step holds
  exact ⟨Heap.empty, Heap.empty, Heap.disjoint_empty_left Heap.empty,
    Heap.union_empty_left Heap.empty, boxed, True.intro⟩

theorem laterIntro {context : Context Loc Val} {goal : IProp Loc Val} :
    Valid context goal -> Valid context (IProp.later goal) := by
  intro valid
  exact IProp.entails_trans valid (IProp.later_intro goal)

/-- Löb induction when there are no spatial hypotheses.

```text
Γp, ih : ▷ R ; · ⊢ R
─────────────────────
      Γp ; · ⊢ R
```
-/
theorem lobEmpty (name : String) {persistent : Environment Loc Val}
    {goal : IProp Loc Val} :
    Valid ((Context.mk persistent []).snoc .persistent name (IProp.later goal)) goal ->
    Valid (Context.mk persistent []) goal := by
  intro valid heap step contextHolds
  induction step generalizing heap with
  | zero =>
      apply valid heap 0
      obtain ⟨_, _, _, _, persistentHolds, _⟩ := contextHolds
      refine ⟨Heap.empty, heap, Heap.disjoint_empty_left heap,
        Heap.union_empty_left heap, ?_, True.intro⟩
      exact ⟨SProp.zero_mem_later (goal.holds Heap.empty), persistentHolds⟩
  | succ previous induction =>
      apply valid heap (Nat.succ previous)
      obtain ⟨_, _, _, _, persistentHolds, _⟩ := contextHolds
      refine ⟨Heap.empty, heap, Heap.disjoint_empty_left heap,
        Heap.union_empty_left heap, ?_, True.intro⟩
      refine ⟨(SProp.succ_mem_later_iff (goal.holds Heap.empty) previous).2 ?_,
        persistentHolds⟩
      apply induction Heap.empty
      refine ⟨Heap.empty, Heap.empty, Heap.disjoint_empty_left Heap.empty,
        Heap.union_empty_left Heap.empty, ?_, True.intro⟩
      exact persistent.andDenote.holds Heap.empty |>.downward
        (Nat.le_succ previous) persistentHolds

/-- Löb induction over the whole current spatial sequent.

The induction predicate is `Γs −∗ R`, rather than just `R`, so the visible
spatial hypotheses remain available without being duplicated between steps.

```text
Γp, ih : ▷ (Γs −∗ R) ; Γs ⊢ R
────────────────────────────────
             Γp ; Γs ⊢ R
```
-/
theorem lob (name : String) {context : Context Loc Val} {goal : IProp Loc Val} :
    Valid (context.snoc .persistent name
      (IProp.later (IProp.wand context.spatial.sepDenote goal))) goal ->
    Valid context goal := by
  intro valid heap step contextHolds
  induction step using Nat.strongRecOn generalizing heap with
  | ind step induction =>
      apply valid heap step
      obtain ⟨persistentHeap, spatialHeap, disjoint, combined,
        persistentHolds, spatialHolds⟩ := contextHolds
      have spatialHoldsWhole := context.spatial.sepDenote.monotone
        (Heap.subheap_of_union_eq_right disjoint combined) spatialHolds
      refine ⟨Heap.empty, heap, Heap.disjoint_empty_left heap,
        Heap.union_empty_left heap, ?_, spatialHoldsWhole⟩
      change step ∈ (IProp.and
        (IProp.later (IProp.wand context.spatial.sepDenote goal))
        context.persistent.andDenote).holds Heap.empty
      refine ⟨?_, persistentHolds⟩
      cases step with
      | zero =>
          exact SProp.zero_mem_later
            ((IProp.wand context.spatial.sepDenote goal).holds Heap.empty)
      | succ previous =>
          apply (SProp.succ_mem_later_iff
            ((IProp.wand context.spatial.sepDenote goal).holds Heap.empty)
            previous).2
          intro smaller included extra _ spatialHoldsExtra
          rw [Heap.union_empty_left]
          apply induction smaller (by omega) extra
          refine ⟨Heap.empty, extra, Heap.disjoint_empty_left extra,
            Heap.union_empty_left extra, ?_, spatialHoldsExtra⟩
          exact context.persistent.andDenote.holds Heap.empty |>.downward
            (Nat.le_trans included (Nat.le_succ previous)) persistentHolds

/-- Later monotonicity at a named spatial hypothesis.

```text
Γp ; h : ▷ P, Γs ⊢ ▷ Q
──────────────────────────
  Γp ; h' : P, Γs ⊢ Q
```
-/
theorem laterMonoSpatial (source name : String)
    {context : Context Loc Val} {front suffix : Environment Loc Val}
    {premise goal : IProp Loc Val}
    (focused : context.spatial.focus source =
      some (front, IProp.later premise, suffix)) :
    Valid ⟨context.persistent, front ++ ⟨name, premise⟩ :: suffix⟩ goal ->
    Valid context (IProp.later goal) := by
  intro valid
  apply IProp.entails_trans
    (IProp.sep_mono
      (IProp.later_intro (IProp.always context.persistent.andDenote))
      (Environment.later_focus_replace_sound focused))
  apply IProp.entails_trans
    (IProp.later_sep_intro (IProp.always context.persistent.andDenote)
      (front ++ ⟨name, premise⟩ :: suffix).sepDenote)
  exact IProp.later_mono valid

theorem clearPersistent (name : String) {context updated : Context Loc Val}
    {source goal : IProp Loc Val}
    (replaced : context.replace name [] = some (.persistent, source, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Context.replacePersistent_sound replaced (IProp.truth_intro source)) valid

theorem clearSpatial (name : String) {context updated : Context Loc Val}
    {source goal : IProp Loc Val}
    (replaced : context.replace name [] = some (.spatial, source, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Context.replaceSpatial_sound replaced (IProp.truth_intro source)) valid

theorem frame (name : String) {context remaining : Context Loc Val} {zone : Zone}
    {framed goal : IProp Loc Val}
    (extracted : context.extract name = some (zone, framed, remaining)) :
    Valid remaining goal -> Valid context (IProp.sep framed goal) := by
  intro valid
  exact IProp.entails_trans (Context.extract_sound extracted)
    (IProp.sep_mono (IProp.entails_refl framed) valid)

theorem frameRight (name : String) {context remaining : Context Loc Val} {zone : Zone}
    {framed goal : IProp Loc Val}
    (extracted : context.extract name = some (zone, framed, remaining)) :
    Valid remaining goal -> Valid context (IProp.sep goal framed) := by
  intro valid
  exact IProp.entails_trans (Context.extract_sound extracted)
    (IProp.entails_trans (IProp.sep_mono (IProp.entails_refl framed) valid)
      (IProp.sep_comm framed goal))

theorem frameMany (names : List String) {context remaining : Context Loc Val}
    {framed goal : IProp Loc Val}
    (extracted : context.extractMany names = some (framed, remaining)) :
    Valid remaining goal -> Valid context (IProp.sep framed goal) := by
  intro valid
  exact IProp.entails_trans (Context.extractMany_sound extracted)
    (IProp.sep_mono (IProp.entails_refl framed) valid)

theorem stop {context : Context Loc Val} {goal : IProp Loc Val} :
    Valid context goal -> IProp.Entails context.denote goal := fun valid => valid

end MPSL.ProofMode
