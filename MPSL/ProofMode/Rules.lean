import MPSL.ProofMode.Bunch

set_option autoImplicit false

namespace MPSL.ProofMode

universe u v w

variable {Loc : Type u} {Val : Type v}

theorem start [DecidableEq Loc] (name : String) {premise goal : Formula Loc Val} :
    Valid (.hyp name premise.denote) goal.denote -> premise ⊢ goal := by
  intro valid
  exact valid

theorem exactNamed {context : Bunch Loc Val} {found goal : IProp Loc Val}
    (name : String) (lookupFound : context.lookup name = some found)
    (sameDenotation : found = goal) : Valid context goal := by
  subst goal
  exact Bunch.lookup_sound lookupFound

theorem exactAddLeft {left right : Bunch Loc Val} {goal : IProp Loc Val} :
    Valid left goal -> Valid (.additive left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.and_elim_left left.denote right.denote) valid

theorem exactAddRight {left right : Bunch Loc Val} {goal : IProp Loc Val} :
    Valid right goal -> Valid (.additive left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.and_elim_right left.denote right.denote) valid

theorem exactMulLeft {left right : Bunch Loc Val} {goal : IProp Loc Val} :
    Valid left goal -> Valid (.multiplicative left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.sep_elim_left left.denote right.denote) valid

theorem exactMulRight {left right : Bunch Loc Val} {goal : IProp Loc Val} :
    Valid right goal -> Valid (.multiplicative left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.sep_elim_right left.denote right.denote) valid

theorem andDestruct (source leftName rightName : String)
    {context updated : Bunch Loc Val} {left right goal : IProp Loc Val}
    (replaced : Bunch.replace source
      (.additive (.hyp leftName left) (.hyp rightName right)) context =
      some (IProp.and left right, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Bunch.replace_sound replaced (IProp.entails_refl (IProp.and left right))) valid

theorem sepDestruct (source leftName rightName : String)
    {context updated : Bunch Loc Val} {left right goal : IProp Loc Val}
    (replaced : Bunch.replace source
      (.multiplicative (.hyp leftName left) (.hyp rightName right)) context =
      some (IProp.sep left right, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Bunch.replace_sound replaced (IProp.entails_refl (IProp.sep left right))) valid

theorem orDestruct (source leftName rightName : String) {left right goal : IProp Loc Val} :
    Valid (.hyp leftName left) goal -> Valid (.hyp rightName right) goal ->
    Valid (.hyp source (IProp.or left right)) goal := by
  intro fromLeft fromRight
  exact IProp.or_elim fromLeft fromRight

theorem andIntro {context : Bunch Loc Val} {left right : IProp Loc Val} :
    Valid context left -> Valid context right ->
    Valid context (IProp.and left right) := by
  exact IProp.and_intro

theorem orIntroLeft {context : Bunch Loc Val} {left right : IProp Loc Val} :
    Valid context left -> Valid context (IProp.or left right) := by
  intro valid
  exact IProp.entails_trans valid (IProp.or_intro_left left right)

theorem orIntroRight {context : Bunch Loc Val} {left right : IProp Loc Val} :
    Valid context right -> Valid context (IProp.or left right) := by
  intro valid
  exact IProp.entails_trans valid (IProp.or_intro_right left right)

theorem impIntro (name : String) {context : Bunch Loc Val} {premise conclusion : IProp Loc Val} :
    Valid (.additive context (.hyp name premise)) conclusion ->
    Valid context (IProp.imp premise conclusion) := by
  exact IProp.imp_intro

theorem wandIntro (name : String) {context : Bunch Loc Val} {premise conclusion : IProp Loc Val} :
    Valid (.multiplicative context (.hyp name premise)) conclusion ->
    Valid context (IProp.wand premise conclusion) := by
  exact IProp.wand_intro

theorem sepIntro {leftContext rightContext : Bunch Loc Val}
    {left right : IProp Loc Val} :
    Valid leftContext left -> Valid rightContext right ->
    Valid (.multiplicative leftContext rightContext) (IProp.sep left right) := by
  exact IProp.sep_mono

theorem sepIntroSwap {leftContext rightContext : Bunch Loc Val}
    {left right : IProp Loc Val} :
    Valid rightContext left -> Valid leftContext right ->
    Valid (.multiplicative leftContext rightContext) (IProp.sep left right) := by
  intro leftValid rightValid
  exact IProp.entails_trans
    (IProp.sep_comm leftContext.denote rightContext.denote)
    (IProp.sep_mono leftValid rightValid)

theorem impApply {implicationName premiseName : String} {premise conclusion : IProp Loc Val} :
    Valid (.additive (.hyp implicationName (IProp.imp premise conclusion))
      (.hyp premiseName premise)) conclusion :=
  IProp.imp_elim premise conclusion

theorem impApplySwap {premiseName implicationName : String} {premise conclusion : IProp Loc Val} :
    Valid (.additive (.hyp premiseName premise)
      (.hyp implicationName (IProp.imp premise conclusion))) conclusion := by
  intro heap step holds
  apply IProp.imp_elim premise conclusion heap step
  exact ⟨holds.2, holds.1⟩

theorem wandApply {wandName premiseName : String} {premise conclusion : IProp Loc Val} :
    Valid (.multiplicative (.hyp wandName (IProp.wand premise conclusion))
      (.hyp premiseName premise)) conclusion :=
  IProp.wand_elim premise conclusion

theorem wandApplySwap {premiseName wandName : String} {premise conclusion : IProp Loc Val} :
    Valid (.multiplicative (.hyp premiseName premise)
      (.hyp wandName (IProp.wand premise conclusion))) conclusion := by
  exact IProp.entails_trans
    (IProp.sep_comm premise (IProp.wand premise conclusion))
    (IProp.wand_elim premise conclusion)

theorem truthIntro {context : Bunch Loc Val} : Valid context IProp.truth :=
  IProp.truth_intro context.denote

theorem falsumElim (name : String) {context : Bunch Loc Val} {goal : IProp Loc Val}
    (found : context.lookup name = some IProp.falsum) : Valid context goal :=
  IProp.entails_trans (Bunch.lookup_sound found) (IProp.falsum_elim goal)

theorem eqRefl {context : Bunch Loc Val} {ty : Ty}
    {term : Ty.denote Loc Val ty} :
    Valid context (IProp.equal (Ty.EquivAt Loc Val ty)
      (Ty.equivAt_mono Loc Val ty) term term) := by
  exact IProp.entails_trans (IProp.truth_intro context.denote)
    (IProp.equal_refl (Ty.EquivAt Loc Val ty) (Ty.equivAt_mono Loc Val ty)
      (fun step value => Ty.equivAt_refl Loc Val ty value) term)

theorem existsIntro {Witness : Type w} {context : Bunch Loc Val}
    {body : Witness -> IProp Loc Val} (witness : Witness) :
    Valid context (body witness) -> Valid context (IProp.exists_ body) := by
  intro valid
  exact IProp.entails_trans valid (IProp.exists_intro body witness)

theorem existsElim (source witnessName : String) {Witness : Type w}
    {body : Witness -> IProp Loc Val} {goal : IProp Loc Val} :
    (forall witness, Valid (.hyp witnessName (body witness)) goal) ->
    Valid (.hyp source (IProp.exists_ body)) goal := by
  exact IProp.exists_elim

theorem forallIntro {Witness : Type w} {context : Bunch Loc Val}
    {body : Witness -> IProp Loc Val} :
    (forall witness, Valid context (body witness)) ->
    Valid context (IProp.forall_ body) := by
  exact IProp.forall_intro

theorem forallElim (source specializedName : String) {Witness : Type w}
    (witness : Witness) {context updated : Bunch Loc Val}
    {body : Witness -> IProp Loc Val} {goal : IProp Loc Val}
    (replaced : Bunch.replace source (.hyp specializedName (body witness)) context =
      some (IProp.forall_ body, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Bunch.replace_sound replaced (IProp.forall_elim body witness)) valid

theorem alwaysIntro {goal : IProp Loc Val} :
    Valid .empty goal -> Valid .empty (IProp.always goal) := by
  exact IProp.always_intro_from_truth

theorem alwaysElim (source name : String) {context updated : Bunch Loc Val}
    {proposition goal : IProp Loc Val}
    (replaced : Bunch.replace source (.hyp name proposition) context =
      some (IProp.always proposition, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Bunch.replace_sound replaced (IProp.always_elim proposition)) valid

theorem alwaysDup (source leftName rightName : String)
    {context updated : Bunch Loc Val} {proposition goal : IProp Loc Val}
    (replaced : Bunch.replace source
      (.multiplicative (.hyp leftName (IProp.always proposition))
        (.hyp rightName (IProp.always proposition))) context =
      some (IProp.always proposition, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Bunch.replace_sound replaced (IProp.always_dup proposition)) valid

theorem clear (name : String) {context updated : Bunch Loc Val}
    {source goal : IProp Loc Val}
    (replaced : Bunch.replace name .empty context = some (source, updated)) :
    Valid updated goal -> Valid context goal := by
  intro valid
  exact IProp.entails_trans
    (Bunch.replace_sound replaced (IProp.truth_intro source)) valid

theorem frame (name : String) {context remaining : Bunch Loc Val}
    {framed goal : IProp Loc Val}
    (extracted : Bunch.extract name context = some (framed, remaining)) :
    Valid remaining goal -> Valid context (IProp.sep framed goal) := by
  intro valid
  exact IProp.entails_trans (Bunch.extract_sound extracted)
    (IProp.sep_mono (IProp.entails_refl framed) valid)

theorem frameMany (names : List String) {context remaining : Bunch Loc Val}
    {framed goal : IProp Loc Val}
    (extracted : Bunch.extractMany names context = some (framed, remaining)) :
    Valid remaining goal -> Valid context (IProp.sep framed goal) := by
  intro valid
  exact IProp.entails_trans (Bunch.extractMany_sound extracted)
    (IProp.sep_mono (IProp.entails_refl framed) valid)

theorem stop {context : Bunch Loc Val} {goal : IProp Loc Val} :
    Valid context goal -> IProp.Entails context.denote goal := by
  intro valid
  exact valid

theorem laterIntro {context : Bunch Loc Val} {goal : IProp Loc Val} :
    Valid context goal -> Valid context (IProp.later goal) := by
  intro valid
  exact IProp.entails_trans valid (IProp.later_intro goal)

theorem laterMono (source name : String) {premise goal : IProp Loc Val} :
    Valid (.hyp name premise) goal ->
    Valid (.hyp source (IProp.later premise)) (IProp.later goal) := by
  intro valid
  exact IProp.later_mono valid

end MPSL.ProofMode
