import MPSL.ProofMode.Bunch

set_option autoImplicit false

namespace MPSL.ProofMode

universe u v

variable {Loc : Type u} {Val : Type v} [DecidableEq Loc]

theorem start (name : String) {premise goal : Formula Loc Val} :
    Valid (.hyp name premise) goal -> premise ⊢ goal := by
  intro valid
  exact valid

theorem exactNamed {context : Bunch Loc Val} {found goal : Formula Loc Val}
    (name : String) (lookupFound : context.lookup name = some found)
    (sameDenotation : found.denote = goal.denote) : Valid context goal := by
  unfold Valid
  rw [← sameDenotation]
  exact Bunch.lookup_sound lookupFound

theorem exactAddLeft {left right : Bunch Loc Val} {goal : Formula Loc Val} :
    Valid left goal -> Valid (.additive left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.and_elim_left left.denote right.denote) valid

theorem exactAddRight {left right : Bunch Loc Val} {goal : Formula Loc Val} :
    Valid right goal -> Valid (.additive left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.and_elim_right left.denote right.denote) valid

theorem exactMulLeft {left right : Bunch Loc Val} {goal : Formula Loc Val} :
    Valid left goal -> Valid (.multiplicative left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.sep_elim_left left.denote right.denote) valid

theorem exactMulRight {left right : Bunch Loc Val} {goal : Formula Loc Val} :
    Valid right goal -> Valid (.multiplicative left right) goal := by
  intro valid
  exact IProp.entails_trans (IProp.sep_elim_right left.denote right.denote) valid

theorem andDestruct (source leftName rightName : String) {left right goal : Formula Loc Val} :
    Valid (.additive (.hyp leftName left) (.hyp rightName right)) goal ->
    Valid (.hyp source (.and left right)) goal := by
  intro valid
  exact valid

theorem sepDestruct (source leftName rightName : String) {left right goal : Formula Loc Val} :
    Valid (.multiplicative (.hyp leftName left) (.hyp rightName right)) goal ->
    Valid (.hyp source (.sep left right)) goal := by
  intro valid
  exact valid

theorem orDestruct (source leftName rightName : String) {left right goal : Formula Loc Val} :
    Valid (.hyp leftName left) goal -> Valid (.hyp rightName right) goal ->
    Valid (.hyp source (.or left right)) goal := by
  intro fromLeft fromRight
  exact IProp.or_elim fromLeft fromRight

theorem andIntro {context : Bunch Loc Val} {left right : Formula Loc Val} :
    Valid context left -> Valid context right ->
    Valid context (.and left right) := by
  exact IProp.and_intro

theorem orIntroLeft {context : Bunch Loc Val} {left right : Formula Loc Val} :
    Valid context left -> Valid context (.or left right) := by
  intro valid
  exact IProp.entails_trans valid (IProp.or_intro_left left.denote right.denote)

theorem orIntroRight {context : Bunch Loc Val} {left right : Formula Loc Val} :
    Valid context right -> Valid context (.or left right) := by
  intro valid
  exact IProp.entails_trans valid (IProp.or_intro_right left.denote right.denote)

theorem impIntro (name : String) {context : Bunch Loc Val} {premise conclusion : Formula Loc Val} :
    Valid (.additive context (.hyp name premise)) conclusion ->
    Valid context (.imp premise conclusion) := by
  exact IProp.imp_intro

theorem wandIntro (name : String) {context : Bunch Loc Val} {premise conclusion : Formula Loc Val} :
    Valid (.multiplicative context (.hyp name premise)) conclusion ->
    Valid context (.wand premise conclusion) := by
  exact IProp.wand_intro

theorem sepIntro {leftContext rightContext : Bunch Loc Val}
    {left right : Formula Loc Val} :
    Valid leftContext left -> Valid rightContext right ->
    Valid (.multiplicative leftContext rightContext) (.sep left right) := by
  exact IProp.sep_mono

theorem sepIntroSwap {leftContext rightContext : Bunch Loc Val}
    {left right : Formula Loc Val} :
    Valid rightContext left -> Valid leftContext right ->
    Valid (.multiplicative leftContext rightContext) (.sep left right) := by
  intro leftValid rightValid
  exact IProp.entails_trans
    (IProp.sep_comm leftContext.denote rightContext.denote)
    (IProp.sep_mono leftValid rightValid)

theorem impApply {implicationName premiseName : String} {premise conclusion : Formula Loc Val} :
    Valid (.additive (.hyp implicationName (.imp premise conclusion))
      (.hyp premiseName premise)) conclusion :=
  IProp.imp_elim premise.denote conclusion.denote

theorem impApplySwap {premiseName implicationName : String} {premise conclusion : Formula Loc Val} :
    Valid (.additive (.hyp premiseName premise)
      (.hyp implicationName (.imp premise conclusion))) conclusion := by
  intro heap step holds
  apply IProp.imp_elim premise.denote conclusion.denote heap step
  exact ⟨holds.2, holds.1⟩

theorem wandApply {wandName premiseName : String} {premise conclusion : Formula Loc Val} :
    Valid (.multiplicative (.hyp wandName (.wand premise conclusion))
      (.hyp premiseName premise)) conclusion :=
  IProp.wand_elim premise.denote conclusion.denote

theorem wandApplySwap {premiseName wandName : String} {premise conclusion : Formula Loc Val} :
    Valid (.multiplicative (.hyp premiseName premise)
      (.hyp wandName (.wand premise conclusion))) conclusion := by
  exact IProp.entails_trans
    (IProp.sep_comm premise.denote (IProp.wand premise.denote conclusion.denote))
    (IProp.wand_elim premise.denote conclusion.denote)

end MPSL.ProofMode
