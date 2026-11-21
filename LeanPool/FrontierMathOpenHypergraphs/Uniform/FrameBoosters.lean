/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.FrontierMathOpenHypergraphs.Uniform.FrameDefs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Booster-frame validations

A support contributes exactly when one of its indices lies outside the capacity mask.
The kernel counts these indices directly in the raw support lists.
The largest booster has separate certificates for the two halves of its mask space.
-/

@[expose] public section

namespace HypergraphLowerBound

private def countRawComplementWitnesses (spec : FrameSpec) (mask : ℕ) : ℕ :=
  spec.rawSupports.countP fun support =>
    decide (support.countP (fun i => !(mask.testBit i)) = 1)

private theorem countSupportComplement_eq_card (spec : FrameSpec) (mask : ℕ)
    {support : List ℕ} (hsupport : support ∈ spec.rawSupports) :
    support.countP (fun i => !(mask.testBit i)) =
      ((supportPatternOfList support (spec.rawSupports_ok support hsupport).2.1
        (spec.rawSupports_ok support hsupport).1
        (spec.rawSupports_ok support hsupport).2.2).1 ∩ (maskFinset spec mask)ᶜ).card := by
  obtain ⟨distinct, inBounds, _⟩ := spec.rawSupports_ok support hsupport
  let indices := support.pmap (fun i hi => (⟨i, hi⟩ : Fin spec.t)) inBounds
  have indicesDistinct : indices.Nodup :=
    distinct.pmap fun _ _ _ _ eq => congrArg Fin.val eq
  have outsideMask (i : Fin spec.t) :
      decide (i ∈ (maskFinset spec mask)ᶜ) = !(mask.testBit i.val) := by
    simp [maskFinset]
  change _ = (indices.toFinset ∩ (maskFinset spec mask)ᶜ).card
  rw [← Finset.filter_mem_eq_inter, indicesDistinct.card_eq_countP]
  simp_rw [outsideMask]
  symm
  refine (List.countP_pmap (g := fun i hi => (⟨i, hi⟩ : Fin spec.t))
    (f := fun i => !(mask.testBit i.val)) inBounds).trans ?_
  calc
    _ = support.attach.countP (fun i => !(mask.testBit i.val)) := by
      apply List.countP_congr
      rintro ⟨i, hi⟩ _
      rfl
    _ = _ := List.countP_attach (l := support) (p := fun i => !(mask.testBit i))

private theorem countRawComplementWitnesses_eq (spec : FrameSpec) (mask : ℕ) :
    countRawComplementWitnesses spec mask =
      spec.countWitnesses Finset.univ (maskFinset spec mask)ᶜ := by
  unfold countRawComplementWitnesses FrameSpec.countWitnesses FrameSpec.supportList
  rw [List.countP_pmap, ← List.countP_attach (l := spec.rawSupports)]
  apply List.countP_congr
  rintro ⟨support, hsupport⟩ _
  have equalCount := countSupportComplement_eq_card spec mask hsupport
  constructor
  · intro witness
    exact decide_eq_true ⟨Finset.subset_univ _, equalCount ▸ of_decide_eq_true witness⟩
  · intro witness
    exact decide_eq_true (equalCount.symm ▸ (of_decide_eq_true witness).2)

private def checkRawComplementsDown (spec : FrameSpec) : ℕ → ℕ → Bool
  | 0, mask =>
    decide (countRawComplementWitnesses spec mask ≤ (maskFinset spec mask).sum spec.cap)
  | n + 1, mask =>
    checkRawComplementsDown spec n mask &&
      checkRawComplementsDown spec n (mask ||| ((1 : ℕ) <<< n))

private theorem checkRawComplementsDown_eq (spec : FrameSpec) (n mask : ℕ) :
    checkRawComplementsDown spec n mask = checkComplementMasksDown spec n mask := by
  induction n generalizing mask with
  | zero =>
    simp only [checkRawComplementsDown, checkComplementMasksDown, countRawComplementWitnesses_eq]
  | succ n ih =>
    simp only [checkRawComplementsDown, checkComplementMasksDown, ih]

-- Preserve the auxiliary certificate declarations from the original kernel decisions.
private theorem booster_0_valid._proof_1_1 :
    (boosters.get ⟨0, by decide⟩).checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_0_valid :
    (boosters.get ⟨0, by decide⟩).IsValid := by
  exact (boosters.get ⟨0, by decide⟩).checkComplementValid_sound booster_0_valid._proof_1_1

private theorem booster_1_valid._proof_1_1 :
    (boosters.get ⟨1, by decide⟩).checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_1_valid :
    (boosters.get ⟨1, by decide⟩).IsValid := by
  exact (boosters.get ⟨1, by decide⟩).checkComplementValid_sound booster_1_valid._proof_1_1

private theorem booster_2_valid._proof_1_1 :
    (boosters.get ⟨2, by decide⟩).checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_2_valid :
    (boosters.get ⟨2, by decide⟩).IsValid := by
  exact (boosters.get ⟨2, by decide⟩).checkComplementValid_sound booster_2_valid._proof_1_1

private theorem booster_3_valid._proof_1_1 :
    (boosters.get ⟨3, by decide⟩).checkComplementValid = true := by
  unfold FrameSpec.checkComplementValid
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_3_valid :
    (boosters.get ⟨3, by decide⟩).IsValid := by
  exact (boosters.get ⟨3, by decide⟩).checkComplementValid_sound booster_3_valid._proof_1_1

private theorem booster_4_valid._proof_1_1 :
    checkComplementMasksDown (boosters.get ⟨4, by decide⟩) 7 0 = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_4_valid._proof_1_2 :
    checkComplementMasksDown (boosters.get ⟨4, by decide⟩) 7 (0 ||| ((1 : ℕ) <<< 7)) = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_4_valid :
    (boosters.get ⟨4, by decide⟩).IsValid := by
  apply (boosters.get ⟨4, by decide⟩).checkComplementValid_sound
  change checkComplementMasksDown _ 8 0 = true
  exact checkComplementMasksDown_step_true _ 7 0
    booster_4_valid._proof_1_1 booster_4_valid._proof_1_2

private theorem booster_5_valid._proof_1_1 :
    checkComplementMasksDown (boosters.get ⟨5, by decide⟩) 7 0 = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_5_valid._proof_1_2 :
    checkComplementMasksDown (boosters.get ⟨5, by decide⟩) 7 (0 ||| ((1 : ℕ) <<< 7)) = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_5_valid :
    (boosters.get ⟨5, by decide⟩).IsValid := by
  apply (boosters.get ⟨5, by decide⟩).checkComplementValid_sound
  change checkComplementMasksDown _ 8 0 = true
  exact checkComplementMasksDown_step_true _ 7 0
    booster_5_valid._proof_1_1 booster_5_valid._proof_1_2

private def booster6Spec : FrameSpec :=
  boosters.get ⟨6, by decide⟩

private theorem booster_6_check_0._proof_1_1 :
    checkComplementMasksDown booster6Spec 7 0 = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_6_check_0._proof_1_2 :
    checkComplementMasksDown booster6Spec 7 (0 ||| ((1 : ℕ) <<< 7)) = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_6_check_0 :
    checkComplementMasksDown booster6Spec 8 0 = true :=
  checkComplementMasksDown_step_true booster6Spec 7 0
    booster_6_check_0._proof_1_1 booster_6_check_0._proof_1_2

private theorem booster_6_check_1._proof_1_1 :
    checkComplementMasksDown booster6Spec 7 ((1 : ℕ) <<< 8) = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_6_check_1._proof_1_2 :
    checkComplementMasksDown booster6Spec 7 (((1 : ℕ) <<< 8) ||| ((1 : ℕ) <<< 7)) = true := by
  rw [← checkRawComplementsDown_eq]
  decide +kernel

private theorem booster_6_check_1 :
    checkComplementMasksDown booster6Spec 8 ((1 : ℕ) <<< 8) = true :=
  checkComplementMasksDown_step_true booster6Spec 7 ((1 : ℕ) <<< 8)
    booster_6_check_1._proof_1_1 booster_6_check_1._proof_1_2

private theorem booster_6_valid :
    (boosters.get ⟨6, by decide⟩).IsValid := by
  apply booster6Spec.checkComplementValid_sound
  exact checkComplementMasksDown_step_true booster6Spec 8 0
    booster_6_check_0 booster_6_check_1

theorem boosters_valid :
    ∀ spec ∈ boosters, spec.IsValid := by
  intro spec hs
  obtain ⟨i, rfl⟩ := List.get_of_mem hs
  fin_cases i
  · exact booster_0_valid
  · exact booster_1_valid
  · exact booster_2_valid
  · exact booster_3_valid
  · exact booster_4_valid
  · exact booster_5_valid
  · exact booster_6_valid

end HypergraphLowerBound
