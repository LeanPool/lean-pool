/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PartialOdometerHalfTurn
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope

-- [TABLET NODE: PartialOdometerHalfTurnFormulas]

/-!
# PartialOdometerHalfTurnFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PartialOdometerHalfTurnFormulas (h : PartialOdometer) :
    (∀ x, x ∈ (PartialOdometerHalfTurn h).domain ↔ -x ∈ h.domain) ∧
    (∀ x, x ∈ (PartialOdometerHalfTurn h).domain →
      (PartialOdometerHalfTurn h).value x = h.value (-x)) ∧
    PartialOdometerSquares (PartialOdometerHalfTurn h) =
      (PartialOdometerSquares h).image (fun x => -x - 1 - ⟨0, 1⟩) ∧
    (PartialOdometerSquares (PartialOdometerHalfTurn h)).card =
      (PartialOdometerSquares h).card ∧
    (∑ y ∈ PartialOdometerSquares (PartialOdometerHalfTurn h),
        ((PartialOdometerHalfTurn h).value (y + 1) -
          (PartialOdometerHalfTurn h).value y +
          (PartialOdometerHalfTurn h).value (y + 1 + ⟨0, 1⟩) -
          (PartialOdometerHalfTurn h).value (y + ⟨0, 1⟩) : ℤ)) =
      -(∑ x ∈ PartialOdometerSquares h,
        (h.value (x + 1) - h.value x +
          h.value (x + 1 + ⟨0, 1⟩) - h.value (x + ⟨0, 1⟩) : ℤ)) ∧
    (∑ y ∈ PartialOdometerSquares (PartialOdometerHalfTurn h),
        ((PartialOdometerHalfTurn h).value (y + ⟨0, 1⟩) -
          (PartialOdometerHalfTurn h).value y +
          (PartialOdometerHalfTurn h).value (y + 1 + ⟨0, 1⟩) -
          (PartialOdometerHalfTurn h).value (y + 1) : ℤ)) =
      -(∑ x ∈ PartialOdometerSquares h,
        (h.value (x + ⟨0, 1⟩) - h.value x +
          h.value (x + 1 + ⟨0, 1⟩) - h.value (x + 1) : ℤ)) ∧
    PartialOdometerSlope (PartialOdometerHalfTurn h) =
      (PartialOdometerSlope h).map (fun p => (-p.1, -p.2)) := by
-- BODY
  classical
  unfold PartialOdometerHalfTurn
  have membership (x : GaussianInt) :
      x ∈ h.domain.image (fun z => -z) ↔ -x ∈ h.domain := by
    constructor
    · intro hx
      change x ∈ h.domain.image (fun z => -z) at hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, heq⟩
      rw [← heq]
      simpa using hz
    · intro hx
      exact Finset.mem_image.mpr ⟨-x, hx, by simp⟩
  have valueFormula (x : GaussianInt)
      (hx : x ∈ h.domain.image (fun z => -z)) :
      (if -x ∈ h.domain then h.value (-x) else 0) = h.value (-x) := by
    rw [ite_eq_left ((membership x).mp hx)]
  have squaresImage :
      PartialOdometerSquares
          ({ domain := h.domain.image (fun z => -z)
             value := fun x => if -x ∈ h.domain then h.value (-x) else 0
             value_outside := by
               intro x hx
               rw [ite_eq_right]
               intro hm
               exact hx ((membership x).mpr hm) } : PartialOdometer) =
        (PartialOdometerSquares h).image (fun x => -x - 1 - ⟨0, 1⟩) := by
    simp only [PartialOdometerSquares]
    ext x
    constructor
    · intro hx
      change x ∈ (h.domain.image (fun z => -z)).filter _ at hx
      rcases Finset.mem_filter.mp hx with ⟨hxdom, hxc⟩
      rcases Finset.mem_image.mp hxdom with ⟨z, hz, heq⟩
      subst x
      have hz0' : z ∈ h.domain := hz
      have hz1' : z - 1 ∈ h.domain := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          (membership (-z + 1)).mp hxc.1
      have hzi' : z - ⟨0, 1⟩ ∈ h.domain := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          (membership (-z + ⟨0, 1⟩)).mp hxc.2.1
      have hz1i' : z - 1 - ⟨0, 1⟩ ∈ h.domain := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          (membership (-z + 1 + ⟨0, 1⟩)).mp hxc.2.2
      apply Finset.mem_image.mpr
      refine ⟨z - 1 - ⟨0, 1⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨hz1i', ?_, ?_, ?_⟩
        · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzi'
        · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz1'
        · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz0'
      · simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      simp only [Finset.mem_filter] at hz
      rcases hz with ⟨hz0, hz1, hzi, hz1i⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨z + 1 + ⟨0, 1⟩, ?_, ?_⟩, ?_⟩
      · exact hz1i
      · simp [sub_eq_add_neg, add_assoc, add_comm]
      refine ⟨?_, ?_, ?_⟩
      · apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzi
      · apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz1
      · apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact membership x
  · intro x hx
    exact valueFormula x hx
  · exact squaresImage
  · rw [squaresImage]
    apply Finset.card_image_of_injective
    intro x y hxy
    simpa using sub_left_injective hxy
  · rw [squaresImage]
    have injectiveMap : Function.Injective (fun x : GaussianInt => -x - 1 - ⟨0, 1⟩) := by
      intro x y hxy
      simpa using sub_left_injective hxy
    rw [Finset.sum_image]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 := (Finset.mem_filter.mp hx).1
      have hx1 := (Finset.mem_filter.mp hx).2.1
      have hxi := (Finset.mem_filter.mp hx).2.2.1
      have hx1i := (Finset.mem_filter.mp hx).2.2.2
      have hm0 : -x ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr; simpa using hx0
      have hm1 : -(x + 1) ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr; simpa using hx1
      have hmi : -(x + ⟨0, 1⟩) ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr; simpa using hxi
      have hm1i : -(x + 1 + ⟨0, 1⟩) ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr; simpa using hx1i
      have ha : -x - 1 - ⟨0, 1⟩ + 1 ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxi
      have hb : -x - 1 - ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx1i
      have hc : -x - 1 - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx0
      have hd : -x - 1 - ⟨0, 1⟩ + ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx1
      dsimp
      rw [valueFormula _ ha, valueFormula _ hb, valueFormula _ hc, valueFormula _ hd]
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    · exact injectiveMap.injOn
  · rw [squaresImage]
    have injectiveMap : Function.Injective (fun x : GaussianInt => -x - 1 - ⟨0, 1⟩) := by
      intro x y hxy
      simpa using sub_left_injective hxy
    rw [Finset.sum_image]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 := (Finset.mem_filter.mp hx).1
      have hx1 := (Finset.mem_filter.mp hx).2.1
      have hxi := (Finset.mem_filter.mp hx).2.2.1
      have hx1i := (Finset.mem_filter.mp hx).2.2.2
      have ha : -x - 1 - ⟨0, 1⟩ + 1 ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxi
      have hb : -x - 1 - ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx1i
      have hc : -x - 1 - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx0
      have hd : -x - 1 - ⟨0, 1⟩ + ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
        apply (membership _).mpr
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx1
      dsimp
      rw [valueFormula _ hd, valueFormula _ hb,
        valueFormula _ hc, valueFormula _ ha]
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    · exact injectiveMap.injOn
  · simp only [PartialOdometerSlope]
    rw [squaresImage]
    by_cases hs : (PartialOdometerSquares h).Nonempty
    · have hsi := hs.image (fun x : GaussianInt => -x - 1 - ⟨0, 1⟩)
      simp only [hs, hsi, ↓reduceIte, Option.map_some]
      have inj : Function.Injective (fun x : GaussianInt => -x - 1 - ⟨0, 1⟩) := by
        intro x y e
        simpa using sub_left_injective e
      rw [Finset.card_image_of_injective _ inj, Finset.sum_image, Finset.sum_image]
      all_goals try exact inj.injOn
      congr 1; congr 1
      all_goals
        have hc : ((PartialOdometerSquares h).card : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hs.card_pos)
        field_simp [hc]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 := (Finset.mem_filter.mp hx).1
        have hx1 := (Finset.mem_filter.mp hx).2.1
        have hxi := (Finset.mem_filter.mp hx).2.2.1
        have hx1i := (Finset.mem_filter.mp hx).2.2.2
        have ha : -x - 1 - ⟨0, 1⟩ + 1 ∈ h.domain.image (fun z => -z) := by
          apply (membership _).mpr
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxi
        have hb : -x - 1 - ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
          apply (membership _).mpr
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx1i
        have hc' : -x - 1 - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
          apply (membership _).mpr
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx0
        have hd : -x - 1 - ⟨0, 1⟩ + ⟨0, 1⟩ ∈ h.domain.image (fun z => -z) := by
          apply (membership _).mpr
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx1
        rw [valueFormula _ ha, valueFormula _ hb, valueFormula _ hc', valueFormula _ hd]
        rw [show -(-x - 1 - (⟨0, 1⟩ : GaussianInt) + 1) = x + ⟨0, 1⟩ by abel,
          show -(-x - 1 - (⟨0, 1⟩ : GaussianInt)) = x + 1 + ⟨0, 1⟩ by abel,
          show -(-x - 1 - (⟨0, 1⟩ : GaussianInt) + 1 + ⟨0, 1⟩) = x by abel,
          show -(-x - 1 - (⟨0, 1⟩ : GaussianInt) + ⟨0, 1⟩) = x + 1 by abel]
        push_cast
        ring
    · simp [hs]

end ApollonianSuperharmonic

end
