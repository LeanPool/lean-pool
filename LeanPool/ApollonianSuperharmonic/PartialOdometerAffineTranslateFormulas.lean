/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslate
public import LeanPool.ApollonianSuperharmonic.PartialOdometer
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSquares
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import LeanPool.ApollonianSuperharmonic.GaussianTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: PartialOdometerAffineTranslateFormulas]

/-!
# PartialOdometerAffineTranslateFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PartialTranslationLemmas

private theorem membership :
    ∀ (h : PartialOdometer), ∀ (u : GaussianInt), ∀ (x : GaussianInt), x ∈ h.domain.image
        (GaussianTranslation u) ↔ x - u ∈ h.domain := by
  classical
  intro h u x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    simpa [GaussianTranslation, add_comm, add_left_comm, add_assoc] using hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x - u, hx, ?_⟩
    simp [GaussianTranslation, add_comm]

private theorem setImage :
    ∀ (h : PartialOdometer), ∀ (u : GaussianInt), ((h.domain.image (GaussianTranslation u) :
        Finset GaussianInt) : Set GaussianInt) =
        GaussianTranslation u '' (h.domain : Set GaussianInt) := by
  classical
  intro h u
  ext x
  constructor
  · intro hx
    change x ∈ h.domain.image (GaussianTranslation u) at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  · rintro ⟨y, hy, rfl⟩
    change GaussianTranslation u y ∈ h.domain.image (GaussianTranslation u)
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

end PartialTranslationLemmas

namespace PartialTranslationSquares

private theorem translatedSquares :
    ∀ (h : PartialOdometer), ∀ (u : GaussianInt), ∀ (a : GaussianInt), ∀ (b : ℤ),
        PartialOdometerSquares
          ({ domain := h.domain.image (GaussianTranslation u)
             value := fun x =>
               if x ∈ h.domain.image (GaussianTranslation u) then
                 h.value (x - u) + a.re * x.re + a.im * x.im + b
               else 0
             value_outside := by
               intro x hx
               simp [hx] } : PartialOdometer) =
        (PartialOdometerSquares h).image (GaussianTranslation u) := by
  classical
  intro h u a b
  simp only [PartialOdometerSquares, Finset.filter_image]
  congr 1
  ext x
  simp [GaussianTranslation, add_assoc, add_comm]

end PartialTranslationSquares

theorem PartialOdometerAffineTranslateFormulas
    (h : PartialOdometer) (u a : GaussianInt) (b : ℤ) :
    (PartialOdometerAffineTranslate h u a b).domain =
        h.domain.image (GaussianTranslation u) ∧
    (∀ x, x ∈ (PartialOdometerAffineTranslate h u a b).domain ↔
      x - u ∈ h.domain) ∧
    (∀ x, x ∈ (PartialOdometerAffineTranslate h u a b).domain →
      (PartialOdometerAffineTranslate h u a b).value x =
        h.value (x - u) + a.re * x.re + a.im * x.im + b) ∧
    (((PartialOdometerAffineTranslate h u a b).domain : Set GaussianInt) =
      GaussianTranslation u '' (h.domain : Set GaussianInt)) ∧
    (∀ T : ProtoTile,
      ((h.domain : Set GaussianInt) = FootprintVertices T) →
      (((PartialOdometerAffineTranslate h u a b).domain : Set GaussianInt) =
        FootprintVertices (TileTranslation T u))) ∧
    PartialOdometerSlope (PartialOdometerAffineTranslate h u a b) =
      (PartialOdometerSlope h).map
        (fun p => (p.1 + (a.re : ℝ), p.2 + (a.im : ℝ))) := by
-- BODY
  classical
  unfold PartialOdometerAffineTranslate
  have membership (x : GaussianInt) :
      x ∈ h.domain.image (GaussianTranslation u) ↔ x - u ∈ h.domain :=
          PartialTranslationLemmas.membership h u x
  have setImage :
      ((h.domain.image (GaussianTranslation u) : Finset GaussianInt) : Set GaussianInt) =
        GaussianTranslation u '' (h.domain : Set GaussianInt) :=
            PartialTranslationLemmas.setImage h u
  refine ⟨rfl, ?_, ?_, setImage, ?_, ?_⟩
  · intro x
    exact membership x
  · intro x hx
    change x ∈ h.domain.image (GaussianTranslation u) at hx
    have hxu := (membership x).mp hx
    simp [hx]
  · intro T hT
    rw [setImage, hT]
    rw [← (TileTranslationFormulas T u).2.2.2.2.2.1]
  · change PartialOdometerSlope
        ({ domain := h.domain.image (GaussianTranslation u)
           value := fun x =>
             if x ∈ h.domain.image (GaussianTranslation u) then
               h.value (x - u) + a.re * x.re + a.im * x.im + b
             else 0
           value_outside := by
             intro x hx
             simp [hx] } : PartialOdometer) = _
    have translatedSquares := PartialTranslationSquares.translatedSquares h u a b
    have valueFormula (z : GaussianInt) (hz : z ∈ h.domain) :
        (if GaussianTranslation u z ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u z - u) + a.re * (GaussianTranslation u z).re +
            a.im * (GaussianTranslation u z).im + b
        else 0) =
          h.value z + a.re * (GaussianTranslation u z).re +
            a.im * (GaussianTranslation u z).im + b := by
      have hz' : GaussianTranslation u z - u ∈ h.domain := by
        simpa [GaussianTranslation, add_assoc, add_comm, add_left_comm] using hz
      rw [ite_eq_left ((membership _).mpr hz')]
      simp [GaussianTranslation, add_comm, add_left_comm]
    have reAdd (x y : GaussianInt) :
        ((x + y).re : ℝ) = (x.re : ℝ) + (y.re : ℝ) := by
      cases x; cases y; simp
    have imAdd (x y : GaussianInt) :
        ((x + y).im : ℝ) = (x.im : ℝ) + (y.im : ℝ) := by
      cases x; cases y; simp
    have reInt (x y : GaussianInt) : (x + y).re = x.re + y.re := by
      cases x; cases y; rfl
    have imInt (x y : GaussianInt) : (x + y).im = x.im + y.im := by
      cases x; cases y; rfl
    have horizontal (x : GaussianInt) (hx : x ∈ PartialOdometerSquares h) :
        (((if GaussianTranslation u (x + 1) ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u (x + 1) - u) + a.re * (GaussianTranslation u (x + 1)).re +
            a.im * (GaussianTranslation u (x + 1)).im + b else 0) -
          (if GaussianTranslation u x ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u x - u) + a.re * (GaussianTranslation u x).re +
            a.im * (GaussianTranslation u x).im + b else 0) +
          (if GaussianTranslation u (x + 1 + ⟨0, 1⟩) ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u (x + 1 + ⟨0, 1⟩) - u) + a.re * (GaussianTranslation u (x
              + 1 + ⟨0, 1⟩)).re +
            a.im * (GaussianTranslation u (x + 1 + ⟨0, 1⟩)).im + b else 0) -
          (if GaussianTranslation u (x + ⟨0, 1⟩) ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u (x + ⟨0, 1⟩) - u) + a.re * (GaussianTranslation u (x +
              ⟨0, 1⟩)).re +
            a.im * (GaussianTranslation u (x + ⟨0, 1⟩)).im + b else 0) : ℤ) : ℝ) =
          ((h.value (x + 1) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
            h.value (x + ⟨0, 1⟩) : ℤ) : ℝ) + 2 * (a.re : ℝ) := by
      have hx0 := (Finset.mem_filter.mp hx).1
      have hx1 := (Finset.mem_filter.mp hx).2.1
      have hxi := (Finset.mem_filter.mp hx).2.2.1
      have hx1i := (Finset.mem_filter.mp hx).2.2.2
      rw [valueFormula (x + 1) hx1, valueFormula x hx0,
        valueFormula (x + 1 + ⟨0, 1⟩) hx1i, valueFormula (x + ⟨0, 1⟩) hxi]
      simp [GaussianTranslation, reInt, imInt]
      ring
    have vertical (x : GaussianInt) (hx : x ∈ PartialOdometerSquares h) :
        (((if GaussianTranslation u (x + ⟨0, 1⟩) ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u (x + ⟨0, 1⟩) - u) + a.re * (GaussianTranslation u (x +
              ⟨0, 1⟩)).re +
            a.im * (GaussianTranslation u (x + ⟨0, 1⟩)).im + b else 0) -
          (if GaussianTranslation u x ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u x - u) + a.re * (GaussianTranslation u x).re +
            a.im * (GaussianTranslation u x).im + b else 0) +
          (if GaussianTranslation u (x + 1 + ⟨0, 1⟩) ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u (x + 1 + ⟨0, 1⟩) - u) + a.re * (GaussianTranslation u (x
              + 1 + ⟨0, 1⟩)).re +
            a.im * (GaussianTranslation u (x + 1 + ⟨0, 1⟩)).im + b else 0) -
          (if GaussianTranslation u (x + 1) ∈ h.domain.image (GaussianTranslation u) then
          h.value (GaussianTranslation u (x + 1) - u) + a.re * (GaussianTranslation u (x + 1)).re +
            a.im * (GaussianTranslation u (x + 1)).im + b else 0) : ℤ) : ℝ) =
          ((h.value (x + ⟨0, 1⟩) - h.value x + h.value (x + 1 + ⟨0, 1⟩) -
            h.value (x + 1) : ℤ) : ℝ) + 2 * (a.im : ℝ) := by
      have hx0 := (Finset.mem_filter.mp hx).1
      have hx1 := (Finset.mem_filter.mp hx).2.1
      have hxi := (Finset.mem_filter.mp hx).2.2.1
      have hx1i := (Finset.mem_filter.mp hx).2.2.2
      rw [valueFormula (x + ⟨0, 1⟩) hxi, valueFormula x hx0,
        valueFormula (x + 1 + ⟨0, 1⟩) hx1i, valueFormula (x + 1) hx1]
      simp [GaussianTranslation, reInt, imInt]
      ring
    simp only [PartialOdometerSlope]
    rw [translatedSquares]
    have injectiveTranslation : Function.Injective (GaussianTranslation u) := by
      intro x y hxy
      exact add_right_cancel hxy
    by_cases hs : (PartialOdometerSquares h).Nonempty
    · have hsi : (Finset.image (GaussianTranslation u) (PartialOdometerSquares h)).Nonempty :=
        hs.image _
      simp only [hsi, hs, ↓reduceIte, Option.map_some]
      rw [Finset.card_image_of_injective _ injectiveTranslation]
      rw [Finset.sum_image]
      all_goals try exact injectiveTranslation.injOn
      rw [Finset.sum_image]
      all_goals try exact injectiveTranslation.injOn
      congr 1
      · congr 2
        · have cardPositive : (PartialOdometerSquares h).card > 0 := hs.card_pos
          have cardReal : ((PartialOdometerSquares h).card : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt cardPositive)
          field_simp [cardReal]
          have constSum :
              (∑ _x ∈ PartialOdometerSquares h, 2 * (a.re : ℝ)) =
                2 * (PartialOdometerSquares h).card * (a.re : ℝ) := by
            rw [Finset.sum_const]
            simp
            ring
          rw [← constSum]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          have hx0 := (Finset.mem_filter.mp hx).1
          have hx1 := (Finset.mem_filter.mp hx).2.1
          have hxi := (Finset.mem_filter.mp hx).2.2.1
          have hx1i := (Finset.mem_filter.mp hx).2.2.2
          have h0' := (membership (GaussianTranslation u x)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hx0)
          have h1' := (membership (GaussianTranslation u x + 1)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hx1)
          have hi' := (membership (GaussianTranslation u x + ⟨0, 1⟩)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hxi)
          have h1i' := (membership (GaussianTranslation u x + 1 + ⟨0, 1⟩)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hx1i)
          rw [ite_eq_left h1', ite_eq_left h0', ite_eq_left h1i', ite_eq_left hi']
          have c0 : GaussianTranslation u x - u = x := by change x + u - u = x; abel
          have c1 : GaussianTranslation u x + 1 - u = x + 1 := by change x + u + 1 - u = x + 1; abel
          have ci : GaussianTranslation u x + ⟨0, 1⟩ - u = x + ⟨0, 1⟩ := by
            change x + u + ⟨0, 1⟩ - u = x + ⟨0, 1⟩
            abel
          have c1i : GaussianTranslation u x + 1 + ⟨0, 1⟩ - u = x + 1 + ⟨0, 1⟩ := by
            change x + u + 1 + ⟨0, 1⟩ - u = x + 1 + ⟨0, 1⟩
            abel
          rw [c1, c0, c1i, ci]
          simp [reInt, imInt]
          ring
        · have cardPositive : (PartialOdometerSquares h).card > 0 := hs.card_pos
          have cardReal : ((PartialOdometerSquares h).card : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt cardPositive)
          field_simp [cardReal]
          have constSum :
              (∑ _x ∈ PartialOdometerSquares h, 2 * (a.im : ℝ)) =
                2 * (PartialOdometerSquares h).card * (a.im : ℝ) := by
            rw [Finset.sum_const]
            simp
            ring
          rw [← constSum]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          have hx0 := (Finset.mem_filter.mp hx).1
          have hx1 := (Finset.mem_filter.mp hx).2.1
          have hxi := (Finset.mem_filter.mp hx).2.2.1
          have hx1i := (Finset.mem_filter.mp hx).2.2.2
          have h0' := (membership (GaussianTranslation u x)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hx0)
          have h1' := (membership (GaussianTranslation u x + 1)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hx1)
          have hi' := (membership (GaussianTranslation u x + ⟨0, 1⟩)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hxi)
          have h1i' := (membership (GaussianTranslation u x + 1 + ⟨0, 1⟩)).mpr (by
            simpa [GaussianTranslation, add_assoc, add_comm] using hx1i)
          rw [ite_eq_left hi', ite_eq_left h0', ite_eq_left h1i', ite_eq_left h1']
          have c0 : GaussianTranslation u x - u = x := by change x + u - u = x; abel
          have c1 : GaussianTranslation u x + 1 - u = x + 1 := by change x + u + 1 - u = x + 1; abel
          have ci : GaussianTranslation u x + ⟨0, 1⟩ - u = x + ⟨0, 1⟩ := by
            change x + u + ⟨0, 1⟩ - u = x + ⟨0, 1⟩
            abel
          have c1i : GaussianTranslation u x + 1 + ⟨0, 1⟩ - u = x + 1 + ⟨0, 1⟩ := by
            change x + u + 1 + ⟨0, 1⟩ - u = x + 1 + ⟨0, 1⟩
            abel
          rw [ci, c0, c1i, c1]
          simp [reInt, imInt]
          ring
    · simp [hs]

end ApollonianSuperharmonic

end
