/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellAverage
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Gaussian averaging box geometry

The local energy cylinder and the Gaussian averaging box occupy a
bounded region of the extended normalized half-space.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The local energy cylinder is contained in the Gaussian averaging
box at the same center and time (`lem:bu-small-time`). -/
theorem bu_short_inner_subset_average
    (Y : Vec3) (δ : ℝ) (hδ : 0 < δ) :
    let r := Real.sqrt δ / 8
    spaceTimeSet (vec3Ball Y r)
      (Ioo (1 / 2 + δ - r ^ 2 / 2)
        (1 / 2 + δ - r ^ 2 / 2 + r ^ 2)) ⊆
      spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)) := by
  dsimp
  let r := Real.sqrt δ / 8
  have hr : 0 < r := by dsimp [r]; positivity
  intro z hz
  have hxOuter : z.1 ∈ vec3Ball Y (2 * r) :=
    (vec3Ball_mono (by linarith only [hr] : r ≤ 2 * r)) hz.1
  have htlo : 1 / 2 + δ - r ^ 2 / 2 < z.2 := by
    simpa only [r] using hz.2.1
  have hthi : z.2 < 1 / 2 + δ - r ^ 2 / 2 + r ^ 2 := by
    simpa only [r] using hz.2.2
  have htOuter : z.2 - 1 / 2 ∈
      Ioo (δ - r ^ 2 / 2) (δ - r ^ 2 / 2 + 4 * r ^ 2) := by
    constructor
    · linarith only [htlo]
    · nlinarith only [hthi, sq_nonneg r]
  have hx := (bu_short_caccioppoli_outer_space_subset Y δ hδ) hxOuter
  have ht := (bu_short_caccioppoli_outer_time_subset δ hδ) htOuter
  exact ⟨hx,
    ⟨by linarith only [ht.1], by linarith only [ht.2]⟩⟩

/-- A Gaussian averaging box is bounded in parabolic space-time. -/
theorem bu_short_average_box_bounded
    (Y : Vec3) (δ : ℝ) (hδ : 0 < δ) :
    Bornology.IsBounded
      (spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
        (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))) := by
  let B : Set Vec3 := vec3Ball Y (Real.sqrt (3 * δ / 2))
  let K : Set ParabolicPoint := parabolicHomeomorph.symm ''
    (closure B ×ˢ Icc (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
  have hKcompact : IsCompact K := by
    exact ((isCompact_closure_vec3Ball (by positivity :
      0 < Real.sqrt (3 * δ / 2))).prod isCompact_Icc).image
        parabolicHomeomorph.symm.continuous
  apply hKcompact.isBounded.subset
  intro z hz
  refine ⟨(z.1, z.2), ⟨subset_closure hz.1, ?_⟩, ?_⟩
  · exact ⟨hz.2.1.le, hz.2.2.le⟩
  · apply parabolicHomeomorph.injective
    rw [parabolicHomeomorph.apply_symm_apply]
    rfl

/-- The Gaussian averaging box lies in the extended normalized
half-space when its center ball does. -/
theorem bu_short_average_box_subset_extended
    (Y : Vec3) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hball : vec3Ball Y (Real.sqrt (3 * δ / 2)) ⊆
      {x : Vec3 | 0 < x 2}) :
    spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)) ⊆
    spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) (3 / 2)) := by
  intro z hz
  refine ⟨hball hz.1, ?_⟩
  constructor
  · linarith only [hz.2.1, hδ]
  · linarith only [hz.2.2, hδhalf]

end ESS
