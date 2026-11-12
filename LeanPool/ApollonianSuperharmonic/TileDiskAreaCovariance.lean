/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TopologicalDisk

-- [TABLET NODE: TileDiskAreaCovariance]

/-!
# TileDiskAreaCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileDiskAreaCovariance : ∀ (T : ProtoTile) (u : GaussianInt),
    (LatticeTile T ↔ LatticeTile (TileTranslation T u)) ∧
    (LatticeTile T ↔ LatticeTile (TileQuarterTurn T)) ∧
    (LatticeTile T ↔ LatticeTile (TileReflection T)) ∧
    TileArea (TileTranslation T u) = TileArea T ∧
    TileArea (TileQuarterTurn T) = TileArea T ∧
    TileArea (TileReflection T) = TileArea T := by
-- BODY
  intro T u
  let translation : (Real × Real) ≃ₜ (Real × Real) :=
    (show (Real × Real) ≃ᵢ (Real × Real) from
      { toEquiv :=
          { toFun := fun p => (p.1 + (u.re : Real), p.2 + (u.im : Real))
            invFun := fun p => (p.1 - (u.re : Real), p.2 - (u.im : Real))
            left_inv := by intro p; ext <;> simp
            right_inv := by intro p; ext <;> simp }
        isometry_toFun := by
          apply Isometry.of_dist_eq
          intro p q
          simp [Prod.dist_eq, Real.dist_eq] })
        |>.toHomeomorph
  let quarter : (Real × Real) ≃ₜ (Real × Real) :=
    (show (Real × Real) ≃ᵢ (Real × Real) from
      { toEquiv :=
          { toFun := fun p => (-p.2, p.1)
            invFun := fun p => (p.2, -p.1)
            left_inv := by intro p; ext <;> simp
            right_inv := by intro p; ext <;> simp }
        isometry_toFun := by
          apply Isometry.of_dist_eq
          intro p q
          simp only [Prod.dist_eq, Real.dist_eq]
          rw [show -p.2 - -q.2 = -(p.2 - q.2) by ring, abs_neg]
          exact max_comm _ _ })
        |>.toHomeomorph
  let reflection : (Real × Real) ≃ₜ (Real × Real) :=
    (show (Real × Real) ≃ᵢ (Real × Real) from
      { toEquiv :=
          { toFun := fun p => (p.1, -p.2)
            invFun := fun p => (p.1, -p.2)
            left_inv := by intro p; ext <;> simp
            right_inv := by intro p; ext <;> simp }
        isometry_toFun := by
          apply Isometry.of_dist_eq
          intro p q
          simp only [Prod.dist_eq, Real.dist_eq]
          rw [show -p.2 - -q.2 = -(p.2 - q.2) by ring, abs_neg] })
        |>.toHomeomorph
  have disk_image : ∀ (S : Set (Real × Real)) (e : (Real × Real) ≃ₜ (Real × Real)),
      TopologicalDisk S ↔ TopologicalDisk (e '' S) := by
    intro S e
    constructor
    · rintro ⟨h⟩
      exact ⟨h.trans (e.image S)⟩
    · rintro ⟨h⟩
      rw [← e.symm_image_image S]
      exact ⟨h.trans ((e.symm).image (e '' S))⟩
  have htranslation := TileTranslationFormulas T u
  have hquarter := TileQuarterTurnFormulas T
  have hreflection := TileReflectionFormulas T
  have ht : LatticeTile T ↔ LatticeTile (TileTranslation T u) := by
    change TopologicalDisk (TileRealization T) ↔
      TopologicalDisk (TileRealization (TileTranslation T u))
    rw [htranslation.2.2.2.1]
    simpa [translation, Function.comp_def, add_comm] using disk_image _ translation
  have hq : LatticeTile T ↔ LatticeTile (TileQuarterTurn T) := by
    change TopologicalDisk (TileRealization T) ↔
      TopologicalDisk (TileRealization (TileQuarterTurn T))
    rw [hquarter.2.2.2.1]
    simpa [quarter, Function.comp_def] using disk_image _ quarter
  have hr : LatticeTile T ↔ LatticeTile (TileReflection T) := by
    change TopologicalDisk (TileRealization T) ↔
      TopologicalDisk (TileRealization (TileReflection T))
    rw [hreflection.2.2.2.1]
    simpa [reflection, Function.comp_def] using disk_image _ reflection
  have transArea : TileArea (TileTranslation T u) = TileArea T := by
    change (TileTranslation T u).cells.card = T.cells.card
    rw [htranslation.1, Finset.card_image_iff.mpr]
    intro a ha b hb hab
    dsimp [GaussianTranslation] at hab
    exact add_right_cancel hab
  have quarterArea : TileArea (TileQuarterTurn T) = TileArea T := by
    change (TileQuarterTurn T).cells.card = T.cells.card
    rw [hquarter.1, Finset.card_image_iff.mpr]
    intro a ha b hb hab
    apply Zsqrtd.ext
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.im) hab
    · simpa [GaussianQuarterTurn] using congrArg (fun z : GaussianInt => z.re) hab
  have reflectionArea : TileArea (TileReflection T) = TileArea T := by
    change (TileReflection T).cells.card = T.cells.card
    rw [hreflection.1, Finset.card_image_iff.mpr]
    intro a ha b hb hab
    apply Zsqrtd.ext
    · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => z.re) hab
    · simpa [GaussianReflection] using congrArg (fun z : GaussianInt => -z.im) hab
  exact ⟨ht, hq, hr, transArea, quarterArea, reflectionArea⟩

end ApollonianSuperharmonic

end
