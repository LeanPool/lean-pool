/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5124T1ParentModel
public import LeanPool.ApollonianSuperharmonic.DiamondTileRecursiveIdentification

-- [TABLET NODE: P5124T1ParentPlacement]

/-!
# P5124T1ParentPlacement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5124T1ParentPlacement (K : DiamondParameter) (i : Fin 3) (s : Bool) :
    let q := DiamondRecursiveQuadruple K
    let P := P5124T1ParentModel K.1 i s
    BandPrototile (q i.succ) P ∧
      TileCentroid P - TileCentroid (DiamondTile K.1) =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
            (if s then GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))
             else -GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) := by
-- BODY
  classical
  have centroid (n : Nat) : TileCentroid (DiamondTile n) = (0, (n : Real)) := by
    by_cases hn : 0 < n
    · exact P4194T1DiamondCentroid n hn
    · have hn0 : n = 0 := by omega
      subst n
      simp [TileCentroid, DiamondTile, DiamondCellDomain]
  have singleton_centroid (x : GaussianInt) :
      TileCentroid (⟨{x}, x⟩ : ProtoTile) =
        ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) := by
    simp [TileCentroid]
  obtain ⟨_, hq, hv0, hv1, hv2, _⟩ := DiamondCoordinateConfiguration K
  have flip := (VectorRecursionLaws _ hq.1).2.2.2.2 hq
  have hunit : (1 : GaussianInt) + 2 * ⟨0, 1⟩ = ⟨1, 2⟩ := by
    ext <;> norm_num
  constructor
  · fin_cases i
    · cases s <;>
        simpa [P5124T1ParentModel, DiamondRecursiveQuadruple, hunit] using
          (BandPrototile.unit (⟨0, 1⟩ : GaussianInt) _ _)
    · cases s <;>
        simpa [P5124T1ParentModel, DiamondRecursiveQuadruple] using
          (BandPrototile.unit (0 : GaussianInt) _ _)
    · obtain ⟨_, S, hS, _, _, _, _, _, hprev, _⟩ :=
        DiamondTileRecursiveIdentification K
      have hp := (hS 2 false).1
      rw [hprev] at hp
      cases s <;>
        exact BandPrototileTranslation _ _ _ hp
  · have hk : 1 ≤ K.1 := K.2
    have ht (w : GaussianInt) :=
      (TileTranslationFormulas (DiamondTile (K.1 - 1)) w).2.2.2.2.1
    rw [(flip i).1]
    fin_cases i <;> cases s <;>
      simp [P5124T1ParentModel, singleton_centroid, centroid, ht,
        hv0, hv1, hv2, GaussianRealPoint, Prod.ext_iff, Nat.cast_sub hk] <;>
      ring <;> simp

end ApollonianSuperharmonic

end
