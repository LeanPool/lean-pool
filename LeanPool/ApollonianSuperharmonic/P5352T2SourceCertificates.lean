/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2Sources
public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P5352T2SourceCertificates]

/-!
# P5352T2SourceCertificates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5352T2SourceCertificates (K : DiamondParameter) (hk : 1 < K.1)
    (j : Fin 4) :
    let S := P5352T2Sources K hk j
    0 < ((DiamondRecursiveQuadruple K) j).1 ∧
    TileCentroid S.1 = S.2.2.1 ∧
    ∃ h : PartialOdometer,
      TileOdometer ((DiamondRecursiveQuadruple K) j) S.1 h ∧
      (h.domain : Set GaussianInt) = FootprintVertices S.1 ∧
      (∀ x, x ∈ h.domain → h.value x = S.2.1 x) ∧
      PartialOdometerSlope h = some S.2.2.2 := by
-- BODY
  classical
  have unit (z : GaussianInt) :
      TileOdometer (1, 1 + 2 * z) ⟨{0}, 0⟩ (CurvatureOneOdometer z) := by
    refine TileOdometer.unit z 0 _ _ rfl ?_ ?_
    · ext x
      simp [CurvatureOneOdometer, FootprintVertices]
    · refine ⟨0, 0, 0, ?_, ?_⟩ <;> simp [CurvatureOneOdometer]
  have slope (z : GaussianInt) : PartialOdometerSlope (CurvatureOneOdometer z) =
      some (((z.im : ℝ) / 2), ((z.im : ℝ) / 2)) := by
    have hs : PartialOdometerSquares (CurvatureOneOdometer z) = {0} := by
      change PartialOdometerSquares (CurvatureOneOdometer 0) = {0}
      decide +kernel
    unfold PartialOdometerSlope
    rw [hs]
    norm_num [CurvatureOneOdometer, Zsqrtd.ext_iff]
  have unitDomain (z : GaussianInt) :
      ((CurvatureOneOdometer z).domain : Set GaussianInt) =
        FootprintVertices (⟨{0}, 0⟩ : ProtoTile) := by
    ext x
    simp [CurvatureOneOdometer, FootprintVertices]
  fin_cases j
  · obtain ⟨h, ho, hd, hf, _, hv, hp⟩ := DiamondTileOdometerRestriction K
    refine ⟨?_, ?_, h, ho, hd.trans hf.symm, hv, hp⟩
    · change 0 < (2 * (K.1 : Int) * ((K.1 : Int) + 1))
      have hki : 0 < (K.1 : Int) := by omega
      positivity
    · exact P4194T1DiamondCentroid K.1 (by omega)
  · refine ⟨by norm_num [DiamondRecursiveQuadruple], ?_,
      CurvatureOneOdometer ⟨0, 1⟩, ?_, unitDomain _, fun _ _ => rfl, ?_⟩
    · norm_num [P5352T2Sources, TileCentroid]
    · convert unit ⟨0, 1⟩ using 1 <;>
        norm_num [P5352T2Sources, DiamondRecursiveQuadruple, Zsqrtd.ext_iff,
          Zsqrtd.re_mul, Zsqrtd.im_mul]
    · simpa [P5352T2Sources] using slope ⟨0, 1⟩
  · refine ⟨by norm_num [DiamondRecursiveQuadruple], ?_,
      CurvatureOneOdometer 0, ?_, unitDomain _, fun _ _ => rfl, ?_⟩
    · norm_num [P5352T2Sources, TileCentroid]
    · simpa [P5352T2Sources, DiamondRecursiveQuadruple] using unit 0
    · simpa [P5352T2Sources] using slope 0
  · let L : DiamondParameter := ⟨K.1 - 1, by omega⟩
    obtain ⟨h, ho, hd, hf, _, hv, hp⟩ := DiamondTileOdometerRestriction L
    have circle : (DiamondRecursiveQuadruple L) 0 = (DiamondRecursiveQuadruple K) 3 := by
      simp [L, DiamondRecursiveQuadruple]
      omega
    refine ⟨?_, ?_, h, ?_, hd.trans hf.symm, hv, ?_⟩
    · change 0 < (2 * ((K.1 - 1 : Nat) : Int) * (K.1 : Int))
      have hsub : 0 < K.1 - 1 := by omega
      have hki : 0 < (K.1 : Int) := by omega
      have hsi : 0 < ((K.1 - 1 : Nat) : Int) := by exact_mod_cast hsub
      positivity
    · simpa [P5352T2Sources, Nat.cast_sub (by omega : 1 ≤ K.1)] using
        P4194T1DiamondCentroid (K.1 - 1) (by omega)
    · simpa [P5352T2Sources, L, circle] using ho
    · simpa [P5352T2Sources, L, Nat.cast_sub (by omega : 1 ≤ K.1)] using hp

end ApollonianSuperharmonic

end
