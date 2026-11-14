/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5352T2PlacementData
public import LeanPool.ApollonianSuperharmonic.DiamondCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.P5352T2Sources
public import Mathlib.Tactic.Polynomial.Basic

-- [TABLET NODE: P5352T2VectorPlacements]

/-!
# P5352T2VectorPlacements

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5352T2VectorPlacements (K : DiamondParameter) (hk : 1 < K.1)
    (i : Fin 3) (s : Fin 4) :
    let q := DiamondRecursiveQuadruple K
    let A := P5352T2Sources K hk 0
    let D := P5352T2Sources K hk i.succ
    let M := P5352T2PlacementData K.1 i
    BandVectors.1 (q 0) (q i.succ) = M.1.1 ∧
    BandVectors.2 (q 0) (q i.succ) = M.1.2 ∧
    (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt)^s.val *
          (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))) =
      (D.2.2.1.1 - A.2.2.1.1 + (M.2 s).1.re,
       D.2.2.1.2 - A.2.2.1.2 + (M.2 s).1.im) ∧
    (1 / 2 : ℝ) • GaussianRealPoint
        ((-⟨0, 1⟩ : GaussianInt)^s.val *
          (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ))) =
      (D.2.2.2.1 - A.2.2.2.1 + (M.2 s).2.1.re,
       D.2.2.2.2 - A.2.2.2.2 + (M.2 s).2.1.im) ∧
    (⟨0, 1⟩ : GaussianInt)^s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0)) = (M.2 s).2.2 := by
-- BODY
  obtain ⟨_, hq, hv0, hv1, hv2, ha0, ha1, ha2, _⟩ := DiamondCoordinateConfiguration K
  have flip := (VectorRecursionLaws _ hq.1).2.2.2.2 hq
  have hv (t : Fin 3) : BandVectors.1 ((DiamondRecursiveQuadruple K) t.succ)
      ((DiamondRecursiveQuadruple K) 0) =
      ![⟨(K.1 : Int)+1, (K.1 : Int)⟩, ⟨-(K.1 : Int)-1, (K.1 : Int)⟩,
        ⟨0, -2*(K.1 : Int)⟩] t := by
    fin_cases t
    · exact hv0
    · exact hv1
    · exact hv2
  have ha (t : Fin 3) : BandVectors.2 ((DiamondRecursiveQuadruple K) t.succ)
      ((DiamondRecursiveQuadruple K) 0) =
      ![⟨(K.1 : Int), 1⟩, ⟨0, -(K.1 : Int)⟩,
        ⟨-(K.1 : Int), (K.1 : Int)-1⟩] t := by
    fin_cases t
    · exact ha0
    · exact ha1
    · exact ha2
  dsimp only
  rw [(flip i).1, (flip i).2, hv, ha]
  fin_cases i <;> fin_cases s <;>
    norm_num [P5352T2PlacementData, P5352T2Sources, GaussianRealPoint,
      GaussianInt.toComplex_def, Zsqrtd.re_mul, Zsqrtd.im_mul,
      Zsqrtd.ext_iff, Prod.ext_iff, pow_succ, Nat.even_iff] <;>
    (repeat' constructor)  <;> ring

end ApollonianSuperharmonic

end
