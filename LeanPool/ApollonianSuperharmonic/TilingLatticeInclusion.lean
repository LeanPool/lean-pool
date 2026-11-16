/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector
public import LeanPool.ApollonianSuperharmonic.IntegralityLattice
public import LeanPool.ApollonianSuperharmonic.TilingLattice

-- [TABLET NODE: TilingLatticeInclusion]

/-!
# TilingLatticeInclusion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TilingLatticeInclusion (C : BandCircle) :
    TilingLattice C ≤ IntegralityLattice C := by
-- BODY
  have hmatrix :
      CircleMatrix C =
        let c : ℝ := C.1.1.1
        let x : ℝ := C.1.1.2.re
        let y : ℝ := C.1.1.2.im
        (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CircleMatrix, BandCircleEuclideanData]
    all_goals field_simp
  by_cases hc : C.1.1.1 = 1
  · have parity : ∀ q : Fin 4 → CircleCoordinates, SemiProperQuadruple q →
        ∀ j : Fin 4, ∃ a b : ℤ,
          (q j).2.re = 1 + 2 * a ∧
          (q j).2.im = 2 * b := by
      intro q hq
      induction hq with
      | base z =>
          intro j
          fin_cases j
          · exact ⟨z.re, z.im, by simp, by simp⟩
          · exact ⟨z.re, z.im + 1, by norm_num [Zsqrtd.ext_iff], by norm_num [Zsqrtd.ext_iff]; ring⟩
          · exact ⟨0, 0, by simp, by simp⟩
          · exact ⟨-1, 0, by simp, by simp⟩
      | rotate hq ih =>
          intro j
          fin_cases j <;> simp_all
      | @successor q hq ih =>
          intro j
          fin_cases j
          · dsimp
            rcases ih 0 with ⟨a0, b0, ha0, hb0⟩
            rcases ih 1 with ⟨a1, b1, ha1, hb1⟩
            rcases ih 2 with ⟨a2, b2, ha2, hb2⟩
            rcases ih 3 with ⟨a3, b3, ha3, hb3⟩
            refine ⟨2 * a0 + 2 * a2 + 2 * a3 - a1 + 2,
              2 * b0 + 2 * b2 + 2 * b3 - b1, ?_, ?_⟩
            · rw [ha0, ha1, ha2, ha3]
              ring
            · rw [hb0, hb1, hb2, hb3]
              ring
          · simpa using ih 0
          · simpa using ih 2
          · simpa using ih 3
    unfold TilingLattice
    split
    · intro u hu
      unfold IntegralityLattice
      intro i
      obtain ⟨q, hq, j, hj⟩ := C.1.2.2
      obtain ⟨a, b, ha, hb⟩ := parity q hq j
      have hxr : C.1.1.2.re = 1 + 2 * a := by simpa [hj] using ha
      have hxi : C.1.1.2.im = 2 * b := by simpa [hj] using hb
      fin_cases i
      · refine ⟨u.re + a * u.re + b * u.im, ?_⟩
        simp [hmatrix, Matrix.mulVec, hc, hxr, hxi]
        ring
      · refine ⟨b * u.re - a * u.im, ?_⟩
        simp [hmatrix, Matrix.mulVec, hc, hxr, hxi]
        ring
    · rename_i h
      exact (h hc).elim
  · unfold TilingLattice
    split
    · rename_i h
      exact (hc h).elim
    · rw [AddSubgroup.closure_le]
      intro u hu
      obtain ⟨q, hq, hq0, hsmall, j, rfl⟩ := hu
      intro i
      obtain hvec := CircleMatrixIncomingVector C q hq hq0 j
      have hcoord := congrFun hvec i
      fin_cases i
      · refine ⟨(BandVectors.2 (q j.succ) (q 0)).re, ?_⟩
        simpa [IntegralityLattice, Matrix.mulVec] using hcoord
      · refine ⟨(BandVectors.2 (q j.succ) (q 0)).im, ?_⟩
        simpa [IntegralityLattice, Matrix.mulVec] using hcoord

end ApollonianSuperharmonic

end
