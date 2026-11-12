/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5455T2CurvatureGrowth
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision

-- [TABLET NODE: P5455T2AlignedPredecessor]

/-!
# P5455T2AlignedPredecessor

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5455T2AlignedPredecessor
    (p p' : Fin 4 → CircleCoordinates)
    (hp : ProperBandQuadruple p) (hp' : ProperBandQuadruple p')
    (hchild : P4828T1Step p 0 = P4828T1Step p' 0) :
    p = p' := by
-- BODY
  obtain ⟨r, hr, _⟩ := BandPredecessorNoCollision _ _
    (P5455T2CurvatureGrowth p hp).2.1
    (P5455T2CurvatureGrowth p' hp').2.1 hchild
  have e0 := hr 0
  have e1 := hr 1
  have e2 := hr 2
  have rzero : r = 0 := by
    fin_cases r
    · rfl
    · have a := hp.2 1
      have b := hp'.2 2
      change (p 2).1 < (p 0).1 at a
      change (p' 3).1 < (p' 0).1 at b
      simp? [P4828T1Step] at e0 e2
      rw [e0, e2] at b
      omega
    · have a := hp.2 2
      have b := hp'.2 1
      change (p 3).1 < (p 0).1 at a
      change (p' 2).1 < (p' 0).1 at b
      simp? [P4828T1Step] at e0 e1
      rw [e0, e1] at b
      omega
  subst r
  simp? [P4828T1Step] at e0 e1 e2
  have cx := congrArg Prod.fst hchild
  have wx := congrArg Prod.snd hchild
  simp only [P4828T1Step, Matrix.cons_val_zero] at cx wx
  rw [e0, e1, e2] at cx wx
  have removed : p 1 = p' 1 := by
    apply Prod.ext
    · omega
    · linear_combination -wx
  funext k
  fin_cases k
  · exact e0.symm
  · exact removed
  · exact e1.symm
  · exact e2.symm

end ApollonianSuperharmonic

end
