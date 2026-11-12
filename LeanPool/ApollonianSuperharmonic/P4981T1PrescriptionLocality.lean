/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4981T1EdgeRank
public import LeanPool.ApollonianSuperharmonic.P4981T1PrescriptionValue
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure

-- [TABLET NODE: P4981T1PrescriptionLocality]

/-!
# P4981T1PrescriptionLocality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4981T1PrescriptionLocality {e : CircleCoordinates × CircleCoordinates}
    (p : P4981T1EdgePrescription e)
    (F G : CircleCoordinates × CircleCoordinates → GaussianInt × GaussianInt)
    (h : ∀ d, P4981T1EdgeRank d < P4981T1EdgeRank e → F d = G d) :
    P4981T1PrescriptionValue p F = P4981T1PrescriptionValue p G := by
-- BODY
  cases p with
  | line => rfl
  | left z => rfl
  | right z => rfl
  | unit z => rfl
  | proper q hq j =>
      have pos := (ProperBandCurvatureStructure q hq).1
      have lower (k : Fin 3) : (q k.succ).1.toNat < (q 0).1.toNat :=
        (Int.toNat_lt_toNat pos).mpr (hq.2 k)
      have small (k l : Fin 3) :
          P4981T1EdgeRank (q k.succ, q l.succ) <
            P4981T1EdgeRank (q j.succ, q 0) := by
        dsimp only [P4981T1EdgeRank]
        exact lt_of_lt_of_le (max_lt (lower k) (lower l)) (le_max_right _ _)
      simp only [P4981T1PrescriptionValue,
        h _ (small j (j + 2)), h _ (small (j + 1) j)]

end ApollonianSuperharmonic

end
