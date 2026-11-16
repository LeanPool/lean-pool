/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4981T1PrescriptionValue
public import LeanPool.ApollonianSuperharmonic.P4981T1Recursion
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientation

-- [TABLET NODE: P4981T1ProperEquations]

/-!
# P4981T1ProperEquations

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4981T1ProperEquations
    (F : CircleCoordinates × CircleCoordinates → GaussianInt × GaussianInt)
    (rev : ∀ C D, PrimitiveVectorOrientation C D →
      F (D, C) = ((⟨0, 1⟩ : GaussianInt) * (F (C, D)).1,
        -(⟨0, 1⟩ : GaussianInt) * (F (C, D)).2)) :
    (∀ q (hq : ProperBandQuadruple q) j,
      F (q j.succ, q 0) = P4981T1PrescriptionValue (.proper q hq j) F) ↔
    (∀ q, ProperBandQuadruple q → P4981T1Recursion F q) := by
-- BODY
  let ii : GaussianInt := ⟨0, 1⟩
  have square : ii * ii = -1 := by decide +kernel
  constructor
  · intro table q hq
    have hin := table q hq 1
    have hout := rev (q 3) (q 0) (.parentChild hq 2)
    have h2 := table q hq 2
    change F (q 3, q 0) = _ at h2
    rw [h2] at hout
    change F (q 2, q 0) =
      ((F (q 2, q 1)).1 - ii * (F (q 3, q 2)).1,
       (F (q 2, q 1)).2 + ii * (F (q 3, q 2)).2) at hin
    change F (q 0, q 3) =
      (ii * ((F (q 3, q 2)).1 - ii * (F (q 1, q 3)).1),
       -ii * ((F (q 3, q 2)).2 + ii * (F (q 1, q 3)).2)) at hout
    refine ⟨congrArg Prod.fst hin, ?_, congrArg Prod.snd hin, ?_⟩
    · change (F (q 0, q 3)).1 = _
      rw [hout]
      dsimp only
      simp only [mul_sub, ← mul_assoc, square, neg_one_mul, sub_neg_eq_add]
      exact add_comm _ _
    · change (F (q 0, q 3)).2 = _
      rw [hout]
      dsimp only
      simp only [neg_mul, mul_add, ← mul_assoc, square]
      ring
  · intro rec q hq j
    let qr : Fin 4 → CircleCoordinates :=
      ![q 0, q ((j + 2).succ), q j.succ, q ((j + 1).succ)]
    have hqr : ProperBandQuadruple qr := by
      fin_cases j
      · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1), ?_⟩
        intro k
        fin_cases k
        · exact hq.2 2
        · exact hq.2 0
        · exact hq.2 1
      · convert hq using 1
        funext k
        fin_cases k <;> rfl
      · refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
        intro k
        fin_cases k
        · exact hq.2 1
        · exact hq.2 2
        · exact hq.2 0
    have equations := rec qr hqr
    exact Prod.ext equations.1 equations.2.2.1

end ApollonianSuperharmonic

end
