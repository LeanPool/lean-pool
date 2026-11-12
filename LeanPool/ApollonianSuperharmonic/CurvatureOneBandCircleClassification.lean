/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: CurvatureOneBandCircleClassification]

/-!
# CurvatureOneBandCircleClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem CurvatureOneBandCircleClassification (C : BandCircle)
    (hc : C.1.1.1 = 1) :
    ∃ z : GaussianInt, C.1.1 = (1, 1 + 2 * z) := by
-- BODY
  have invariant : ∀ q : Fin 4 → CircleCoordinates,
      SemiProperQuadruple q → ∀ k : Fin 4, (q k).1 = 1 →
        ∃ z : GaussianInt, q k = (1, 1 + 2 * z) := by
    intro q hq
    induction hq with
    | base z =>
        intro k hk
        fin_cases k
        · exact ⟨z, by rfl⟩
        · refine ⟨z + ⟨0, 1⟩, ?_⟩
          change (1, 1 + 2 * z + 2 * ⟨0, 1⟩) =
            (1, 1 + 2 * (z + ⟨0, 1⟩))
          congr 1
          ring_nf
        · simp at hk
        · simp at hk
    | rotate hq ih =>
        intro k hk
        fin_cases k
        · exact ih 0 hk
        · exact ih 2 hk
        · exact ih 3 hk
        · exact ih 1 hk
    | @successor q hq ih =>
        intro k hk
        fin_cases k
        · let s : Fin 4 → CircleCoordinates :=
            ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
                2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
              q 0, q 2, q 3]
          have hs : SemiProperQuadruple s := by
            exact SemiProperQuadruple.successor hq
          have classified := SemiProperForestClassification s hs
          rcases classified.2 with root | root | root | proper
          · rcases root with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            simpa [s] using congrFun hz 0
          · rcases root with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            simpa [s] using congrFun hz 0
          · rcases root with ⟨z, hz⟩
            refine ⟨z, ?_⟩
            simpa [s] using congrFun hz 0
          · have nonneg := classified.1
            have oldNonneg := (SemiProperForestClassification q hq).1
            have h1 := proper.2 0
            have h2 := proper.2 1
            have h3 := proper.2 2
            simp [s] at hk h1 h2 h3
            have a := nonneg 0
            have b := nonneg 1
            have c := nonneg 2
            have d := nonneg 3
            have e := oldNonneg 1
            simp [s] at a b c d
            exfalso
            omega
        · exact ih 0 hk
        · exact ih 2 hk
        · exact ih 3 hk
  rcases C.1.2.2 with ⟨q, hq, j, hj⟩
  have hjcurv : (q j).1 = 1 := by
    simpa [hj] using hc
  rcases invariant q hq j hjcurv with ⟨z, hz⟩
  exact ⟨z, by simpa [hj] using hz⟩

end ApollonianSuperharmonic

end
