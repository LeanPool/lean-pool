/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.VectorSquareProduct
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity

-- [TABLET NODE: VectorNonvanishing]

/-!
# VectorNonvanishing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem VectorNonvanishing (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) (i j : Fin 4) (hij : i ≠ j)
    (hpositive : 0 < (q i).1 ∨ 0 < (q j).1) :
    BandVectors.1 (q i) (q j) ≠ 0 := by
-- BODY
  have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 := by
    intro r hr
    induction hr with
    | base z =>
        intro k
        fin_cases k <;> simp
    | rotate hr ih =>
        intro k
        fin_cases k
        · simpa using ih 0
        · simpa using ih 2
        · simpa using ih 3
        · simpa using ih 1
    | @successor r hr ih =>
        intro k
        have classification := BandSuccessorClassification r hr
        dsimp at classification
        rcases classification with special | proper
        · fin_cases k
          · simp [special]
          · simpa using ih 0
          · simpa using ih 2
          · simpa using ih 3
        · rcases proper with ⟨_, larger0, larger2, larger3⟩
          fin_cases k
          · change 0 ≤ 2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1
            exact (ih 0).trans larger0.le
          · exact ih 0
          · exact ih 2
          · exact ih 3
  have hnonneg := nonnegative q hq
  have hsum : 0 < (q i).1 + (q j).1 := by
    rcases hpositive with hi | hj
    · exact add_pos_of_pos_of_nonneg hi (hnonneg j)
    · exact add_pos_of_nonneg_of_pos (hnonneg i) hj
  intro hv
  have hproduct := (VectorSquareProduct q hq i j hij).1
  have hzero : (q j).1 • (q i).2 - (q i).1 • (q j).2 = 0 := by
    rw [← hproduct, hv]
    simp
  have hnorm : Zsqrtd.norm ((q j).1 • (q i).2 - (q i).1 • (q j).2) = 0 := by
    rw [hzero]
    simp
  have hsquare : ((q i).1 + (q j).1) ^ 2 = 0 := by
    rw [← TangencyCoordinateIdentity q hq i j hij]
    exact hnorm
  nlinarith

end ApollonianSuperharmonic

end
