/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: IncomingSuperbasisRelation]

/-!
# IncomingSuperbasisRelation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IncomingSuperbasisRelation (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) :
    (∑ j : Fin 3, BandVectors.1 (q j.succ) (q 0)) = 0 ∧
    (∑ j : Fin 3, BandVectors.2 (q j.succ) (q 0)) = 0 := by
-- BODY
  have firstLaw := VectorRecursionLaws q hq.1
  have rotated : ProperBandQuadruple (![q 0, q 2, q 3, q 1]) := by
    refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
    intro j
    fin_cases j
    · simpa using hq.2 1
    · simpa using hq.2 2
    · simpa using hq.2 0
  have secondLaw := VectorRecursionLaws (![q 0, q 2, q 3, q 1]) rotated.1
  have rotatedAgain : ProperBandQuadruple (![q 0, q 3, q 1, q 2]) := by
    refine ⟨SemiProperQuadruple.rotate rotated.1, ?_⟩
    intro j
    fin_cases j
    · simpa using hq.2 2
    · simpa using hq.2 0
    · simpa using hq.2 1
  have thirdLaw := VectorRecursionLaws (![q 0, q 3, q 1, q 2]) rotatedAgain.1
  rcases firstLaw with ⟨sumFirst, sumSecond, incomingFirst, incomingSecond, _⟩
  rcases secondLaw with ⟨_, _, rotatedFirst, rotatedSecond, _⟩
  rcases thirdLaw with ⟨_, _, rotatedAgainFirst, rotatedAgainSecond, _⟩
  simp? at rotatedFirst rotatedSecond rotatedAgainFirst rotatedAgainSecond
  simp? [Fin.sum_univ_succ]
  constructor
  · rw [incomingFirst, rotatedFirst, rotatedAgainFirst]
    calc
      _ = (1 - (⟨0, 1⟩ : GaussianInt)) *
          (BandVectors.1 (q 1) (q 3) +
            BandVectors.1 (q 2) (q 1) + BandVectors.1 (q 3) (q 2)) := by ring
      _ = 0 := by
        rw [show BandVectors.1 (q 1) (q 3) +
            BandVectors.1 (q 2) (q 1) + BandVectors.1 (q 3) (q 2) = 0 by
          calc
            _ = BandVectors.1 (q 3) (q 2) +
                BandVectors.1 (q 1) (q 3) + BandVectors.1 (q 2) (q 1) := by ring
            _ = 0 := sumFirst]
        simp
  · rw [incomingSecond, rotatedSecond, rotatedAgainSecond]
    calc
      _ = (1 + (⟨0, 1⟩ : GaussianInt)) *
          (BandVectors.2 (q 1) (q 3) +
            BandVectors.2 (q 2) (q 1) + BandVectors.2 (q 3) (q 2)) := by ring
      _ = 0 := by
        rw [show BandVectors.2 (q 1) (q 3) +
            BandVectors.2 (q 2) (q 1) + BandVectors.2 (q 3) (q 2) = 0 by
          calc
            _ = BandVectors.2 (q 3) (q 2) +
                BandVectors.2 (q 1) (q 3) + BandVectors.2 (q 2) (q 1) := by ring
            _ = 0 := sumSecond]
        simp

end ApollonianSuperharmonic

end
