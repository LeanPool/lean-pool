/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandVectors

-- [TABLET NODE: VectorRecursionLaws]

/-!
# VectorRecursionLaws

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem VectorRecursionLaws (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) :
    BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
        BandVectors.1 (q 2) (q 1) = 0 ∧
      BandVectors.2 (q 3) (q 2) + BandVectors.2 (q 1) (q 3) +
        BandVectors.2 (q 2) (q 1) = 0 ∧
      BandVectors.1 (q 1) (q 0) =
        BandVectors.1 (q 1) (q 3) -
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 2) (q 1) ∧
      BandVectors.2 (q 1) (q 0) =
        BandVectors.2 (q 1) (q 3) +
          (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 2) (q 1) ∧
      (ProperBandQuadruple q →
        ∀ j : Fin 3,
          BandVectors.1 (q 0) (q j.succ) =
              (⟨0, 1⟩ : GaussianInt) *
                BandVectors.1 (q j.succ) (q 0) ∧
            BandVectors.2 (q 0) (q j.succ) =
              -(⟨0, 1⟩ : GaussianInt) *
                BandVectors.2 (q j.succ) (q 0)) := by
-- BODY
  have systemLaw : RecursiveVectorSystem BandVectors :=
    by simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  rcases systemLaw with ⟨zeroLaw, baseLaw, stepLaw, flipLaw⟩
  induction hq with
  | base z =>
      have baseFacts := baseLaw z
      simp only [Int.reduceNeg, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
          Matrix.cons_val_zero] at baseFacts
      rcases baseFacts with ⟨v32, v21, v13, a32, a21, a13⟩
      have rotatedFacts := stepLaw (![(1, 1 + 2 * z),
        (0, -1), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1)])
        (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate (SemiProperQuadruple.base z)))
      rcases rotatedFacts with ⟨rv, ra, rv2, ra2⟩
      constructor
      · simp [v32, v21, v13]
      constructor
      · simp [a32, a21, a13]
        ring
      constructor
      · simpa using rv
      constructor
      · simpa using rv2
      intro proper j
      exact ⟨flipLaw _ _ (PrimitiveVectorOrientation.parentChild proper j) |>.1,
        flipLaw _ _ (PrimitiveVectorOrientation.parentChild proper j) |>.2⟩
  | rotate hq ih =>
      have rotatedFacts := stepLaw _ hq
      rcases rotatedFacts with ⟨rv, ra, rv2, ra2⟩
      rcases ih with ⟨iv, ia, isv, isa, iproper⟩
      constructor
      · simpa [add_assoc, add_left_comm, add_comm] using iv
      constructor
      · simpa [add_assoc, add_left_comm, add_comm] using ia
      constructor
      · simpa using rv
      constructor
      · simpa using rv2
      intro proper j
      exact ⟨flipLaw _ _ (PrimitiveVectorOrientation.parentChild proper j) |>.1,
        flipLaw _ _ (PrimitiveVectorOrientation.parentChild proper j) |>.2⟩
  | @successor predecessor hq ih =>
      have directFacts := stepLaw predecessor hq
      rcases directFacts with ⟨directV, directW, directA, directB⟩
      rcases ih with ⟨oldV, oldA, oldW, oldB, oldFlip⟩
      dsimp
      constructor
      · rw [directW, directV]
        rw [← oldV]
        ring
      constructor
      · rw [directB, directA]
        rw [← oldA]
        ring
      have rotatedFacts := stepLaw _
        (SemiProperQuadruple.rotate
          (SemiProperQuadruple.rotate (SemiProperQuadruple.successor hq)))
      rcases rotatedFacts with ⟨rotatedV, rotatedW, rotatedA, rotatedB⟩
      constructor
      · simpa using rotatedV
      constructor
      · simpa using rotatedA
      intro proper j
      exact ⟨flipLaw _ _ (PrimitiveVectorOrientation.parentChild proper j) |>.1,
        flipLaw _ _ (PrimitiveVectorOrientation.parentChild proper j) |>.2⟩

/-- The four vector recursion laws at any cyclic parent occurrence. -/
theorem VectorRecursionLaws.cyclic (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) (i : Fin 3) :
    BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ)) +
        BandVectors.1 (q i.succ) (q ((i + 2).succ)) +
        BandVectors.1 (q ((i + 1).succ)) (q i.succ) = 0 ∧
    BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ)) +
        BandVectors.2 (q i.succ) (q ((i + 2).succ)) +
        BandVectors.2 (q ((i + 1).succ)) (q i.succ) = 0 ∧
    BandVectors.1 (q i.succ) (q 0) =
        BandVectors.1 (q i.succ) (q ((i + 2).succ)) -
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q ((i + 1).succ)) (q i.succ) ∧
    BandVectors.2 (q i.succ) (q 0) =
        BandVectors.2 (q i.succ) (q ((i + 2).succ)) +
          (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q ((i + 1).succ)) (q i.succ) := by
  fin_cases i
  · have h := VectorRecursionLaws q hq
    simpa using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))
  · have h := VectorRecursionLaws ![q 0, q 2, q 3, q 1]
      (SemiProperQuadruple.rotate hq)
    simpa using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))
  · have hr : SemiProperQuadruple ![q 0, q 3, q 1, q 2] := by
      simpa using SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq)
    have h := VectorRecursionLaws ![q 0, q 3, q 1, q 2] hr
    simpa using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))

end ApollonianSuperharmonic

end
