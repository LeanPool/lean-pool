/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn
public import Mathlib.Tactic.Ring

/-!
# Parent-vector sum identities

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- The three parent vectors pointing into the child sum to zero. -/
theorem BandVectorIncomingSum (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) :
    BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
      BandVectors.1 (q 3) (q 0) = 0 := by
  classical
  have laws := VectorRecursionLaws q hq.1
  let r : Fin 4 -> CircleCoordinates := ![q 0, q 2, q 3, q 1]
  have hr : SemiProperQuadruple r := by
    simpa [r] using SemiProperQuadruple.rotate
      hq.1
  let s : Fin 4 -> CircleCoordinates := ![r 0, r 2, r 3, r 1]
  have hs : SemiProperQuadruple s := by
    simpa [s] using SemiProperQuadruple.rotate hr
  have second := VectorRecursionLaws r hr
  have third := VectorRecursionLaws s hs
  have e0 := laws.2.2.1
  have e1 := second.2.2.1
  have e2 := third.2.2.1
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Int.reduceNeg,
      Matrix.cons_val, r, s] at e1 e2
  rw [e0, e1, e2]
  calc
    _ = (1 - (⟨0, 1⟩ : GaussianInt)) *
        (BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
          BandVectors.1 (q 2) (q 1)) := by ring
    _ = 0 := by rw [laws.1]; simp


/-- The three vectors pointing from the child to its parents sum to zero. -/
theorem BandVectorOutgoingSum (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) :
    BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) +
      BandVectors.1 (q 0) (q 3) = 0 := by
  classical
  have flip := (VectorRecursionLaws q hq.1).2.2.2.2 hq
  have turn (j : Fin 3) : GaussianQuarterTurn (BandVectors.1 (q j.succ) (q 0)) =
      BandVectors.1 (q 0) (q j.succ) := by
    rw [(flip j).1]
    rcases BandVectors.1 (q j.succ) (q 0) with ⟨a, b⟩
    ext <;> simp [GaussianQuarterTurn, Zsqrtd.re_mul, Zsqrtd.im_mul]
  have turn0 : GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) =
      BandVectors.1 (q 0) (q 1) := turn 0
  have turn1 : GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) =
      BandVectors.1 (q 0) (q 2) := turn 1
  have turn2 : GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) =
      BandVectors.1 (q 0) (q 3) := turn 2
  have incoming_relation := BandVectorIncomingSum q hq
  rw [← turn0, ← turn1, ← turn2]
  calc
    _ = GaussianQuarterTurn (BandVectors.1 (q 1) (q 0) +
        BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0)) := by
          rcases BandVectors.1 (q 1) (q 0) with ⟨a0, b0⟩
          rcases BandVectors.1 (q 2) (q 0) with ⟨a1, b1⟩
          rcases BandVectors.1 (q 3) (q 0) with ⟨a2, b2⟩
          apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]; ring
    _ = GaussianQuarterTurn 0 := congrArg GaussianQuarterTurn incoming_relation
    _ = 0 := by rfl

end ApollonianSuperharmonic

end
