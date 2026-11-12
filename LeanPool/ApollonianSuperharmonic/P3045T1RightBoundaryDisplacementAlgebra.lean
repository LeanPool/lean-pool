/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P3045T1RightBoundaryDisplacementAlgebra]

/-!
# P3045T1RightBoundaryDisplacementAlgebra

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3045T1RightBoundaryDisplacementAlgebra (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (r t k : Fin 3)
    (hcyc : (r = 0 ∧ t = 1 ∧ k = 2) ∨
      (r = 1 ∧ t = 2 ∧ k = 0) ∨ (r = 2 ∧ t = 0 ∧ k = 1)) :
    let v := BandVectors.1
    let a := BandVectors.2
    let I : GaussianInt := ⟨0, 1⟩
    ((1 - I) * v (q k.succ) (q t.succ) + 2 * v (q 0) (q k.succ) =
      -I * (v (q r.succ) (q 0) + v (q 0) (q r.succ))) ∧
    (-(1 - I) * v (q r.succ) (q k.succ) + 2 * v (q 0) (q k.succ) =
      -(v (q t.succ) (q 0) + v (q 0) (q t.succ))) ∧
    (-(1 - I) * v (q k.succ) (q t.succ) - 2 * v (q 0) (q k.succ) =
      I * (v (q r.succ) (q 0) + v (q 0) (q r.succ))) ∧
    ((1 - I) * v (q r.succ) (q k.succ) - 2 * v (q 0) (q k.succ) =
      v (q t.succ) (q 0) + v (q 0) (q t.succ)) ∧
    ((1 + I) * a (q k.succ) (q t.succ) + 2 * a (q 0) (q k.succ) =
      I * (a (q r.succ) (q 0) + a (q 0) (q r.succ))) ∧
    (-(1 + I) * a (q r.succ) (q k.succ) + 2 * a (q 0) (q k.succ) =
      -(a (q t.succ) (q 0) + a (q 0) (q t.succ))) ∧
    (-(1 + I) * a (q k.succ) (q t.succ) - 2 * a (q 0) (q k.succ) =
      -I * (a (q r.succ) (q 0) + a (q 0) (q r.succ))) ∧
    ((1 + I) * a (q r.succ) (q k.succ) - 2 * a (q 0) (q k.succ) =
      a (q t.succ) (q 0) + a (q 0) (q t.succ)) ∧
    (∀ j : Fin 3, v (q 0) (q j.succ) = I * v (q j.succ) (q 0) ∧
      a (q 0) (q j.succ) = -I * a (q j.succ) (q 0)) := by
-- BODY
  dsimp only
  obtain ⟨vsum, asum, v1, a1, flip⟩ := VectorRecursionLaws q hq.1
  have laws2 := VectorRecursionLaws _ (SemiProperQuadruple.rotate hq.1)
  have laws3 := VectorRecursionLaws _
    (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1))
  have v2 : BandVectors.1 (q 2) (q 0) = BandVectors.1 (q 2) (q 1) -
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 2) := by
    simpa using laws2.2.2.1
  have a2 : BandVectors.2 (q 2) (q 0) = BandVectors.2 (q 2) (q 1) +
      (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 3) (q 2) := by
    simpa using laws2.2.2.2.1
  have v3 : BandVectors.1 (q 3) (q 0) = BandVectors.1 (q 3) (q 2) -
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 3) := by
    simpa using laws3.2.2.1
  have a3 : BandVectors.2 (q 3) (q 0) = BandVectors.2 (q 3) (q 2) +
      (⟨0, 1⟩ : GaussianInt) * BandVectors.2 (q 1) (q 3) := by
    simpa using laws3.2.2.2.1
  have vf1 := (flip hq 0).1
  have vf2 := (flip hq 1).1
  have vf3 := (flip hq 2).1
  have af1 := (flip hq 0).2
  have af2 := (flip hq 1).2
  have af3 := (flip hq 2).2
  have s0 : (0 : Fin 3).succ = (1 : Fin 4) := rfl
  have s1 : (1 : Fin 3).succ = (2 : Fin 4) := rfl
  have s2 : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simp only [s0, s1, s2] at vf1 vf2 vf3 af1 af2 af3
  have vc : BandVectors.1 (q 2) (q 1) =
      -BandVectors.1 (q 3) (q 2) - BandVectors.1 (q 1) (q 3) := by
    apply eq_of_sub_eq_zero
    calc
      _ = BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
          BandVectors.1 (q 2) (q 1) := by ring
      _ = 0 := vsum
  have ac : BandVectors.2 (q 2) (q 1) =
      -BandVectors.2 (q 3) (q 2) - BandVectors.2 (q 1) (q 3) := by
    apply eq_of_sub_eq_zero
    calc
      _ = BandVectors.2 (q 3) (q 2) + BandVectors.2 (q 1) (q 3) +
          BandVectors.2 (q 2) (q 1) := by ring
      _ = 0 := asum
  rcases hcyc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, flip hq⟩
    all_goals
      simp only [s0, s1, s2]
      simp only [vf1, vf2, vf3, af1, af2, af3, v1, v2, v3, a1, a2, a3, vc, ac]
      ext <;> simp <;> ring

end ApollonianSuperharmonic

end
