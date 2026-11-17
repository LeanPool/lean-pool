/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Tactic.Ring
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryReversesOrientation


/-!
# Affine vector action laws

Additivity, negation and signed quarter-turn covariance shared by marked-data
covariance and subtile lattice transport.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPackingSymmetryAffineVectorLaws :
    (by
      classical
      exact
        let affineQuarter : GaussianInt × GaussianInt → GaussianInt × GaussianInt :=
          fun z => (GaussianQuarterTurn z.1, -GaussianQuarterTurn z.2)
        ∀ k : BandPackingSymmetry, (∀ y, ∀ z, BandPackingSymmetryAffineVectorAction k (y + z) =
            BandPackingSymmetryAffineVectorAction k y + BandPackingSymmetryAffineVectorAction k
            z) ∧ (∀ y, BandPackingSymmetryAffineVectorAction k (-y) =
            -BandPackingSymmetryAffineVectorAction k y) ∧ (∀ y,
            BandPackingSymmetryAffineVectorAction k (affineQuarter y) = if
            BandPackingSymmetryReversesOrientation k then -affineQuarter
            (BandPackingSymmetryAffineVectorAction k y) else affineQuarter
            (BandPackingSymmetryAffineVectorAction k y)) ) := by
  classical
  intro affineQuarter k
  induction k with
  | identity => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | shift w =>
      rcases w with ⟨wr, wi⟩
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨⟨vr, vi⟩, ⟨ar, ai⟩⟩ ⟨⟨ur, ui⟩, ⟨br, bi⟩⟩
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
      · rintro ⟨⟨vr, vi⟩, ⟨ar, ai⟩⟩
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
      · rintro ⟨⟨vr, vi⟩, ⟨ar, ai⟩⟩
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection,
          BandPackingSymmetryReversesOrientation, affineQuarter,
          GaussianQuarterTurn]; ring
  | negate =>
      refine ⟨?_, ?_, ?_⟩
      · intro y z
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn] <;> ring
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn,
          BandPackingSymmetryReversesOrientation, affineQuarter]
  | conjugate =>
      refine ⟨?_, ?_, ?_⟩
      · intro y z
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection] <;> ring
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection]
      · intro y
        ext <;> simp [BandPackingSymmetryAffineVectorAction, GaussianReflection,
          BandPackingSymmetryReversesOrientation, affineQuarter,
          GaussianQuarterTurn]
  | comp a b iha ihb =>
      refine ⟨?_, ?_, ?_⟩
      · intro y z
        change BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b (y + z)) = _
        rw [ihb.1, iha.1]
        rfl
      · intro y
        change BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b (-y)) = _
        rw [ihb.2.1, iha.2.1]
        rfl
      · intro y
        change BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b (affineQuarter y)) = _
        rw [ihb.2.2]
        cases ha : BandPackingSymmetryReversesOrientation a <;>
          cases hb : BandPackingSymmetryReversesOrientation b <;>
          simp [ha, hb, iha.2.1, iha.2.2,
            BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryAffineVectorAction]

end ApollonianSuperharmonic

end
