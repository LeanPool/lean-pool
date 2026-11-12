/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.PrimitiveVectorOrientationUnique
public import LeanPool.ApollonianSuperharmonic.RecursiveVectorsExistUnique

-- [TABLET NODE: BandVectorOrientationDichotomy]

/-!
# BandVectorOrientationDichotomy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandVectorOrientationDichotomy
    (C D : CircleCoordinates) (hCD : BandTangency C D) :
    (((⟨0, 1⟩ : GaussianInt) * BandVectors.1 C D = BandVectors.1 D C) ∧
        (-⟨0, 1⟩ : GaussianInt) * BandVectors.2 C D = BandVectors.2 D C) ∨
      (((⟨0, 1⟩ : GaussianInt) * BandVectors.1 C D = -BandVectors.1 D C) ∧
        (-⟨0, 1⟩ : GaussianInt) * BandVectors.2 C D = -BandVectors.2 D C) := by
-- BODY
  have hsystem : RecursiveVectorSystem BandVectors := by
    simpa [BandVectors] using
      (Classical.choose_spec RecursiveVectorsExistUnique).1
  rcases (PrimitiveVectorOrientationUnique C D).2 hCD with ⟨_, horient⟩
  unfold Xor at horient
  rcases horient with ⟨hforward, _⟩ | ⟨hbackward, _⟩
  · left
    exact ⟨(hsystem.2.2.2 C D hforward).1.symm,
      (hsystem.2.2.2 C D hforward).2.symm⟩
  · right
    have hv := (hsystem.2.2.2 D C hbackward).1
    have ha := (hsystem.2.2.2 D C hbackward).2
    constructor
    · rw [hv]
      norm_num [Zsqrtd.ext_iff]
    · rw [ha]
      norm_num [Zsqrtd.ext_iff]

end ApollonianSuperharmonic

end
