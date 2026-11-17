/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.FordRecursiveQuadruple
public import Mathlib.Init


/-!
# FordParentVectors

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace FordParentVectors

/-- Shared firstParent identity for FordParentVectors. -/
theorem firstParent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandVectors.1 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) = (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ :
            GaussianInt)) → ((∀ (j : Fin (3 : ℕ)), BandVectors.1 (FordRecursiveQuadruple P (0 :
            Fin (4 : ℕ))) (FordRecursiveQuadruple P j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            * BandVectors.1 (FordRecursiveQuadruple P j.succ) (FordRecursiveQuadruple P (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (FordRecursiveQuadruple P j.succ) (FordRecursiveQuadruple P (0 : Fin (4
            : ℕ)))) → (BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P)
            1) = ⟨-(P.q₁:Int),P.q⟩)) ) := by
  classical
  intro P h10 hf
  have h := (hf 0).1
  change BandVectors.1 ((FordRecursiveQuadruple P) 0)
    ((FordRecursiveQuadruple P) 1) = (⟨0,1⟩ : GaussianInt) *
      BandVectors.1 ((FordRecursiveQuadruple P) 1) ((FordRecursiveQuadruple P) 0) at h
  rw [h10] at h
  exact h.trans (by ext <;> simp)

/-- Shared secondParent identity for FordParentVectors. -/
theorem secondParent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandVectors.1 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) = (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ :
            GaussianInt)) → ((∀ (j : Fin (3 : ℕ)), BandVectors.1 (FordRecursiveQuadruple P (0 :
            Fin (4 : ℕ))) (FordRecursiveQuadruple P j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            * BandVectors.1 (FordRecursiveQuadruple P j.succ) (FordRecursiveQuadruple P (0 : Fin
            (4 : ℕ))) ∧ BandVectors.2 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (FordRecursiveQuadruple P j.succ) (FordRecursiveQuadruple P (0 : Fin (4
            : ℕ)))) → (BandVectors.1 ((FordRecursiveQuadruple P) 0) ((FordRecursiveQuadruple P)
            2) = ⟨-(P.q₂:Int),-(P.q:Int)⟩)) ) := by
  classical
  intro P h20 hf
  have h := (hf 1).1
  change BandVectors.1 ((FordRecursiveQuadruple P) 0)
    ((FordRecursiveQuadruple P) 2) = (⟨0,1⟩ : GaussianInt) *
      BandVectors.1 ((FordRecursiveQuadruple P) 2) ((FordRecursiveQuadruple P) 0) at h
  rw [h20] at h
  exact h.trans (by ext <;> simp)

end FordParentVectors
end ApollonianSuperharmonic

end
