/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import Mathlib.Init
public import Mathlib.Order.SuccPred.Int


/-!
# DiamondFootprintCoordinates

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace DiamondFootprintCoordinates

/-- Shared coordinates identity for DiamondFootprintCoordinates. -/
theorem coordinates :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (z : GaussianInt), z ∈ FootprintVertices (DiamondTile k)
            ↔ (0 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑k : ℤ) ∧ -(↑k : ℤ) ≤ z.re ∧ z.re ≤ (↑k : ℤ) ∧
            -(z.im + (1 : ℤ)) ≤ z.re ∧ z.re ≤ z.im + (1 : ℤ) ∧ -((2 : ℤ) * (↑k : ℤ) - z.im + (1 :
            ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑k : ℤ) - z.im + (1 : ℤ))
    ) := by
  classical
  intro k hk z
  rw [(P4194T1DiamondVertexIncidence k hk z).1]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_succ,
    Fin.exists_fin_succ]
  rw [show LatticeVertexIncidentCell z 0 = z by rfl,
    show LatticeVertexIncidentCell z (Fin.succ 0) = z - 1 by rfl,
    show LatticeVertexIncidentCell z (Fin.succ 0).succ = z - 1 - ⟨0, 1⟩ by rfl,
    show LatticeVertexIncidentCell z (Fin.succ 0).succ.succ = z - ⟨0, 1⟩ by rfl]
  rw [(P4194T1DiamondCellRows k z).1,
    (P4194T1DiamondCellRows k (z - 1)).1,
    (P4194T1DiamondCellRows k (z - 1 - ⟨0, 1⟩)).1,
    (P4194T1DiamondCellRows k (z - ⟨0, 1⟩)).1]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
    ]
  simp []
  omega

end DiamondFootprintCoordinates
end ApollonianSuperharmonic

end
