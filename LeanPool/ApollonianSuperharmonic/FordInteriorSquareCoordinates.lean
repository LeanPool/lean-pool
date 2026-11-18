/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4062T1InteriorSquare
public import Mathlib.Init


/-!
# FordInteriorSquareCoordinates

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace FordInteriorSquareCoordinates

/-- Shared membership identity for FordInteriorSquareCoordinates. -/
theorem membership :
    ∀ (q : Nat), ∀ (x : GaussianInt), x ∈ P4062T1InteriorSquare q ↔
        1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (q : Int) - 1 := by
  classical
  intro q x
  unfold P4062T1InteriorSquare
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2,
      (Finset.mem_Icc.mp hb).1, (Finset.mem_Icc.mp hb).2⟩
  · intro h
    exact Finset.mem_image.mpr ⟨(x.re, x.im),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩,
        Finset.mem_Icc.mpr h.2.2⟩, by cases x; rfl⟩

end FordInteriorSquareCoordinates
end ApollonianSuperharmonic

end
