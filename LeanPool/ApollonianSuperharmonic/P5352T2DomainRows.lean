/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.DiamondTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows

-- [TABLET NODE: P5352T2DomainRows]

/-!
# P5352T2DomainRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5352T2DomainRows (K : DiamondParameter) (z : GaussianInt) :
    (z ∈ FootprintVertices (DiamondTile K.1) ↔
      0 ≤ z.im ∧ z.im ≤ 2 * (K.1 : Int) ∧
      -(K.1 : Int) ≤ z.re ∧ z.re ≤ (K.1 : Int) ∧
      -z.im-1 ≤ z.re ∧ z.re ≤ z.im+1 ∧
      -(2*(K.1 : Int)-z.im+1) ≤ z.re ∧ z.re ≤ 2*(K.1 : Int)-z.im+1) ∧
    (z ∈ FootprintVertices (DiamondTile K.1) →
      DiamondOdometer K z =
        (Int.natAbs z.re : Int) * ((Int.natAbs z.re : Int)-1)/2 -
          (z.re-z.im)^2/4) := by
-- BODY
  obtain ⟨_, _, _, hf, _⟩ := DiamondTileOdometerRestriction K
  have bounds : (z ∈ FootprintVertices (DiamondTile K.1) ↔
      0 ≤ z.im ∧ z.im ≤ 2 * (K.1 : Int) ∧
      -(K.1 : Int) ≤ z.re ∧ z.re ≤ (K.1 : Int) ∧
      -z.im-1 ≤ z.re ∧ z.re ≤ z.im+1 ∧
      -(2*(K.1 : Int)-z.im+1) ≤ z.re ∧ z.re ≤ 2*(K.1 : Int)-z.im+1) := by
    rw [hf]
    change max (Int.natAbs z.re) (max (Int.natAbs (z.im-(K.1 : Int)))
      (Int.natAbs z.re + Int.natAbs (z.im-(K.1 : Int)) - 1)) ≤ K.1 ↔ _
    simp only [max_le_iff]
    have ha := Int.natCast_natAbs z.re
    have hb := Int.natCast_natAbs (z.im-(K.1 : Int))
    rcases le_total 0 z.re with h | h <;>
      rcases le_total 0 (z.im-(K.1 : Int)) with h' | h' <;>
      simp only [abs_of_nonneg, abs_of_nonpos, h, h'] at ha hb <;> omega
  refine ⟨bounds, ?_⟩
  intro hz
  exact (Classical.choose_spec (DiamondOdometerExistsUnique K)).1.2.2.2 z (hf ▸ hz)

end ApollonianSuperharmonic

end
