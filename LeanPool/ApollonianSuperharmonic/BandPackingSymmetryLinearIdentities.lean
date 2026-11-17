/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetry
public import Mathlib.Init


/-!
# BandPackingSymmetryLinearIdentities

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandPackingSymmetryLinearIdentities

/-- The real linear part of a packing symmetry respects subtraction and scaling. -/
theorem linearity :
    let R : BandPackingSymmetry → (Real × Real) → (Real × Real) :=
      BandPackingSymmetry.rec (fun p => p) (fun p => (-p.2, p.1))
        (fun p => (-p.1, p.2)) (fun _ p => p) (fun _ _ f k p => f (k p))
    (∀ h p t, R h (p - t) = R h p - R h t) ∧
      (∀ (h : BandPackingSymmetry) (c : Real) (p : Real × Real), R h (c • p) = c • R h p) := by
  classical
  intro R
  constructor
  · intro h p t
    induction h generalizing p t with
    | identity => rfl
    | negate => ext <;> simp [R]; ring
    | conjugate => ext <;> simp [R]; ring
    | shift w => rfl
    | comp h k ih ik => simp [R, ih, ik]
  · intro h c p
    induction h generalizing p with
    | identity => rfl
    | negate => ext <;> simp [R]
    | conjugate => ext <;> simp [R]
    | shift w => rfl
    | comp h k ih ik => simp [R, ih, ik]

end BandPackingSymmetryLinearIdentities
end ApollonianSuperharmonic

end
