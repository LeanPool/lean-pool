/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

-- [TABLET NODE: P4994T6UnitCoordinates]

/-!
# P4994T6UnitCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The additive coordinate isomorphism $K_\epsilon:\mathbb Z[i]\to\mathbb Z^2$
is $K_{\mathsf{standard}}(z)=(\Re z,\Im z)$ and
$K_{\mathsf{rotated}}(z)=(\Im z,-\Re z)$.
These are the coordinates in the positive bases $(1,i)$ and $(i,-1)$,
respectively; standard is the Boolean true and rotated is false.
-/
def P4994T6UnitCoordinates (orientation : Bool) : GaussianInt ≃+ (Int × Int) :=
-- BODY
  if orientation then
    { toFun := fun z => (z.re, z.im)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro p; rfl
      map_add' := by intro z w; rfl }
  else
    { toFun := fun z => (z.im, -z.re)
      invFun := fun p => ⟨-p.2, p.1⟩
      left_inv := by intro z; ext <;> simp
      right_inv := by intro p; ext <;> simp
      map_add' := by intro z w; ext <;> simp; omega }

end ApollonianSuperharmonic

end
