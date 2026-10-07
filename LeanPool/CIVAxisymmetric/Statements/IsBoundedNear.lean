/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Is Bounded Near

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- `u` is bounded near `x` if it is bounded, by some constant, on some backward
parabolic neighbourhood of `x` whose time window has length the square of its spatial
radius: `∃ r, M`, `|u| ≤ M` on `B(x, r) × (-r², 0)`. This is the scale-invariant relative
of `BoundedNearOrigin`, centred at a general point, that names the failure set of
`lem:aniso:annulus` (design note R12). -/
@[expose] def IsBoundedNear (u : ParabolicPoint → Vec3) (x : Vec3) : Prop :=
  ∃ r M : ℝ, 0 < r ∧
    ∀ y ∈ vec3Ball x r, ∀ t ∈ Ioo (-(r ^ 2)) 0, vec3EuclideanNorm (u (y, t)) ≤ M

end CIV
