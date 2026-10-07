/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Meridional

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- The point `(x₁, 0, x₃)` of the meridional plane `{x₂ = 0}`. -/
@[expose] def meridional (x₁ x₃ : ℝ) : Vec3 := ![x₁, 0, x₃]

end CIV
