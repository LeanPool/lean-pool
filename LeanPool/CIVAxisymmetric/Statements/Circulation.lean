/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Circulation

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- The circulation `Γ = r u_θ = x₁ u₂ - x₂ u₁`. -/
@[expose] def circulation (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  z.1 0 * u z 1 - z.1 1 * u z 0

end CIV
