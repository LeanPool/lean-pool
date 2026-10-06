/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.RotField
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Angular Mean

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- The angular mean `𝒫u = (2π)⁻¹ ∫₀^{2π} ℛ_φ u dφ` of `eq:interior:average`, the
axisymmetric part of a field. -/
@[expose] def angularMean (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u z

end CIV
