/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.RotZ
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Angular Mean Scalar

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open CKN.Foundation.Parabolic


noncomputable section

namespace CIV

/-- The angular mean of a scalar field, `(2π)⁻¹ ∫₀^{2π} g(Q_φ⁻¹ x, t) dφ`. -/
@[expose] def angularMeanScalar (g : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), g (rotZ (-φ) z.1, z.2)

end CIV
