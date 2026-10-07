/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.MeridionalPartial
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Anisotropic Bounds

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The anisotropic Type II bounds `eq:aniso:bounds` (for the angular mean,
`eq:interior:mean:bounds`) with exponent `h` and constant `C`, for all derivatives of
total order at most two, read on the meridional plane (design note R4). -/
@[expose] def AnisotropicBounds (C h : ℝ) (v : ParabolicPoint → Vec3) : Prop :=
  ∀ a b : ℕ, a + b ≤ 2 → ∀ x₁ x₃ t : ℝ, (meridional x₁ x₃, t) ∈ unitCylinder →
    |meridionalPartial (fun z => v z 0) a b (meridional x₁ x₃, t)| ≤
        C * (-t) ^ (-(1 / 2 : ℝ) - a / 2 - (1 / 2 - h) * b) ∧
      |meridionalPartial (fun z => v z 2) a b (meridional x₁ x₃, t)| +
        |meridionalPartial (fun z => v z 1) a b (meridional x₁ x₃, t)| ≤
        C * (-t) ^ (-(1 / 2 : ℝ) - h - a / 2 - (1 / 2 - h) * b)

end CIV
