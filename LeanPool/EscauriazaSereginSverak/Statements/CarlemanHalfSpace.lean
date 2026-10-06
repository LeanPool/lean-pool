/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.CarlemanHalfSpace
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Carleman inequality on a half-space with an anisotropic weight
(`prop:carleman-halfspace`; ESS Proposition 6.2). -/
theorem carlemanHalfSpace :
    ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ a : ℝ, a₀ < a → ∀ w : ParabolicPoint → Vec3,
        w ∈ spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1) →
        ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
                spatialGradientSq w (spatialGradient w) z / z.2) ≤
          c * ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
                ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 :=
by exact ESS.Main.carlemanHalfSpace

end ESS
