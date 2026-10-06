/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Main.CarlemanGaussian
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Gaussian Carleman inequality

-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Carleman inequality with a Gaussian weight (`prop:carleman-gauss`; ESS
Proposition 6.1). -/
theorem carlemanGaussian :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ a : ℝ, 0 < a → ∀ w : ParabolicPoint → Vec3,
      w ∈ spaceTimeTestFunction (V := Vec3) univ (Ioo 0 2) →
      ∫ z in spaceTimeSet univ (Ioo 0 2),
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
            (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
              spatialGradientSq w (spatialGradient w) z) ≤
        c₀ * ∫ z in spaceTimeSet univ (Ioo 0 2),
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
            vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
              ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 :=
by exact ESS.Main.carlemanGaussian

end ESS
