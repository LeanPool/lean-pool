/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussExplicit

/-!
# The Gaussian Carleman estimate

`prop:carleman-gauss`: the existential statement, witnessed by the
explicit constant of `ESS.carlemanGaussian_explicit`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

namespace ESS.Main

/-- Gaussian Carleman inequality on the positive-time cylinder
(`prop:carleman-gauss`). -/
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
  ⟨Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6), by positivity,
    fun a ha w hw => ESS.carlemanGaussian_explicit a ha w hw⟩

end ESS.Main
