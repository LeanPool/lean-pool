/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfSpaceProof

/-!
# Assembly of the half-space Carleman inequality

-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.Main

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
                ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  apply halfSpace_estimate_of_pointwise_bound
  intro α hα hα1 a ha v z hz
  have hpoint := halfSpacePhase_commutatorDensity_lower
    a α v hz ha hα hα1
  calc
    (a * (2 * α - 1) * halfSpaceMassFactor α z +
        halfSpaceNormalEnergy a α z) * v z ^ 2 =
        a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α * v z ^ 2 +
          z.2 * halfSpaceGradientTwo a α z ^ 2 * v z ^ 2 := by
      dsimp [halfSpaceMassFactor, halfSpaceNormalEnergy]
      ring
    _ ≤ carlemanCommutatorDensity (halfSpacePhase a α) v z := hpoint

end ESS.Main
