/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCarlemanAbsorption

/-!
# Gaussian Carleman estimate in parabolic coordinates

The shared measure-preserving homeomorphism converts the Gaussian cutoff
estimate to CKN parabolic points.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The fixed Gaussian Carleman constant controls the cutoff in CKN
parabolic coordinates. -/
theorem uc_cutoff_carleman_parabolic_with_constant
    (c₀ : ℝ)
    (hgaussRaw : ∀ a : ℝ, 0 < a → ∀ v : ParabolicPoint → Vec3,
      v ∈ spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 2) →
      (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
        (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
          (a / z.2 * vec3EuclideanNorm (v z) ^ 2 +
            spatialGradientSq v (spatialGradient v) z)) ≤
        c₀ * (∫ z in spaceTimeSet Set.univ (Ioo 0 2),
          (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
            Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
            vec3EuclideanNorm (fun i =>
              timePartial (fun y => v y i) z +
                ∑ j, spatialSecondPartial (fun y => v y i) j j z) ^ 2))
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (a : ℝ) (ha : 0 < a) :
    let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
    let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv
    (∫ z in ucCylinder ρ,
      ucGaussianWeight a z * (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 +
        ucGaussianWeight a z * spatialGradientSq Z DZ z) ≤
      c₀ * (∫ z in ucCylinder ρ,
        ucGaussianWeight a z * vec3EuclideanNorm (LZ z) ^ 2) := by
  dsimp
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v Dtv
  have hcar := (uc_gaussian_cutoff_carleman_with_constant c₀ hgaussRaw
    hρ hε hweak hL2) a ha
  have hH := setIntegral_parabolic_to_product
    (Ω := vec3Ball 0 ρ) (I := Ioo (0 : ℝ) 2)
    (F := fun z => ucGaussianWeight a z * (a / z.2) *
      vec3EuclideanNorm (Z z) ^ 2 +
        ucGaussianWeight a z * spatialGradientSq Z DZ z)
  have hF := setIntegral_parabolic_to_product
    (Ω := vec3Ball 0 ρ) (I := Ioo (0 : ℝ) 2)
    (F := fun z => ucGaussianWeight a z * vec3EuclideanNorm (LZ z) ^ 2)
  change (∫ z in ucCylinder ρ,
      ucGaussianWeight a z * (a / z.2) * vec3EuclideanNorm (Z z) ^ 2 +
        ucGaussianWeight a z * spatialGradientSq Z DZ z) ≤
      c₀ * (∫ z in ucCylinder ρ,
        ucGaussianWeight a z * vec3EuclideanNorm (LZ z) ^ 2)
  simp only [ucCylinder]
  rw [hH, hF]
  convert hcar using 1
  · congr 1
  · rfl

end ESS
