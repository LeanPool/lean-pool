/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffHeatPlateau

/-!
# Carleman estimate for a compact Gaussian cutoff

The weak product identities make the cut off field admissible for the
Gaussian Carleman inequality.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A fixed Gaussian Carleman constant applies to the compact cutoff
of a normalized weak field. -/
theorem uc_gaussian_cutoff_carleman_with_constant
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
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
    let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv
    ∀ a : ℝ, 0 < a →
      (∫ z in vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2,
        ucGaussianWeight a z * (a / z.2) *
          vec3EuclideanNorm (Z (parabolicHomeomorph.symm z)) ^ 2 +
        ucGaussianWeight a z *
          ∑ i, ∑ j, DZ (parabolicHomeomorph.symm z) i j ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) ≤
        c₀ * (∫ z in vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2,
          ucGaussianWeight a z *
            vec3EuclideanNorm (LZ (parabolicHomeomorph.symm z)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
  dsimp
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
  let D2Z := ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v
  let DtZ := ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dtv
  obtain ⟨hweakZ, hcompact, hsupport, hL2Z⟩ :=
    ucGaussianCutoff_admissible hρ hε hweak hL2
  change HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
    Z DZ D2Z DtZ at hweakZ
  change HasCompactSupport Z at hcompact
  change tsupport Z ⊆ ucCylinder ρ at hsupport
  change (∫⁻ z in ucCylinder ρ,
      ‖Z z‖ₑ ^ (2 : ℝ) + ‖DZ z‖ₑ ^ (2 : ℝ) +
        ‖D2Z z‖ₑ ^ (2 : ℝ) + ‖DtZ z‖ₑ ^ (2 : ℝ)) < ⊤ at hL2Z
  have hcar := uc_gaussian_weak_carleman_ball_with_constant ρ c₀
    hgaussRaw hweakZ hcompact hsupport hL2Z
  intro a ha
  have h := hcar a ha
  convert h using 1
  · rfl
  · congr 1
    congr 1
    funext z
    congr 2
    apply congrArg vec3EuclideanNorm
    change ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv
      (parabolicHomeomorph.symm z) =
        ucWeakHeatVector D2Z DtZ (parabolicHomeomorph.symm z)
    exact ucCutoffHeat_eq_weakHeat _ _ _ _ _ _ _ _

/-- The Gaussian Carleman estimate applies to the compact cutoff of a
normalized weak field. -/
theorem uc_gaussian_cutoff_carleman
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
    let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ a : ℝ, 0 < a →
      (∫ z in vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2,
        ucGaussianWeight a z * (a / z.2) *
          vec3EuclideanNorm (Z (parabolicHomeomorph.symm z)) ^ 2 +
        ucGaussianWeight a z *
          ∑ i, ∑ j, DZ (parabolicHomeomorph.symm z) i j ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) ≤
        c₀ * (∫ z in vec3Ball 0 ρ ×ˢ Ioo (0 : ℝ) 2,
          ucGaussianWeight a z *
            vec3EuclideanNorm (LZ (parabolicHomeomorph.symm z)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
  obtain ⟨c₀, hc₀, hgaussRaw⟩ := ESS.carlemanGaussian
  exact ⟨c₀, hc₀,
    uc_gaussian_cutoff_carleman_with_constant c₀ hgaussRaw hρ hε
      hweak hL2⟩

end ESS
