/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCNormalizedEnergy

/-!
# Integrability of the weighted cutoff energy

The lower time cutoff removes the Gaussian weight singularity at time zero.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The cut off field and its first spatial derivative vanish through the
initial cutoff time. -/
theorem uc_cutoff_energy_zero_below
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (hz : z.2 ≤ ε) :
    ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v z = 0 ∧
    ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv z = 0 := by
  have hχ := ucInitialTimeCutoff_eq_zero hε hz
  have hζ : ucGaussianCutoff ρ hρ ε z = 0 := by
    simp [ucGaussianCutoff, ucCutoffScalar, hχ]
  have hpartial (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε z j]
    simp [ucGaussianTimeCutoff, hχ]
  constructor
  · change (ucGaussianCutoff ρ hρ ε z) • v z = 0
    simp [hζ]
  · funext i j
    change ucGaussianCutoff ρ hρ ε z * Dv z i j +
      v z i * spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0
    simp [hζ, hpartial]

/-- The Gaussian weight times the cutoff field energy is integrable on the
normalized cylinder for each positive initial cutoff time. -/
theorem uc_weighted_cutoff_energy_integrable
    {ρ ε a : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (ha : 0 ≤ a)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    (let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v
    let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv
    IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z))
      (ucCylinder ρ) volume) := by
  dsimp
  let Z := ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v
  let DZ := ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv
  let D2Z := ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v
  let DtZ := ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dtv
  obtain ⟨hweakZ, _, _, hL2Z⟩ :=
    ucGaussianCutoff_admissible hρ hε hweak hL2
  change HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
    Z DZ D2Z DtZ at hweakZ
  change (∫⁻ z in ucCylinder ρ,
      ‖Z z‖ₑ ^ (2 : ℝ) + ‖DZ z‖ₑ ^ (2 : ℝ) +
        ‖D2Z z‖ₑ ^ (2 : ℝ) + ‖DtZ z‖ₑ ^ (2 : ℝ)) < ⊤ at hL2Z
  obtain ⟨hZInt, hDZInt⟩ := uc_normalized_energy_integrable hweakZ hL2Z
  let G : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z
  have hGInt : IntegrableOn G (ucCylinder ρ) volume := hZInt.add hDZInt
  let F : ParabolicPoint → ℝ := fun z =>
    if ε < z.2 then ucGaussianWeight a z else 0
  let B : ℝ := (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (ucGaussianWeight_measurable a).ite
      (measurableSet_Ioi.preimage measurable_snd) measurable_const
  have hFbound : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)), ‖F z‖ ≤ B := by
    have hQmeas : MeasurableSet (ucCylinder ρ) :=
      (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    by_cases ht : ε < z.2
    · have h0 := ucGaussianWeight_nonneg a (hε.trans ht)
      have hle := ucGaussianWeight_le_after hε ha ht.le hz.2.2.le
      simpa [F, ht, Real.norm_eq_abs, abs_of_nonneg h0, B] using hle
    · simp [F, ht, hB]
  have hprod : IntegrableOn (fun z => F z * G z)
      (ucCylinder ρ) volume := by
    have h := hGInt.mul_bdd hFmeas.aestronglyMeasurable hFbound
    change Integrable (fun z => F z * G z) (volume.restrict (ucCylinder ρ))
    convert h using 1
    funext z
    ring
  have heq (z : ParabolicPoint) : F z * G z =
      ucGaussianWeight a z *
        (vec3EuclideanNorm (Z z) ^ 2 + spatialGradientSq Z DZ z) := by
    change F z * G z = ucGaussianWeight a z * G z
    by_cases ht : ε < z.2
    · simp [F, ht]
    · have hzero := uc_cutoff_energy_zero_below hρ hε v Dv z (le_of_not_gt ht)
      change Z z = 0 ∧ DZ z = 0 at hzero
      rcases hzero with ⟨hZ0, hDZ0⟩
      simp [F, ht, G, hZ0, hDZ0, spatialGradientSq, vec3EuclideanNorm_zero]
  exact hprod.congr (Filter.Eventually.of_forall heq)

end ESS
