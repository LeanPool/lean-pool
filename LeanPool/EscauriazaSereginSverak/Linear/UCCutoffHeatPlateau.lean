/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffPlateau

/-!
# Heat operator on the Gaussian cutoff plateau

All cutoff derivatives vanish in the interior after the initial time
transition, leaving the original weak heat operator.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- On the inner region, the only cutoff error comes from the initial
time transition. -/
theorem ucGaussianCutoff_heat_eq_on_inner
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ)
    (v : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dw D2w Dtw z =
      (ucInitialTimeCutoff ε z.2) • ucWeakHeatVector D2w Dtw z +
        (deriv (ucInitialTimeCutoff ε) z.2) • v z := by
  have hθ : ucSpatialCutoff ρ hρ z.1 = 1 :=
    ucSpatialCutoff_eq_one hρ hz.1
  have hη : ucFinalTimeCutoff z.2 = 1 :=
    ucFinalTimeCutoff_eq_one hz.2.2.le
  have hηderiv : deriv ucFinalTimeCutoff z.2 = 0 :=
    ucFinalTimeCutoff_deriv_zero hz.2.2
  have hcut : ucCutoffScalar (ucSpatialCutoff ρ hρ)
      ucFinalTimeCutoff (ucInitialTimeCutoff ε) z =
      ucInitialTimeCutoff ε z.2 := by
    simp [ucCutoffScalar, hθ, hη]
  have htime : timePartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
      ucFinalTimeCutoff (ucInitialTimeCutoff ε)) z =
      deriv (ucInitialTimeCutoff ε) z.2 := by
    change timePartial (ucGaussianCutoff ρ hρ ε) z = _
    rw [ucGaussianCutoff_timePartial hρ ε z,
      ucGaussianTimeCutoff_deriv, hθ, hηderiv, hη]
    ring
  have hgrad : ∀ j : Fin 3, spatialPartial (ucCutoffScalar
      (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε)) j z = 0 := by
    intro j
    exact ucGaussianCutoff_spatialPartial_zero_on_inner hρ ε hz j
  have hhess : ∀ j : Fin 3, spatialSecondPartial (ucCutoffScalar
      (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε)) j j z = 0 := by
    intro j
    exact ucGaussianCutoff_spatialSecondPartial_zero_on_inner hρ ε hz j j
  funext i
  simp [ucCutoffHeat, hcut, htime, hgrad, hhess,
    Pi.add_apply, Pi.smul_apply]


/-- The compact field equals the original field on the late interior. -/
theorem ucGaussianCutoff_field_eq_on_inner_late
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ)
    (hlate : 2 * ε < z.2) (v : ParabolicPoint → Vec3) :
    ucCutoffField (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v z = v z := by
  have hcut := ucGaussianCutoff_eq_one_on_inner hρ hε hz hlate.le
  change (ucGaussianCutoff ρ hρ ε z) • v z = v z
  rw [hcut, one_smul]

/-- The first weak derivative data agree on the late interior. -/
theorem ucGaussianCutoff_dw_eq_on_inner_late
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ)
    (hlate : 2 * ε < z.2)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3) :
    ucCutoffDw (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv z = Dv z := by
  have hcut := ucGaussianCutoff_eq_one_on_inner hρ hε hz hlate.le
  change ucCutoffScalar (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) z = 1 at hcut
  have hgrad (j : Fin 3) :
      spatialPartial (ucCutoffScalar (ucSpatialCutoff ρ hρ)
        ucFinalTimeCutoff (ucInitialTimeCutoff ε)) j z = 0 :=
    ucGaussianCutoff_spatialPartial_zero_on_inner hρ ε hz j
  funext i j
  simp [ucCutoffDw, hcut, hgrad]


/-- The initial cutoff derivative vanishes before its transition. -/
theorem ucInitialTimeCutoff_deriv_zero_below
    {ε s : ℝ} (hε : 0 < ε) (hs : s < ε) :
    deriv (ucInitialTimeCutoff ε) s = 0 := by
  have heq : ucInitialTimeCutoff ε =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hs] with t ht
    exact ucInitialTimeCutoff_eq_zero hε ht.le
  rw [heq.deriv_eq]
  simp

/-- The initial cutoff derivative is confined to the early time interval. -/
theorem ucInitialTimeCutoff_abs_deriv_le_early
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (ucInitialTimeCutoff ε) s| ≤
      if ε ≤ s ∧ s ≤ 2 * ε then 8 / ε else 0 := by
  by_cases hslo : ε ≤ s
  · by_cases hshi : s ≤ 2 * ε
    · simpa [hslo, hshi] using ucInitialTimeCutoff_abs_deriv_le hε s
    · simp [hslo, hshi,
        ucInitialTimeCutoff_deriv_zero hε (lt_of_not_ge hshi)]
  · simp [hslo,
      ucInitialTimeCutoff_deriv_zero_below hε (lt_of_not_ge hslo)]


end ESS
