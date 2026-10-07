/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCWeightedCutoffEnergy

/-!
# Integrability of the cutoff heat operator

The weak derivative fields give quadratic integrability of the heat
operator. The initial time cutoff permits its Gaussian weighting.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The cutoff heat operator vanishes before the initial time transition. -/
theorem uc_cutoff_heat_zero_before
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (hz : z.2 < ε) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
      (ucInitialTimeCutoff ε) v Dv D2v Dtv z = 0 := by
  have hχ : ucInitialTimeCutoff ε z.2 = 0 :=
    ucInitialTimeCutoff_eq_zero hε hz.le
  have hχ' : deriv (ucInitialTimeCutoff ε) z.2 = 0 :=
    ucInitialTimeCutoff_deriv_zero_below hε hz
  have hζ : ucGaussianCutoff ρ hρ ε z = 0 := by
    simp [ucGaussianCutoff, ucCutoffScalar, hχ]
  have hζt : timePartial (ucGaussianCutoff ρ hρ ε) z = 0 := by
    rw [ucGaussianCutoff_timePartial hρ ε z,
      ucGaussianTimeCutoff_deriv]
    simp [hχ, hχ']
  have hζsp (j : Fin 3) :
      spatialPartial (ucGaussianCutoff ρ hρ ε) j z = 0 := by
    rw [ucGaussianCutoff_spatialPartial hρ ε z j]
    simp [ucGaussianTimeCutoff, hχ]
  have hζsp2 (j : Fin 3) :
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z = 0 := by
    rw [ucGaussianCutoff_spatialSecondPartial hρ ε z j j]
    simp [ucGaussianTimeCutoff, hχ]
  funext i
  change ucGaussianCutoff ρ hρ ε z * ucWeakHeatVector D2v Dtv z i +
      (timePartial (ucGaussianCutoff ρ hρ ε) z +
        ∑ j : Fin 3, spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z) *
        v z i +
      2 * ∑ j : Fin 3,
        spatialPartial (ucGaussianCutoff ρ hρ ε) j z * Dv z i j = 0
  simp [hζ, hζt, hζsp, hζsp2]

/-- The heat operator of a compact cutoff has integrable quadratic norm on
the normalized cylinder. -/
theorem uc_cutoff_heat_sq_integrable
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
    IntegrableOn (fun z => vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ^ 2)
      (ucCylinder ρ) volume := by
  let μ := volume.restrict (ucCylinder ρ)
  let D2Z := ucCutoffD2 (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v
  let DtZ := ucCutoffDt (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dtv
  let LZ := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v Dtv
  obtain ⟨_, _, hD2Zm, hDtZm⟩ :=
    ucGaussianCutoff_l2_data hρ hε hweak hL2
  change MemLp D2Z 2 μ at hD2Zm
  change MemLp DtZ 2 μ at hDtZm
  have hLm : MemLp LZ 2 μ := by
    have hH : MemLp (ucWeakHeatVector D2Z DtZ) 2 μ := by
      apply MemLp.of_eval
      intro i
      have h0 := (((hD2Zm.eval i).eval (0 : Fin 3)).eval (0 : Fin 3))
      have h1 := (((hD2Zm.eval i).eval (1 : Fin 3)).eval (1 : Fin 3))
      have h2 := (((hD2Zm.eval i).eval (2 : Fin 3)).eval (2 : Fin 3))
      have hsum : MemLp (fun z => ∑ j : Fin 3, D2Z z i j j) 2 μ := by
        convert (h0.add h1).add h2 using 1
        funext z
        simp only [Fin.sum_univ_three, Pi.add_apply]
      convert (hDtZm.eval i).add hsum using 1
      funext z
      rfl
    convert hH using 1
    funext z
    exact ucCutoffHeat_eq_weakHeat _ _ _ _ _ _ _ z
  have hNormInt : Integrable (fun z => ‖LZ z‖ ^ 2) μ := by
    simpa only [μ] using hLm.integrable_norm_pow (p := 2) (by norm_num)
  have hEuMeas : AEStronglyMeasurable
      (fun z => vec3EuclideanNorm (LZ z) ^ 2) μ :=
    ((continuous_vec3EuclideanNorm).pow 2).comp_aestronglyMeasurable
      hLm.aestronglyMeasurable
  have hbound (z : ParabolicPoint) :
      vec3EuclideanNorm (LZ z) ^ 2 ≤ 3 * ‖LZ z‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm (LZ z)
    have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := by norm_num
    have hnn : 0 ≤ vec3EuclideanNorm (LZ z) := vec3EuclideanNorm_nonneg _
    have hn : 0 ≤ Real.sqrt 3 * ‖LZ z‖ := by positivity
    nlinarith only [h, hs, hnn, hn, sq_nonneg (‖LZ z‖)]
  have hEuInt : Integrable (fun z => vec3EuclideanNorm (LZ z) ^ 2) μ := by
    apply Integrable.mono' (hNormInt.const_mul 3) hEuMeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound z
  exact hEuInt

private theorem uc_integrableOn_gaussian_of_zero_before
    {ρ ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    {f : ParabolicPoint → ℝ}
    (hf : IntegrableOn f (ucCylinder ρ) volume)
    (hzero : ∀ z : ParabolicPoint, z.2 < ε → f z = 0) :
    IntegrableOn (fun z => ucGaussianWeight a z * f z)
      (ucCylinder ρ) volume := by
  let F : ParabolicPoint → ℝ := fun z =>
    if ε ≤ z.2 then ucGaussianWeight a z else 0
  let B : ℝ := (ε * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (ucGaussianWeight_measurable a).ite
      (measurableSet_Ici.preimage measurable_snd) measurable_const
  have hFbound : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)), ‖F z‖ ≤ B := by
    have hQmeas : MeasurableSet (ucCylinder ρ) :=
      (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    by_cases ht : ε ≤ z.2
    · have h0 := ucGaussianWeight_nonneg a (hε.trans_le ht)
      have hle := ucGaussianWeight_le_after hε ha ht hz.2.2.le
      simpa [F, ht, Real.norm_eq_abs, abs_of_nonneg h0, B] using hle
    · simp [F, ht, hB]
  have hprod : IntegrableOn (fun z => F z * f z)
      (ucCylinder ρ) volume := by
    have h := hf.mul_bdd hFmeas.aestronglyMeasurable hFbound
    change Integrable (fun z => F z * f z) (volume.restrict (ucCylinder ρ))
    convert h using 1
    funext z
    ring
  have heq (z : ParabolicPoint) : F z * f z =
      ucGaussianWeight a z * f z := by
    by_cases ht : ε ≤ z.2
    · simp [F, ht]
    · simp [F, ht, hzero z (lt_of_not_ge ht)]
  exact hprod.congr (Filter.Eventually.of_forall heq)

/-- The Gaussian weighted quadratic heat operator of the cutoff is
integrable for each positive initial cutoff time. -/
theorem uc_weighted_cutoff_heat_sq_integrable
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
    IntegrableOn (fun z => ucGaussianWeight a z *
      vec3EuclideanNorm
        (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ^ 2)
      (ucCylinder ρ) volume := by
  apply uc_integrableOn_gaussian_of_zero_before hε ha
    (uc_cutoff_heat_sq_integrable hρ hε hweak hL2)
  intro z hz
  rw [uc_cutoff_heat_zero_before hρ hε v Dv D2v Dtv z hz,
    vec3EuclideanNorm_zero]
  norm_num

/-- The weighted field mass in the initial cutoff transition is
integrable at every positive cutoff scale. -/
theorem uc_initial_transition_weighted_sq_integrable
    {ρ ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    IntegrableOn (fun z => ucGaussianWeight a z *
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0))
      (ucCylinder ρ) volume := by
  let S : Set ParabolicPoint := {z | ε ≤ z.2 ∧ z.2 ≤ 2 * ε}
  have hSmeas : MeasurableSet S := by
    change MeasurableSet (Prod.snd ⁻¹' Icc ε (2 * ε))
    exact measurableSet_Icc.preimage measurable_snd
  have hVInt := (uc_normalized_energy_integrable hweak hL2).1
  have hFInt : IntegrableOn (fun z =>
      if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0)
      (ucCylinder ρ) volume := by
    have h := hVInt.indicator hSmeas
    convert h using 1
    funext z
    by_cases hz : ε ≤ z.2 ∧ z.2 ≤ 2 * ε <;>
      simp [S, Set.indicator, hz]
  apply uc_integrableOn_gaussian_of_zero_before hε ha hFInt
  intro z hz
  have hnot : ¬(ε ≤ z.2 ∧ z.2 ≤ 2 * ε) := by
    intro h
    exact (not_le_of_gt hz) h.1
  simp [hnot]

end ESS
