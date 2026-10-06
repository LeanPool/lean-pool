/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCollarUniform

/-!
# Initial transition integral

The time indicator in the cutoff heat error is precisely integration over
the initial transition interval.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped Classical Topology

noncomputable section

namespace ESS

/-- The indicator form of the early cutoff error equals the weighted
integral over its time transition interval. -/
theorem uc_initial_indicator_integral_eq
    {ρ ε a : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (v : ParabolicPoint → Vec3) :
    (∫ z in ucCylinder ρ, ucGaussianWeight a z *
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0)) =
      ∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
        ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2 := by
  let S : Set ParabolicPoint := {z | ε ≤ z.2 ∧ z.2 ≤ 2 * ε}
  let F : ParabolicPoint → ℝ := fun z =>
    ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2
  have hSmeas : MeasurableSet S := by
    change MeasurableSet (Prod.snd ⁻¹' Icc ε (2 * ε))
    exact measurableSet_Icc.preimage measurable_snd
  have hfunc : (fun z : ParabolicPoint => ucGaussianWeight a z *
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
        vec3EuclideanNorm (v z) ^ 2 else 0)) = S.indicator F := by
    funext z
    by_cases hz : ε ≤ z.2 ∧ z.2 ≤ 2 * ε <;>
      simp [S, F, Set.indicator, hz]
  rw [hfunc, setIntegral_indicator hSmeas]
  have hset : ucCylinder ρ ∩ S =
      spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)) := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1.1, hz.2⟩
    · intro hz
      have h2ε : 2 * ε < 2 := by linarith only [hε1]
      exact ⟨⟨hz.1, hε.trans_le hz.2.1,
        hz.2.2.trans_lt h2ε⟩, hz.2⟩
  rw [hset]

/-- The initial cutoff error in the absorbed estimate vanishes as the
cutoff reaches time zero. -/
theorem uc_initial_indicator_error_tendsto_zero
    {ρ a : ℝ} (hρ : 4 ≤ ρ) (ha : 0 ≤ a)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in ucCylinder ρ,
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hflat : UCIntegralFlatness 0 ρ 2 v) :
    Tendsto (fun ε : ℝ => (192 / ε ^ 2) *
      (∫ z in ucCylinder ρ, ucGaussianWeight a z *
        (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then
          vec3EuclideanNorm (v z) ^ 2 else 0)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hVInt := (uc_normalized_energy_integrable hweak hL2).1
  have hbase := uc_initial_time_error_tendsto_zero ρ hρ a ha v hVInt hflat
  have hlim : Tendsto (fun ε : ℝ => 192 *
      (ε ^ (-(2 : ℝ)) *
        (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Icc ε (2 * ε)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul 192
  apply hlim.congr'
  have hε1 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hε1] with ε hε hε1
  rw [uc_initial_indicator_integral_eq hε hε1 v]
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two]
  have hεpos : 0 < ε := hε
  field_simp [hεpos.ne']

end ESS
