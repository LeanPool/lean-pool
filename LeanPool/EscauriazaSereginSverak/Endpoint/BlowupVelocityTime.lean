/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupMassLp
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Blowup Velocity Time

Velocity estimates for the rescaled sequence used in endpoint compactness.
-/

public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- Tonelli identifies the time-integrated spatial cubic norm with the
space-time cubic mass. -/
theorem blowupScalarTimeThree_eq
    {Ω : Set Vec3} {J : Set ℝ}
    (g : ParabolicPoint → ℝ)
    (hg : AEStronglyMeasurable (fun z : Vec3 × ℝ => g (z.1, z.2))
      ((volume.restrict Ω).prod (volume.restrict J))) :
    (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => g (x, t)) (3 : ℝ≥0∞)
        (volume.restrict Ω) ^ (3 : ℝ)) =
      ∫⁻ z, ENNReal.ofReal |g z| ^ (3 : ℝ)
        ∂((volume.restrict Ω).prod (volume.restrict J)) := by
  let μx := volume.restrict Ω
  let μt := volume.restrict J
  have hslice := hg.prodMk_right
  have hpow : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => g (x, t)) (3 : ℝ≥0∞) μx ^ (3 : ℝ) =
        ∫⁻ x, ENNReal.ofReal |g (x, t)| ^ (3 : ℝ) ∂μx := by
    filter_upwards [hslice] with t ht
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (p := (3 : NNReal)) (f := fun x : Vec3 => g (x, t))
      (by norm_num) ht
    norm_num at h ⊢
    simpa [Real.enorm_eq_ofReal_abs] using h
  have hmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal |g z| ^ (3 : ℝ))
      (μx.prod μt) := by
    simpa only [μx, μt, Real.enorm_eq_ofReal_abs, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hg.enorm)
  calc
    (∫⁻ t in J,
      eLpNorm (fun x : Vec3 => g (x, t)) (3 : ℝ≥0∞)
        (volume.restrict Ω) ^ (3 : ℝ)) =
      ∫⁻ t, ∫⁻ x, ENNReal.ofReal |g (x, t)| ^ (3 : ℝ) ∂μx ∂μt := by
        exact lintegral_congr_ae hpow
    _ = ∫⁻ z, ENNReal.ofReal |g z| ^ (3 : ℝ)
        ∂(μx.prod μt) := (lintegral_prod_symm _ hmeas).symm
    _ = _ := rfl

/-- A source-time uniform whole-space velocity bound persists on a rescaled
past time interval. -/
theorem blowupRescaledVelocity_slice_bound_ae
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (J : Set ℝ)
    (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => u (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,s))) 3 volume ≤ M) :
    ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x : Vec3 =>
        vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u (x,t)))
        3 volume ≤ M := by
  have hpull := blowup_ae_time_pullback_on r t₀ hr
    (Ioo (-1 : ℝ) 0) J measurableSet_Ioo hJ
    (fun s => AEStronglyMeasurable (fun x : Vec3 => u (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,s))) 3 volume ≤ M)
    hsource
  filter_upwards [hpull] with t ht
  have heq (x : Vec3) :
      parabolicRescaleVelocity x₀ t₀ r u (x,t) =
        r • u (x₀ + r • x, CKN.scalingTime r t₀ t) := by
    simp [parabolicRescaleVelocity, CKN.scalingTime,
      parabolicTranslate, parabolicScale]
  simp_rw [heq]
  exact (blowup_rescaled_velocitySlice_eLpNorm_three_eq
    (fun x => u (x, CKN.scalingTime r t₀ t)) ht.1 x₀ r hr).le.trans ht.2

/-- The rescaled velocity has a uniform whole-space cubic mass on a finite
past time interval. -/
theorem blowupRescaledVelocity_spaceTime_mass_bound
    (u : ParabolicPoint → Vec3) (x₀ : Vec3) (t₀ r : ℝ)
    (hr : 0 < r) (J : Set ℝ)
    (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => u (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,s))) 3 volume ≤ M)
    (hjoint : AEStronglyMeasurable
      (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u (z.1,z.2)))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J))) :
    (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal
        (vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u z)) ^ (3 : ℝ)
      ∂((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J))) ≤
      volume J * M ^ (3 : ℝ) := by
  let g : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u z)
  have hslice := blowupRescaledVelocity_slice_bound_ae
    u x₀ t₀ r hr J hJ M hsource
  have htime :
      (∫⁻ t in J,
        eLpNorm (fun x : Vec3 => g (x,t)) 3 volume ^ (3 : ℝ)) ≤
          volume J * M ^ (3 : ℝ) := by
    calc
      _ ≤ ∫⁻ _t in J, M ^ (3 : ℝ) := by
        apply lintegral_mono_ae
        filter_upwards [hslice] with t ht
        exact ENNReal.rpow_le_rpow ht (by norm_num)
      _ = volume J * M ^ (3 : ℝ) := by
        rw [setLIntegral_const]
        exact mul_comm _ _
  have htonelli := blowupScalarTimeThree_eq
    (Ω := (Set.univ : Set Vec3)) (J := J) g hjoint
  have heq :
      (∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal (g (z.1,z.2)) ^ (3 : ℝ)
          ∂((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J))) =
      ∫⁻ t in J, eLpNorm (fun x : Vec3 => g (x,t)) 3 volume ^ (3 : ℝ) := by
    simpa only [Measure.restrict_univ, g,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      using htonelli.symm
  change (∫⁻ z : Vec3 × ℝ,
    ENNReal.ofReal (g (z.1,z.2)) ^ (3 : ℝ)
      ∂((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J))) ≤
    volume J * M ^ (3 : ℝ)
  exact heq.trans_le htime

end ESS
