/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityPotentialCompact
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Decaying potential tests for pressure duality

The derivative bounds in `RieszPressurePotentialDecay` are the componentwise
form of `eq:riesz-potential-decay`.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Uniform spatial decay and compact time support for the potential tests in
`lem:riesz-duality`. -/
structure RieszPressurePotentialDecay (ψ : Vec3 × ℝ → ℝ) : Prop where
  timeSupport : ∃ K : Set ℝ, IsCompact K ∧ ∀ t ∉ K, ∀ x, ψ (x, t) = 0
  value_bound : ∃ C ≥ 0, ∀ z, |ψ z| ≤ C * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))
  gradient_bound : ∃ C ≥ 0, ∀ i z,
    |rieszPressureJointDirection ψ i z| ≤
      C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))
  hessian_bound : ∃ C ≥ 0, ∀ i j z,
    |rieszPressureJointHessian ψ i j z| ≤
      C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ))

/-- The common space-time (L^3) majorant for derivatives of a decaying
potential test, used by `lem:riesz-duality`. -/
@[expose]
def rieszPressurePotentialSpatialProfile (K : Set ℝ) (z : Vec3 × ℝ) : ℝ :=
  K.indicator (fun _ => (1 : ℝ)) z.2 *
    (1 + ‖z.1‖) ^ (-(4 : ℝ))

/-- The potential-test majorant is in space-time (L^3), used by
`lem:riesz-duality`. -/
theorem rieszPressurePotentialSpatialProfile_memLp3
    {K : Set ℝ} (hK : IsCompact K) :
    MemLp (rieszPressurePotentialSpatialProfile K) (ENNReal.ofReal (3 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
  have htime : MemLp (K.indicator (fun _ : ℝ => (1 : ℝ)))
      (ENNReal.ofReal (3 : ℝ)) (volume : Measure ℝ) :=
    memLp_indicator_const (ENNReal.ofReal (3 : ℝ)) hK.measurableSet (1 : ℝ)
      (Or.inr hK.measure_lt_top.ne)
  have hthree : (ENNReal.ofReal (3 : ℝ)).toReal = 3 := by norm_num
  let b : Vec3 → ℝ := fun x => (1 + ‖x‖) ^ (-(4 : ℝ))
  have hspace : MemLp b (ENNReal.ofReal (3 : ℝ)) (volume : Measure Vec3) := by
    have hmeas : AEStronglyMeasurable b (volume : Measure Vec3) := by
      exact (by fun_prop : Measurable b).aestronglyMeasurable
    have hpower : Integrable (fun x : Vec3 => ‖b x‖ ^ (3 : ℝ))
        (volume : Measure Vec3) := by
      have hbracket : Integrable (fun x : Vec3 =>
          (1 + ‖x‖) ^ (-(12 : ℝ))) (volume : Measure Vec3) := by
        apply integrable_one_add_norm
        rw [Module.finrank_fin_fun]
        norm_num
      convert hbracket using 1
      ext x
      dsimp [b]
      rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + ‖x‖) (-(4 : ℝ)) (3 : ℝ)]
      norm_num
    have hp0 : ENNReal.ofReal (3 : ℝ) ≠ 0 := by norm_num
    exact (integrable_norm_rpow_iff hmeas hp0 ENNReal.ofReal_ne_top).mp
      (by simpa only [hthree] using hpower)
  have htimePower : Integrable
      (fun t : ℝ => ‖K.indicator (fun _ : ℝ => (1 : ℝ)) t‖ ^
        (ENNReal.ofReal (3 : ℝ)).toReal)
      (volume : Measure ℝ) := htime.integrable_norm_rpow (by norm_num) (by norm_num)
  have hspacePower : Integrable (fun x : Vec3 => ‖b x‖ ^
      (ENNReal.ofReal (3 : ℝ)).toReal)
      (volume : Measure Vec3) := hspace.integrable_norm_rpow (by norm_num) (by norm_num)
  have hprofilePower : Integrable
      (fun z : Vec3 × ℝ => ‖rieszPressurePotentialSpatialProfile K z‖ ^
        (ENNReal.ofReal (3 : ℝ)).toReal)
      (volume : Measure (Vec3 × ℝ)) := by
    rw [Measure.volume_eq_prod]
    convert hspacePower.mul_prod htimePower using 1
    ext z
    by_cases hz : z.2 ∈ K <;> simp [rieszPressurePotentialSpatialProfile, b, hz]
  have hp0 : ENNReal.ofReal (3 : ℝ) ≠ 0 := by norm_num
  have hprofileMeas : Measurable (rieszPressurePotentialSpatialProfile K) := by
    change Measurable (fun z : Vec3 × ℝ =>
      K.indicator (fun _ => (1 : ℝ)) z.2 * (1 + ‖z.1‖) ^ (-(4 : ℝ)))
    have hind : Measurable (K.indicator (fun _ : ℝ => (1 : ℝ))) :=
      Measurable.indicator measurable_const hK.measurableSet
    have hbracket : Measurable (fun z : Vec3 × ℝ =>
        (1 + ‖z.1‖) ^ (-(4 : ℝ))) := by fun_prop
    exact (hind.comp measurable_snd).mul hbracket
  exact (integrable_norm_rpow_iff hprofileMeas.aestronglyMeasurable hp0
    ENNReal.ofReal_ne_top).mp hprofilePower

/-- A continuous function with fourth-order spatial decay and compact time
support belongs to space-time (L^3), used by `lem:riesz-duality`. -/
theorem rieszPressurePotential_memLp3_of_decay
    {K : Set ℝ} (hK : IsCompact K) {f : Vec3 × ℝ → ℝ}
    (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    (hbound : ∀ z, |f z| ≤ C *
      (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ))) :
    MemLp f (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  have hprof := rieszPressurePotentialSpatialProfile_memLp3 hK
  apply hprof.of_le_mul (c := C) hf.aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z.2 ∈ K
  · have hprofile : rieszPressurePotentialSpatialProfile K z =
        (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
      simp [rieszPressurePotentialSpatialProfile, hz]
    have hnonneg : 0 ≤ (1 + ‖z.1‖) ^ (-(4 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have heucNorm := CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm z.1
    have hdecay : (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) ≤
        (1 + ‖z.1‖) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by linarith only [heucNorm]) (by norm_num)
    rw [Real.norm_eq_abs, hprofile, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact (hbound z).trans
      (mul_le_mul_of_nonneg_left hdecay hC)
  · have hzero' := hzero z.2 hz z.1
    simp only [hzero', Real.norm_eq_abs, abs_zero]
    exact mul_nonneg hC (abs_nonneg _)

private theorem rieszPressureJointLaplacian_zero_outside_time_support
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set ℝ} (hzero : ∀ t ∉ K, ∀ x, ψ (x, t) = 0)
    {z : Vec3 × ℝ} (hz : z.2 ∉ K) :
    rieszPressureJointLaplacian ψ z = 0 := by
  have hslice : (fun x : Vec3 => ψ (x, z.2)) = fun _ => (0 : ℝ) := by
    funext x
    exact hzero z.2 hz x
  rw [← rieszPressure_sliceLaplacian_eq_joint hψ z]
  change CKN.spatialLaplacian (fun x : Vec3 => ψ (x, z.2)) z.1 = 0
  rw [hslice]
  have hdir (i : Fin 3) :
      CKN.spatialDeriv (fun _ : Vec3 => (0 : ℝ)) i = fun _ => 0 := by
    funext x
    simp [CKN.spatialDeriv]
  simp [CKN.spatialLaplacian, hdir]

/-- The spatial Laplacian test in `lem:riesz-duality` belongs to space-time
`L^3`, used by the noncompact-potential identity. -/
theorem rieszPressureJointLaplacian_memLp3
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ) :
    MemLp (rieszPressureJointLaplacian ψ) (ENNReal.ofReal (3 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
  obtain ⟨K, hK, hzero⟩ := hdecay.timeSupport
  obtain ⟨C, hC, hbound⟩ := hdecay.hessian_bound
  have hboundLap (z : Vec3 × ℝ) :
      |rieszPressureJointLaplacian ψ z| ≤
        (3 * C) * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
    rw [rieszPressureJointLaplacian]
    calc
      |∑ i : Fin 3, rieszPressureJointHessian ψ i i z| ≤
          ∑ i : Fin 3, |rieszPressureJointHessian ψ i i z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3,
          C * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hbound i i z
      _ = (3 * C) * (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hC' : 0 ≤ 3 * C := mul_nonneg (by norm_num) hC
  exact rieszPressurePotential_memLp3_of_decay hK
    ((rieszPressureJointLaplacian_contDiff hψ).continuous) (3 * C) hC'
    (fun t ht x => rieszPressureJointLaplacian_zero_outside_time_support hψ hzero ht)
    hboundLap

end CKN.Leray

end
