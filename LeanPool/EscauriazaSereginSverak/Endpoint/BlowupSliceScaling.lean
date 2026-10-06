/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureRemainder
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic

public section
open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- Critical spatial `L^(3/2)` pressure mass is invariant under positive
Navier–Stokes spatial scaling. -/
theorem blowupPressureSlice_mass_eq
    (f : Vec3 → ℝ) (hf : AEStronglyMeasurable f (volume : Measure Vec3))
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    (∫⁻ x : Vec3, ENNReal.ofReal |r^2 * f (x₀ + r • x)| ^
      (3 / 2 : ℝ)) =
      ∫⁻ y : Vec3, ENNReal.ofReal |f y| ^ (3 / 2 : ℝ) := by
  have hscaled (x : Vec3) :
      ENNReal.ofReal |r^2 * f (x₀ + r • x)| ^ (3 / 2 : ℝ) =
        ENNReal.ofReal (r^3) *
          ENNReal.ofReal |f (x₀ + r • x)| ^ (3 / 2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg r),
      ENNReal.ofReal_mul (sq_nonneg r),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3/2),
      ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r)
        (by norm_num : (0 : ℝ) ≤ 3/2)]
    have hscalar : (r^2) ^ (3 / 2 : ℝ) = r^3 := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r 3,
        ← Real.rpow_mul hr.le]
      norm_num
    rw [hscalar]
  simp_rw [hscaled]
  rw [lintegral_const_mul' (ENNReal.ofReal (r^3)) _ ENNReal.ofReal_ne_top]
  let c : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 3)
  have hmap : Measure.map (CKN.scalingSpace r x₀) volume =
      c • (volume : Measure Vec3) := CKN.map_scalingSpace r hr x₀
  have hfm : AEStronglyMeasurable f (c • (volume : Measure Vec3)) :=
    hf.mono_ac Measure.smul_absolutelyContinuous
  have hpow : AEMeasurable
      (fun y : Vec3 => ENNReal.ofReal |f y| ^ (3 / 2 : ℝ))
      (Measure.map (CKN.scalingSpace r x₀) volume) := by
    rw [hmap]
    simpa only [Real.enorm_eq_ofReal_abs, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfm.enorm)
  have hscaleMeas : Measurable (CKN.scalingSpace r x₀) := by
    unfold CKN.scalingSpace
    fun_prop
  have hchange :
      (∫⁻ x : Vec3,
        ENNReal.ofReal |f (x₀ + r • x)| ^ (3 / 2 : ℝ)) =
        c * (∫⁻ y : Vec3,
          ENNReal.ofReal |f y| ^ (3 / 2 : ℝ)) := by
    have h := lintegral_map' hpow hscaleMeas.aemeasurable
    rw [hmap, lintegral_smul_measure] at h
    simpa only [CKN.scalingSpace, Function.comp_def, c, smul_eq_mul] using h.symm
  rw [hchange, ← mul_assoc]
  have hcoeff : ENNReal.ofReal (r^3) * c = 1 := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r^3)]
    have hreal : r^3 * r⁻¹ ^ 3 = 1 := by
      rw [← mul_pow]
      field_simp
    rw [hreal]
    norm_num
  rw [hcoeff, one_mul]

/-- Critical spatial `L³` velocity mass is invariant under positive
Navier–Stokes spatial scaling. -/
theorem blowupVelocityScalarSlice_mass_eq
    (f : Vec3 → ℝ) (hf : AEStronglyMeasurable f (volume : Measure Vec3))
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    (∫⁻ x : Vec3, ENNReal.ofReal |r * f (x₀ + r • x)| ^
      (3 : ℝ)) =
      ∫⁻ y : Vec3, ENNReal.ofReal |f y| ^ (3 : ℝ) := by
  have hscaled (x : Vec3) :
      ENNReal.ofReal |r * f (x₀ + r • x)| ^ (3 : ℝ) =
        ENNReal.ofReal (r^3) *
          ENNReal.ofReal |f (x₀ + r • x)| ^ (3 : ℝ) := by
    rw [abs_mul, abs_of_pos hr,
      ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_rpow_of_nonneg hr.le
        (by norm_num : (0 : ℝ) ≤ 3)]
    have hscalar : r ^ (3 : ℝ) = r^3 := by
      exact Real.rpow_natCast r 3
    rw [hscalar]
  simp_rw [hscaled]
  rw [lintegral_const_mul' (ENNReal.ofReal (r^3)) _ ENNReal.ofReal_ne_top]
  let c : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 3)
  have hmap : Measure.map (CKN.scalingSpace r x₀) volume =
      c • (volume : Measure Vec3) := CKN.map_scalingSpace r hr x₀
  have hfm : AEStronglyMeasurable f (c • (volume : Measure Vec3)) :=
    hf.mono_ac Measure.smul_absolutelyContinuous
  have hpow : AEMeasurable
      (fun y : Vec3 => ENNReal.ofReal |f y| ^ (3 : ℝ))
      (Measure.map (CKN.scalingSpace r x₀) volume) := by
    rw [hmap]
    simpa only [Real.enorm_eq_ofReal_abs, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfm.enorm)
  have hscaleMeas : Measurable (CKN.scalingSpace r x₀) := by
    unfold CKN.scalingSpace
    fun_prop
  have hchange :
      (∫⁻ x : Vec3,
        ENNReal.ofReal |f (x₀ + r • x)| ^ (3 : ℝ)) =
        c * (∫⁻ y : Vec3,
          ENNReal.ofReal |f y| ^ (3 : ℝ)) := by
    have h := lintegral_map' hpow hscaleMeas.aemeasurable
    rw [hmap, lintegral_smul_measure] at h
    simpa only [CKN.scalingSpace, Function.comp_def, c, smul_eq_mul] using h.symm
  rw [hchange, ← mul_assoc]
  have hcoeff : ENNReal.ofReal (r^3) * c = 1 := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r^3)]
    have hreal : r^3 * r⁻¹ ^ 3 = 1 := by
      rw [← mul_pow]
      field_simp
    rw [hreal]
    norm_num
  rw [hcoeff, one_mul]

/-- The critical spatial `L³` mass of a velocity slice is invariant under
positive Navier–Stokes scaling. -/
theorem blowupVelocitySlice_mass_eq
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    (∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (r • u (x₀ + r • x))) ^ (3 : ℝ)) =
      ∫⁻ y : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) := by
  have hf : AEStronglyMeasurable (fun y : Vec3 => vec3EuclideanNorm (u y)) volume :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  have h := blowupVelocityScalarSlice_mass_eq
    (fun y : Vec3 => vec3EuclideanNorm (u y)) hf x₀ r hr
  have hfun (x : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm (r • u (x₀ + r • x))) ^ (3 : ℝ) =
        ENNReal.ofReal |r * vec3EuclideanNorm (u (x₀ + r • x))| ^ (3 : ℝ) := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hr, abs_mul,
      abs_of_pos hr,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hfun2 (y : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm (u y)) ^ (3 : ℝ) =
        ENNReal.ofReal |vec3EuclideanNorm (u y)| ^ (3 : ℝ) := by
    rw [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  simp_rw [hfun, hfun2]
  exact h


end ESS
