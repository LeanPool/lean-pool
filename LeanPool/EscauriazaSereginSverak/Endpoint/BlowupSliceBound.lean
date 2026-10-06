/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTerminal

public section

open MeasureTheory Filter CKN.Foundation.Parabolic
open scoped ENNReal
namespace ESS

/-- The global Euclidean velocity `L³` norm is invariant under positive
spatial Navier–Stokes rescaling. -/
theorem blowup_rescaled_velocitySlice_eLpNorm_three_eq
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r) :
    eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3
      (volume : Measure Vec3) =
    eLpNorm (fun y => vec3EuclideanNorm (u y)) 3
      (volume : Measure Vec3) := by
  have hscaled : AEStronglyMeasurable
      (fun x => vec3EuclideanNorm (r • u (x₀ + r • x)))
      (volume : Measure Vec3) :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (blowup_rescaled_velocitySlice_aestronglyMeasurable u hu x₀ r hr)
  have hsource : AEStronglyMeasurable
      (fun y => vec3EuclideanNorm (u y)) (volume : Measure Vec3) :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 : ℝ≥0∞) ≠ ⊤) hscaled,
    eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 : ℝ≥0∞) ≠ ⊤) hsource]
  norm_num
  simp only [Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hm := congrArg (fun a : ℝ≥0∞ => a ^ (1 / 3 : ℝ))
    (blowupVelocitySlice_mass_eq u hu x₀ r hr)
  norm_num at hm
  exact hm

/-- A global velocity `L³` slice bound controls the local `L²` norm of
each positive spatial rescaling. -/
theorem blowup_rescaled_velocitySlice_local_two_le
    (u : Vec3 → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure Vec3))
    (x₀ c : Vec3) (r : ℝ) (hr : 0 < r) :
    eLpNorm (fun x => r • u (x₀ + r • x)) 2
        (volume.restrict (vec3Ball c 1)) ≤
      eLpNorm (fun y => vec3EuclideanNorm (u y)) 3
        (volume : Measure Vec3) *
      (volume (vec3Ball c 1)) ^ (1 / 6 : ℝ) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball c 1)
  have hscaled := blowup_rescaled_velocitySlice_aestronglyMeasurable
    u hu x₀ r hr
  have hnorm : eLpNorm (fun x => r • u (x₀ + r • x)) 2 μ ≤
      eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 2 μ := by
    apply eLpNorm_mono_enorm_ae hscaled.restrict
    filter_upwards [] with x
    rw [← ofReal_norm, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm _)
  have hcompare : eLpNorm
      (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 2 μ ≤
      eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3 μ *
        (μ Set.univ) ^ (1 / 6 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (μ := μ) (f := fun x => vec3EuclideanNorm (r • u (x₀ + r • x)))
      (p := (2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
      (by norm_num) (by norm_num)
    convert h using 1
    norm_num
  have hmono : eLpNorm
      (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3 μ ≤
      eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3
        (volume : Measure Vec3) :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  calc
    eLpNorm (fun x => r • u (x₀ + r • x)) 2 μ ≤
        eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 2 μ := hnorm
    _ ≤ eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3 μ *
        (μ Set.univ) ^ (1 / 6 : ℝ) := hcompare
    _ ≤ eLpNorm (fun x => vec3EuclideanNorm (r • u (x₀ + r • x))) 3 volume *
        (μ Set.univ) ^ (1 / 6 : ℝ) := by gcongr
    _ = eLpNorm (fun y => vec3EuclideanNorm (u y)) 3 volume *
        (volume (vec3Ball c 1)) ^ (1 / 6 : ℝ) := by
      rw [blowup_rescaled_velocitySlice_eLpNorm_three_eq u hu x₀ r hr]
      simp only [μ, Measure.restrict_apply_univ]

end ESS
