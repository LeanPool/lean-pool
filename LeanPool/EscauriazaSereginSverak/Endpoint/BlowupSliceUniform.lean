/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupH1Slices
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsVector

/-!
# Blowup Slice Uniform

Spatial slice bounds and rescaling identities in the endpoint compactness argument.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- A uniform whole-space `L³` velocity slice bound controls the essential
supremum of every component's local `L²` slice norm. -/
theorem blowup_component_slice_two_essSup_le_of_three
    (v : ParabolicPoint → Vec3) (J : Set ℝ)
    (c : Vec3) (R : ℝ) (i : Fin 3) (M : ℝ≥0∞)
    (hslice : ∀ᵐ t ∂volume.restrict J,
      AEStronglyMeasurable (fun x : Vec3 => v (x,t)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 3 volume ≤ M) :
    essSup (fun t => eLpNorm (fun x : Vec3 => v (x,t) i) 2
      (volume.restrict (vec3Ball c R))) (volume.restrict J) ≤
      M * (volume (vec3Ball c R)) ^ (1 / 6 : ℝ) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball c R)
  by_cases hJzero : (volume.restrict J : Measure ℝ) = 0
  · simp [hJzero]
  have : (ae (volume.restrict J)).NeBot := ae_neBot.mpr hJzero
  apply essSup_le_of_ae_le _ _
    (Filter.isCoboundedUnder_le_of_le _ (fun _ => bot_le))
  filter_upwards [hslice] with t ht
  have hcomp : AEStronglyMeasurable (fun x : Vec3 => v (x,t) i) volume := by
    have hcont : Continuous (fun w : Vec3 => w i) := continuous_apply i
    exact hcont.comp_aestronglyMeasurable ht.1
  have hcompLe :
      eLpNorm (fun x : Vec3 => v (x,t) i) 2 μ ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 2 μ := by
    apply eLpNorm_mono_enorm_ae hcomp.restrict
    filter_upwards [] with x
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (abs_apply_le_vec3EuclideanNorm (v (x,t)) i)
  have hcompare :
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 2 μ ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 3 μ *
        (μ Set.univ) ^ (1 / 6 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (μ := μ) (f := fun x => vec3EuclideanNorm (v (x,t)))
      (p := (2 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
      (by norm_num) (by norm_num)
    convert h using 1
    norm_num
  have hglobal :
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 3 μ ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 3 volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  calc
    eLpNorm (fun x : Vec3 => v (x,t) i) 2 μ ≤
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 2 μ := hcompLe
    _ ≤ eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v (x,t))) 3 μ *
        (μ Set.univ) ^ (1 / 6 : ℝ) := hcompare
    _ ≤ M * (volume (vec3Ball c R)) ^ (1 / 6 : ℝ) := by
      simpa only [μ, Measure.restrict_apply_univ] using
        (mul_le_mul_of_nonneg_right (hglobal.trans ht.2) (by positivity))

end ESS
