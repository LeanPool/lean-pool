/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetRescale

/-!
# The weighted target-box estimate

The interior Gaussian weight controls the unweighted target box in
`lem:uc-gaussian`.
-/

public section


open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian decay remaining after the target-box weight comparison is
the decay in `eq:uc-gaussian-box`. -/
theorem uc_target_exponential_identity
    (x₀ x : Vec3) (scale t ρ : ℝ) (hscale : 0 < scale)
    (hscaleSq : scale ^ 2 = 2 * t)
    (hρdef : ρ = 2 * vec3EuclideanNorm
      ((Real.sqrt (2 / 100))⁻¹ • (x - x₀)) / scale) :
    Real.exp (vec3EuclideanNorm (scale⁻¹ • (x - x₀)) ^ 2 + 1) *
      Real.exp (-(ρ ^ 2) / 100) =
        Real.exp 1 *
          Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
  let μ : ℝ := Real.sqrt (2 / 100)
  let d : ℝ := vec3EuclideanNorm (x - x₀)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμsq : μ ^ 2 = 1 / 50 := by dsimp [μ]; norm_num
  have ht : 0 < t := by nlinarith only [hscale, hscaleSq]
  have hcenter : vec3EuclideanNorm (scale⁻¹ • (x - x₀)) = d / scale := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hscale)]
    simp only [d, inv_mul_eq_div]
  have hX : vec3EuclideanNorm (μ⁻¹ • (x - x₀)) = d / μ := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hμ)]
    simp only [d, inv_mul_eq_div]
  have hρ : ρ = 2 * d / (μ * scale) := by
    rw [hρdef, show Real.sqrt (2 / 100 : ℝ) = μ from rfl, hX]
    ring
  have hρsq : ρ ^ 2 / 100 = 2 * d ^ 2 / scale ^ 2 := by
    rw [hρ]
    calc
      (2 * d / (μ * scale)) ^ 2 / 100 =
          4 * d ^ 2 / (100 * μ ^ 2 * scale ^ 2) := by ring
      _ = 2 * d ^ 2 / scale ^ 2 := by rw [hμsq]; ring
  have hcenterSq : (d / scale) ^ 2 = d ^ 2 / (2 * t) := by
    rw [← hscaleSq]
    ring
  have hhalf : d ^ 2 / scale ^ 2 = d ^ 2 / (2 * t) := by
    rw [← hscaleSq]
  have hρsq' : ρ ^ 2 / 100 = 2 * (d ^ 2 / (2 * t)) := by
    calc
      _ = 2 * (d ^ 2 / scale ^ 2) := by rw [hρsq]; ring
      _ = _ := by rw [hhalf]
  have hkey : (d / scale) ^ 2 + 1 - ρ ^ 2 / 100 =
      1 - d ^ 2 / (2 * t) := by
    rw [hρsq', hcenterSq]
    ring
  rw [hcenter, ← Real.exp_add, ← Real.exp_add]
  congr 1
  convert hkey using 1 <;> ring

/-- The lower Gaussian weight on a target box converts an interior weighted
integral into an unweighted box integral (`lem:uc-gaussian`). -/
theorem uc_target_box_le_weighted_interior
    (ρ a : ℝ) (ha : 0 ≤ a) (center : Vec3)
    (hbox : spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1) ⊆
      ucInnerRegion ρ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hboxInt : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      (spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) volume)
    (hinnerInt : IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
      (ucInnerRegion ρ) volume) :
    (∫ z in spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1),
      vec3EuclideanNorm (v z) ^ 2) ≤
      Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
        ∫ z in ucInnerRegion ρ, ucGaussianWeight a z *
          (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z) := by
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  let F : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)
  let c : ℝ := Real.exp (vec3EuclideanNorm center ^ 2 + 1)
  have hBmeas : MeasurableSet B :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hFbox : IntegrableOn F B volume := hinnerInt.mono_set hbox
  have hright : IntegrableOn (fun z => c * F z) B volume := hFbox.const_mul c
  have hpoint (z : ParabolicPoint) (hz : z ∈ B) :
      vec3EuclideanNorm (v z) ^ 2 ≤ c * F z := by
    have hw := uc_gaussian_weight_lower_on_target a ha center z hz
    have hwPos : 0 ≤ ucGaussianWeight a z := by
      dsimp [ucGaussianWeight]
      have hs : 0 < z.2 := by linarith only [hz.2.1]
      have hh : 0 < gaussCarlemanTimeWeight z.2 := by
        dsimp [gaussCarlemanTimeWeight]
        positivity
      positivity
    have hgrad : 0 ≤ spatialGradientSq v Dv z := by
      dsimp [spatialGradientSq]
      positivity
    have hv : 0 ≤ vec3EuclideanNorm (v z) ^ 2 := sq_nonneg _
    have hfirst :
        Real.exp (-(vec3EuclideanNorm center ^ 2 + 1)) *
          vec3EuclideanNorm (v z) ^ 2 ≤
        ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2 :=
      mul_le_mul_of_nonneg_right hw hv
    have hsecond : ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2 ≤
        F z := by
      dsimp [F]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hgrad) hwPos
    have hfactor : c * Real.exp (-(vec3EuclideanNorm center ^ 2 + 1)) = 1 := by
      dsimp [c]
      rw [← Real.exp_add]
      simp
    have hcpos : 0 ≤ c := Real.exp_pos _ |>.le
    have hmul := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) hcpos
    calc
      vec3EuclideanNorm (v z) ^ 2 =
          c * (Real.exp (-(vec3EuclideanNorm center ^ 2 + 1)) *
            vec3EuclideanNorm (v z) ^ 2) := by
              rw [← mul_assoc, hfactor, one_mul]
      _ ≤ c * F z := hmul
  have hFnonneg : ∀ z ∈ ucInnerRegion ρ, 0 ≤ F z := by
    intro z hz
    have hs : 0 < z.2 := hz.2.1
    have hh : 0 < gaussCarlemanTimeWeight z.2 := by
      dsimp [gaussCarlemanTimeWeight]
      positivity
    dsimp [F, ucGaussianWeight]
    have hg : 0 ≤ spatialGradientSq v Dv z := by
      dsimp [spatialGradientSq]
      positivity
    positivity
  have hinnerMeas : MeasurableSet (ucInnerRegion ρ) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hFae : 0 ≤ᵐ[volume.restrict (ucInnerRegion ρ)] F := by
    filter_upwards [ae_restrict_mem hinnerMeas] with z hz
    exact hFnonneg z hz
  calc
    (∫ z in B, vec3EuclideanNorm (v z) ^ 2)
      ≤ ∫ z in B, c * F z :=
        setIntegral_mono_on hboxInt hright hBmeas hpoint
    _ = c * ∫ z in B, F z := by rw [integral_const_mul]
    _ ≤ c * ∫ z in ucInnerRegion ρ, F z := by
      apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact setIntegral_mono_set hinnerInt hFae
        (Filter.Eventually.of_forall (fun _ hz => hbox hz))
    _ = _ := rfl

/-- Rescaling the interior weighted estimate gives the Gaussian box estimate
in `lem:uc-gaussian`, with the absolute factor from the weight lower bound
kept explicit. -/
theorem uc_gaussian_target_box_rescaling
    (x₀ x : Vec3) (R T t ρ scale a C₀ : ℝ)
    (ht : 0 < t) (hscale : scale = Real.sqrt (2 * t))
    (hρ : 4 ≤ ρ) (hC₀ : 0 < C₀)
    (hρdef : ρ = 2 * vec3EuclideanNorm
      ((Real.sqrt (2 / 100))⁻¹ • (x - x₀)) / scale)
    (ha : a = (1 / 100) * ρ ^ 2 /
      (2 * Real.log (gaussCarlemanTimeWeight (3 / 2))))
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (hsourceInt : IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
      (spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t))) volume)
    (hboxInt : IntegrableOn
      (fun z => vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2)
      (spaceTimeSet (vec3Ball (scale⁻¹ • (x - x₀)) 1)
        (Ioo (1 / 2) 1)) volume)
    (hinnerInt : IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z)) (ucInnerRegion ρ) volume)
    (hinterior : (∫ z in ucInnerRegion ρ, ucGaussianWeight a z *
      (vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z)) ≤
        C₀ * Real.exp (-(ρ ^ 2) / 100) *
          (∫ z in ucCylinder ρ,
            vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
              spatialGradientSq (ucScaledField x₀ scale w)
                (ucScaledDw x₀ scale Dw) z))
    (henergy : (∫ z in ucCylinder ρ,
      vec3EuclideanNorm ((ucScaledField x₀ scale w) z) ^ 2 +
        spatialGradientSq (ucScaledField x₀ scale w)
          (ucScaledDw x₀ scale Dw) z) ≤
        2 * Real.rpow scale (-5 : ℝ) * ucLocalEnergy x₀ R T w Dw) :
    (∫ z in spaceTimeSet (vec3Ball x (Real.sqrt (2 * t)))
        (Ioo t (2 * t)), vec3EuclideanNorm (w z) ^ 2) ≤
      2 * Real.exp 1 * C₀ * ucLocalEnergy x₀ R T w Dw *
        Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
  have hscalePos : 0 < scale := by rw [hscale]; positivity
  have hscaleSq : scale ^ 2 = 2 * t := by
    rw [hscale, Real.sq_sqrt (by positivity)]
  have hlog : 0 < Real.log (gaussCarlemanTimeWeight (3 / 2)) := by
    have hlo := uc_log_weight_three_half_bounds.1
    linarith only [hlo]
  have ha0 : 0 ≤ a := by
    rw [ha]
    positivity
  let center : Vec3 := scale⁻¹ • (x - x₀)
  let v := ucScaledField x₀ scale w
  let Dv := ucScaledDw x₀ scale Dw
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  let M : ℝ := ∫ z in ucInnerRegion ρ, ucGaussianWeight a z *
    (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)
  let E : ℝ := ∫ z in ucCylinder ρ,
    vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z
  let N : ℝ := ucLocalEnergy x₀ R T w Dw
  let J : ℝ := ∫ z in B, vec3EuclideanNorm (v z) ^ 2
  let I : ℝ := ∫ z in spaceTimeSet (vec3Ball x scale) (Ioo t (2 * t)),
    vec3EuclideanNorm (w z) ^ 2
  have hbox : B ⊆ ucInnerRegion ρ :=
    uc_target_box_subset_inner x₀ x scale ρ hscalePos hρ hρdef
  have htarget : J ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) * M :=
    uc_target_box_le_weighted_interior ρ a ha0 center hbox
      v Dv hboxInt hinnerInt
  have hinterior' : M ≤ C₀ * Real.exp (-(ρ ^ 2) / 100) * E := hinterior
  have henergy' : E ≤ 2 * Real.rpow scale (-5 : ℝ) * N := henergy
  have hchange : J = Real.rpow scale (-5 : ℝ) * I :=
    uc_target_box_integral_scaling x₀ x scale t hscalePos hscaleSq w hsourceInt
  have hcoef : scale ^ 5 * Real.rpow scale (-5 : ℝ) = 1 := by
    norm_num [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
    field_simp [ne_of_gt hscalePos]
  have hIeq : I = scale ^ 5 * J := by
    rw [hchange, ← mul_assoc, hcoef, one_mul]
  have hexp := uc_target_exponential_identity x₀ x scale t ρ
    hscalePos hscaleSq hρdef
  have hJbound : J ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
      (C₀ * Real.exp (-(ρ ^ 2) / 100) *
        (2 * Real.rpow scale (-5 : ℝ) * N)) := by
    calc
      J ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) * M := htarget
      _ ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
          (C₀ * Real.exp (-(ρ ^ 2) / 100) * E) :=
        mul_le_mul_of_nonneg_left hinterior' (Real.exp_pos _).le
      _ ≤ Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
          (C₀ * Real.exp (-(ρ ^ 2) / 100) *
            (2 * Real.rpow scale (-5 : ℝ) * N)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left henergy'
          (mul_nonneg hC₀.le (Real.exp_pos _).le)
  have hfinal : I ≤ 2 * Real.exp 1 * C₀ * N *
      Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
    rw [hIeq]
    have hmul := mul_le_mul_of_nonneg_left hJbound
      (pow_pos hscalePos 5).le
    calc
      scale ^ 5 * J ≤ scale ^ 5 *
        (Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
          (C₀ * Real.exp (-(ρ ^ 2) / 100) *
            (2 * Real.rpow scale (-5 : ℝ) * N))) := hmul
      _ = 2 * Real.exp 1 * C₀ * N *
          Real.exp (-(vec3EuclideanNorm (x - x₀) ^ 2) / (2 * t)) := by
        change scale ^ 5 *
          (Real.exp (vec3EuclideanNorm (scale⁻¹ • (x - x₀)) ^ 2 + 1) *
            (C₀ * Real.exp (-(ρ ^ 2) / 100) *
              (2 * Real.rpow scale (-5 : ℝ) * N))) = _
        calc
          _ = (scale ^ 5 * Real.rpow scale (-5 : ℝ)) *
              (Real.exp (vec3EuclideanNorm (scale⁻¹ • (x - x₀)) ^ 2 + 1) *
                Real.exp (-(ρ ^ 2) / 100)) * (2 * C₀ * N) := by ring
          _ = _ := by rw [hcoef, hexp]; ring
  simpa only [I, N, hscale] using hfinal

end ESS
