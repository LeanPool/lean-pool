/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCBoxWeightedEstimate
public import LeanPool.EscauriazaSereginSverak.Linear.UCTargetEstimate

/-!
# Gaussian target-box comparison

The positive-time target box permits direct comparison of weighted and
unweighted integrals.
-/

public section


open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian weight on a positive-time target box controls its
unweighted mass. -/
theorem uc_target_box_le_weighted_box
    (a : ℝ) (ha : 0 ≤ a) (center : Vec3)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (hboxInt : IntegrableOn (fun z => vec3EuclideanNorm (v z) ^ 2)
      (spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) volume)
    (hweightedInt : IntegrableOn (fun z => ucGaussianWeight a z *
      (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z))
      (spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)) volume) :
    (∫ z in spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1),
      vec3EuclideanNorm (v z) ^ 2) ≤
      Real.exp (vec3EuclideanNorm center ^ 2 + 1) *
        ∫ z in spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1),
          ucGaussianWeight a z *
            (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z) := by
  let B : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball center 1) (Ioo (1 / 2) 1)
  let F : ParabolicPoint → ℝ := fun z => ucGaussianWeight a z *
    (vec3EuclideanNorm (v z) ^ 2 + spatialGradientSq v Dv z)
  let c : ℝ := Real.exp (vec3EuclideanNorm center ^ 2 + 1)
  have hBmeas : MeasurableSet B :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
  have hright : IntegrableOn (fun z => c * F z) B volume :=
    hweightedInt.const_mul c
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
  calc
    (∫ z in B, vec3EuclideanNorm (v z) ^ 2)
      ≤ ∫ z in B, c * F z :=
        setIntegral_mono_on hboxInt hright hBmeas hpoint
    _ = c * ∫ z in B, F z := by rw [integral_const_mul]
    _ = _ := rfl

end ESS
