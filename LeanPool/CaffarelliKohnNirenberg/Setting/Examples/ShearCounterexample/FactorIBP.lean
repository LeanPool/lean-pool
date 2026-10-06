/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.FactorDerivative
public import LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearCounterexample.SmoothIBP
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Integration by parts for space-time factors. -/

public section

open MeasureTheory
open CKN.Foundation.Parabolic
namespace CKN

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

theorem integral_mul_spatialPartial_eq_neg_spatialPartial_mul
    {F G : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGcompact : HasCompactSupport G) (i : Fin 3) :
    ∫ z : Vec3 × ℝ, F z * spatialPartial (show ParabolicPoint → ℝ from G) i z ∂volume =
      -∫ z : Vec3 × ℝ, spatialPartial (show ParabolicPoint → ℝ from F) i z * G z ∂volume := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiff_compact_right
    (E := Vec3 × ℝ) (μ := volume) (v := (basisVec i, 0)) hF hG hGcompact
  have hleft : (fun z : Vec3 × ℝ =>
      F z * spatialPartial (show ParabolicPoint → ℝ from G) i z) =
      fun z => F z * fderiv ℝ G z (basisVec i, 0) := by
    funext z
    exact congrArg (fun a : ℝ => F z * a)
      (spatialPartial_eq_joint_fderiv (g := G) hG z i)
  have hright : (∫ z : Vec3 × ℝ, fderiv ℝ F z (basisVec i, 0) * G z) =
      ∫ z : Vec3 × ℝ, spatialPartial (show ParabolicPoint → ℝ from F) i z * G z := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun a : ℝ => a * G z)
      (spatialPartial_eq_joint_fderiv (g := F) hF z i).symm
  calc
    _ = ∫ z : Vec3 × ℝ, F z * fderiv ℝ G z (basisVec i, 0) := by
      rw [← hleft]
    _ = -∫ z : Vec3 × ℝ, fderiv ℝ F z (basisVec i, 0) * G z := h
    _ = -∫ z : Vec3 × ℝ, spatialPartial (show ParabolicPoint → ℝ from F) i z * G z :=
      congrArg Neg.neg hright

theorem integral_mul_timePartial_eq_neg_timePartial_mul
    {F G : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGcompact : HasCompactSupport G) :
    ∫ z : Vec3 × ℝ, F z * timePartial (show ParabolicPoint → ℝ from G) z ∂volume =
      -∫ z : Vec3 × ℝ, timePartial (show ParabolicPoint → ℝ from F) z * G z ∂volume := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiff_compact_right
    (E := Vec3 × ℝ) (μ := volume) (v := (0, 1)) hF hG hGcompact
  have hleft : (fun z : Vec3 × ℝ =>
      F z * timePartial (show ParabolicPoint → ℝ from G) z) =
      fun z => F z * fderiv ℝ G z (0, 1) := by
    funext z
    exact congrArg (fun a : ℝ => F z * a)
      (timePartial_eq_joint_fderiv (g := G) hG z)
  have hright : (∫ z : Vec3 × ℝ, fderiv ℝ F z (0, 1) * G z) =
      ∫ z : Vec3 × ℝ, timePartial (show ParabolicPoint → ℝ from F) z * G z := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun a : ℝ => a * G z)
      (timePartial_eq_joint_fderiv (g := F) hF z).symm
  calc
    _ = ∫ z : Vec3 × ℝ, F z * fderiv ℝ G z (0, 1) := by
      rw [← hleft]
    _ = -∫ z : Vec3 × ℝ, fderiv ℝ F z (0, 1) * G z := h
    _ = -∫ z : Vec3 × ℝ, timePartial (show ParabolicPoint → ℝ from F) z * G z :=
      congrArg Neg.neg hright

end CKN
