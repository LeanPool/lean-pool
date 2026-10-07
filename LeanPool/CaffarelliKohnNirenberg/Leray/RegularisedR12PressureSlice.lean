/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityReg

/-!
# Spatial regularity of scalar Fourier fields

A bounded continuous path of scalar frequency fields with four Bessel
derivatives gives spatially differentiable real slices. The first spatial
partials are continuous and share a uniform bound with the field. This is
the scalar field estimate used for the pressure in `thm:regularised` (R2).
-/

public section

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- Slice differentiability, continuity of first spatial partials, and a
common pointwise bound for a scalar H⁴ Fourier field. -/
theorem regR12ScalarPressureField_sliceC1_bound
    (G : ℝ → Lp ℂ 2 (volume : Measure L2Vec3))
    (hG : Continuous G) (B : ℝ) (hB : ∀ t, ‖G t‖ ≤ B) :
    (∀ z : ParabolicPoint,
      DifferentiableAt ℝ
        (fun x : Vec3 => regR12SpaceTimeField Complex.reCLM (fun _ => 1) G (x, z.2)) z.1) ∧
    (∀ j : Fin 3, Continuous
      (fun z : Vec3 × ℝ => spatialPartial
        (regR12SpaceTimeField Complex.reCLM (fun _ => 1) G) j z)) ∧
    (∀ z : ParabolicPoint,
      |regR12SpaceTimeField Complex.reCLM (fun _ => 1) G z| ≤
        ‖Complex.reCLM‖ * ((1 + 2 * π) *
          ((eLpNorm regR12Kernel 2 volume).toReal * B)) ∧
      ∀ j : Fin 3,
        |spatialPartial (regR12SpaceTimeField Complex.reCLM (fun _ => 1) G) j z| ≤
          ‖Complex.reCLM‖ * ((1 + 2 * π) *
            ((eLpNorm regR12Kernel 2 volume).toReal * B))) := by
  have hD (z : ParabolicPoint) :=
    regR12SpaceTimeField_spatialPartial Complex.reCLM (fun _ => (1 : ℂ))
      aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le G
      regR12_one_norm_le' z
  refine ⟨fun z => (hD z).1, fun j => ?_, fun z => ?_⟩
  · have heq : (fun z : Vec3 × ℝ => spatialPartial
        (regR12SpaceTimeField Complex.reCLM (fun _ => 1) G) j z) =
        fun z => regR12SpaceTimeField Complex.reCLM
          (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) G z := by
      funext z
      exact (hD z).2 j
    rw [heq]
    exact regR12SpaceTimeField_continuous Complex.reCLM _
      (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
      (2 * π) (by positivity) (regR12_first_norm_le j) G hG
  · have hK : 0 ≤ (eLpNorm regR12Kernel 2 volume).toReal := ENNReal.toReal_nonneg
    have hB0 : 0 ≤ B := (norm_nonneg (G z.2)).trans (hB z.2)
    have hGB := mul_le_mul_of_nonneg_left (hB z.2) hK
    have hC1 : (1 : ℝ) ≤ 1 + 2 * π := by linarith only [Real.pi_pos]
    have hC2 : (2 * π : ℝ) ≤ 1 + 2 * π := by linarith only
    have hp := regR12SpaceTimeField_abs_le Complex.reCLM (fun _ => (1 : ℂ))
      aestronglyMeasurable_const 1 zero_le_one regR12_one_norm_le G z
    refine ⟨?_, fun j => ?_⟩
    · calc
        |regR12SpaceTimeField Complex.reCLM (fun _ => 1) G z| ≤
            ‖Complex.reCLM‖ * (1 *
              (eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) := hp
        _ = ‖Complex.reCLM‖ * (1 *
            ((eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖)) := by ring
        _ ≤ ‖Complex.reCLM‖ * ((1 + 2 * π) *
            ((eLpNorm regR12Kernel 2 volume).toReal * B)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          calc
            1 * ((eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) ≤
                1 * ((eLpNorm regR12Kernel 2 volume).toReal * B) := by
                  simpa only [one_mul] using hGB
            _ ≤ (1 + 2 * π) *
                ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                  mul_le_mul_of_nonneg_right hC1 (mul_nonneg hK hB0)
    · rw [(hD z).2 j]
      have hdp := regR12SpaceTimeField_abs_le Complex.reCLM
        (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ)
        (((regR12CoordSymbol_continuous j).mul continuous_const).aestronglyMeasurable)
        (2 * π) (by positivity) (regR12_first_norm_le j) G z
      calc
        |regR12SpaceTimeField Complex.reCLM
            (fun ξ => regR12CoordSymbol j ξ * (fun _ : L2Vec3 => (1 : ℂ)) ξ) G z| ≤
          ‖Complex.reCLM‖ * ((2 * π) *
            (eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) := hdp
        _ = ‖Complex.reCLM‖ * ((2 * π) *
            ((eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖)) := by ring
        _ ≤ ‖Complex.reCLM‖ * ((1 + 2 * π) *
            ((eLpNorm regR12Kernel 2 volume).toReal * B)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          calc
            (2 * π) * ((eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) ≤
                (2 * π) * ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                  mul_le_mul_of_nonneg_left hGB (by positivity)
            _ ≤ (1 + 2 * π) *
                ((eLpNorm regR12Kernel 2 volume).toReal * B) :=
                  mul_le_mul_of_nonneg_right hC2 (mul_nonneg hK hB0)

end CKN.Leray

end
