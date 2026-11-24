/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Haar integration under complex rotations

Linear isometries preserve any additive Haar measure on a finite-dimensional
real normed space: Haar uniqueness reduces this to the closed unit ball.
Consequently unit complex scalar multiplication preserves nonnegative
integrals on balls, including infinite integrals and arbitrary integrands.
-/

@[expose] public section

open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SGPT.Foundations.Analysis

section RealIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A linear isometry preserves every Haar normalization, with no inner-product
assumption on the norm. -/
theorem measurePreserving_linearIsometryEquiv_addHaar
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e μ μ := by
  let K : PositiveCompacts E :=
    { carrier := closedBall 0 1
      isCompact' := isCompact_closedBall 0 1
      interior_nonempty' := ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds 0 (by
        norm_num))⟩ }
  have hpre : e ⁻¹' (K : Set E) = K := by
    ext x
    change e x ∈ closedBall (0 : E) 1 ↔ x ∈ closedBall (0 : E) 1
    simp [mem_closedBall, dist_eq_norm]
  have hmap : μ.map e (K : Set E) = μ K := by
    rw [Measure.map_apply e.continuous.measurable K.isCompact.measurableSet, hpre]
  let : (μ.map e).IsAddHaarMeasure :=
    e.toContinuousLinearEquiv.isAddHaarMeasure_map μ
  refine ⟨e.continuous.measurable, ?_⟩
  calc
    μ.map e = μ.map e K • Measure.addHaarMeasure K := Measure.addHaarMeasure_unique _ K
    _ = μ K • Measure.addHaarMeasure K := by rw [hmap]
    _ = μ := (Measure.addHaarMeasure_unique μ K).symm

/-- A real linear isometry preserves nonnegative integration on the ball about
zero. No measurability or finiteness of the integrand is needed. -/
theorem lintegral_ball_linearIsometryEquiv (μ : Measure E) [μ.IsAddHaarMeasure]
    (e : E ≃ₗᵢ[ℝ] E) (f : E → ℝ≥0∞) (R : ℝ) :
    ∫⁻ x in ball 0 R, f (e x) ∂μ = ∫⁻ x in ball 0 R, f x ∂μ := by
  have hpre : e ⁻¹' ball 0 R = ball 0 R := by
    ext x
    simp [mem_ball, dist_eq_norm]
  have hpres := (measurePreserving_linearIsometryEquiv_addHaar μ e).restrict_preimage
    (s := ball 0 R) measurableSet_ball
  rw [hpre] at hpres
  exact (MeasurePreserving.lintegral_map_equiv f e.toHomeomorph.toMeasurableEquiv hpres).symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Translating the ball and its integrand leaves nonnegative Haar integrals
unchanged. -/
theorem lintegral_ball_add (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (a : E) (R : ℝ) :
    ∫⁻ w in ball 0 R, f (a + w) ∂μ = ∫⁻ x in ball a R, f x ∂μ := by
  have hpre : (fun w : E => a + w) ⁻¹' ball a R = ball 0 R := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have hpres := (measurePreserving_add_left μ a).restrict_preimage
    (s := ball a R) measurableSet_ball
  rw [hpre] at hpres
  exact (MeasurePreserving.lintegral_map_equiv f
    (Homeomorph.addLeft a).toMeasurableEquiv hpres).symm

end RealIsometry

section ComplexRotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Multiplication by a unit-modulus complex scalar, as a real linear isometry. -/
noncomputable def complexRotation (z : ℂ) (hz : ‖z‖ = 1) : E ≃ₗᵢ[ℝ] E where
  toFun x := z • x
  invFun x := z⁻¹ • x
  map_add' := smul_add z
  map_smul' r x := smul_comm z r x
  left_inv x := by
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    simp [smul_smul, hz0]
  right_inv x := by
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    simp [smul_smul, hz0]
  norm_map' x := by simp [norm_smul, hz]

@[simp] theorem complexRotation_apply (z : ℂ) (hz : ‖z‖ = 1) (x : E) :
    complexRotation z hz x = z • x := rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Unit complex multiplication preserves an arbitrary Haar measure. -/
theorem measurePreserving_smul_of_norm_eq_one (μ : Measure E) [μ.IsAddHaarMeasure]
    (z : ℂ) (hz : ‖z‖ = 1) : MeasurePreserving (fun x : E => z • x) μ μ :=
  measurePreserving_linearIsometryEquiv_addHaar μ (complexRotation z hz)

/-- Rotation invariance of the nonnegative integral on a centered ball. -/
theorem lintegral_ball_smul_of_norm_eq_one (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (z : ℂ) (hz : ‖z‖ = 1) (R : ℝ) :
    ∫⁻ x in ball 0 R, f (z • x) ∂μ = ∫⁻ x in ball 0 R, f x ∂μ :=
  lintegral_ball_linearIsometryEquiv μ (complexRotation z hz) f R

/-- Rotation followed by translation identifies integration on centered and
translated balls. -/
theorem lintegral_ball_add_smul_of_norm_eq_one (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (a : E) (z : ℂ) (hz : ‖z‖ = 1) (R : ℝ) :
    ∫⁻ w in ball 0 R, f (a + z • w) ∂μ = ∫⁻ x in ball a R, f x ∂μ := by
  rw [lintegral_ball_smul_of_norm_eq_one μ (fun x => f (a + x)) z hz,
    lintegral_ball_add]

/-- The angular parametrization of the unit circle gives the same integral
on the ball for each angle. -/
theorem lintegral_ball_add_circleMap_smul (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (a : E) (t R : ℝ) :
    ∫⁻ w in ball 0 R, f (a + circleMap 0 1 t • w) ∂μ =
      ∫⁻ x in ball a R, f x ∂μ := by
  apply lintegral_ball_add_smul_of_norm_eq_one
  simp

end ComplexRotation

end SGPT.Foundations.Analysis
