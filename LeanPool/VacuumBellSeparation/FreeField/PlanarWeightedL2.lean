/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarEnergyWeight
public import LeanPool.VacuumBellSeparation.FreeField.BoundedL2Multiplier
public import LeanPool.VacuumBellSeparation.FreeField.StrongProductDerivative

/-!
# The actual planar cutoff acting on L² curves

The fixed-vector derivative follows from a genuine dominated slope estimate
using the proved bound on the transition derivative. The bounded multiplication
operator then acts on a differentiable L² curve by the strong product rule.
No operator-norm differentiability of the cutoff family is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology

theorem hasTemperateGrowth_complex_planarEnergyWeight
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    Function.HasTemperateGrowth (fun x => (planarEnergyWeight a x₀ R t x : ℂ)) :=
  Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_planarEnergyWeight a x₀ R t)

theorem hasTemperateGrowth_complex_planarEnergySlope
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    Function.HasTemperateGrowth (fun x => (planarEnergySlope a x₀ R t x : ℂ)) :=
  Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_planarEnergySlope a x₀ R t)

/-- Planar weighted Schwartz defined as `SchwartzMap.smulLeftCLM ℂ (fun x => (planarEnergyWeight a
x₀ R t x : ℂ)) f`. -/
noncomputable def planarWeightedSchwartz (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) : SpatialSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (planarEnergyWeight a x₀ R t x : ℂ)) f

/-- Planar weighted Schwartz derivative. -/
noncomputable def planarWeightedSchwartzDerivative (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) : SpatialSchwartz :=
  -(SchwartzMap.smulLeftCLM ℂ (fun x => (planarEnergySlope a x₀ R t x : ℂ)) f)

@[simp] theorem planarWeightedSchwartz_apply (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    planarWeightedSchwartz a x₀ R t f x = (planarEnergyWeight a x₀ R t x : ℂ) * f x := by
  rw [planarWeightedSchwartz, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_complex_planarEnergyWeight a x₀ R t)]
  rfl

theorem planarWeightedSchwartzDerivative_apply (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) (x : EuclideanSpace ℝ (Fin 3)) :
    planarWeightedSchwartzDerivative a x₀ R t f x =
      -((planarEnergySlope a x₀ R t x : ℂ) * f x) := by
  rw [planarWeightedSchwartzDerivative, neg_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_complex_planarEnergySlope a x₀ R t)]
  rfl

theorem norm_planarEnergyWeight_sub_le (a x₀ x : EuclideanSpace ℝ (Fin 3))
    (R s t : ℝ) {C : ℝ} (hC : ∀ r, ‖deriv Real.smoothTransition r‖ ≤ C) :
    ‖planarEnergyWeight a x₀ R s x - planarEnergyWeight a x₀ R t x‖ ≤ C * ‖s - t‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun r _ => (hasDerivAt_planarEnergyWeight a x₀ x R r).differentiableAt)
    (fun r _ => ?_) convex_univ (Set.mem_univ t) (Set.mem_univ s)
  rw [(hasDerivAt_planarEnergyWeight a x₀ x R r).deriv, norm_neg]
  exact hC _

theorem norm_slope_planarWeightedSchwartz_le (a x₀ x : EuclideanSpace ℝ (Fin 3))
    (R s t : ℝ) (hst : s ≠ t) (f : SpatialSchwartz)
    {C : ℝ} (hC : ∀ r, ‖deriv Real.smoothTransition r‖ ≤ C) :
    ‖(s - t)⁻¹ • (planarWeightedSchwartz a x₀ R s f x -
      planarWeightedSchwartz a x₀ R t f x)‖ ≤ C * ‖f x‖ := by
  have hst' : ‖s - t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hst)
  simp only [planarWeightedSchwartz_apply, ← sub_mul, ← Complex.ofReal_sub,
    norm_smul, norm_inv, norm_mul, Complex.norm_real]
  calc
    ‖s - t‖⁻¹ * (‖planarEnergyWeight a x₀ R s x - planarEnergyWeight a x₀ R t x‖ * ‖f x‖)
        ≤ ‖s - t‖⁻¹ * ((C * ‖s - t‖) * ‖f x‖) := by
          gcongr
          exact norm_planarEnergyWeight_sub_le a x₀ x R s t hC
    _ = C * ‖f x‖ := by field_simp [hst']

theorem hasDerivAt_planarWeightedSchwartz_toL2
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt (fun s => (planarWeightedSchwartz a x₀ R s f).toLp 2)
      ((planarWeightedSchwartzDerivative a x₀ R t f).toLp 2) t := by
  obtain ⟨C, hC₀, hC⟩ := exists_bound_deriv_smoothTransition
  refine hasDerivAt_spatialSchwartz_toL2_of_dominated
    (fun s => planarWeightedSchwartz a x₀ R s f)
    (planarWeightedSchwartzDerivative a x₀ R t f) t ?_
      (fun x => (4 * C ^ 2) * ‖f x‖ ^ 2) ?_ ?_
  · intro x
    simpa only [planarWeightedSchwartz_apply, planarWeightedSchwartzDerivative_apply,
      Complex.ofReal_neg, neg_mul] using
      (hasDerivAt_planarEnergyWeight a x₀ x R t).ofReal_comp.mul_const (f x)
  · exact ((memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp
      (f.memLp 2)).const_mul (4 * C ^ 2)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine Eventually.of_forall fun x => ?_
    have hslope := norm_slope_planarWeightedSchwartz_le a x₀ x R s t hs f hC
    have hder : ‖planarWeightedSchwartzDerivative a x₀ R t f x‖ ≤ C * ‖f x‖ := by
      rw [planarWeightedSchwartzDerivative_apply, norm_neg, norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    have hres := norm_sub_le
      ((s - t)⁻¹ • (planarWeightedSchwartz a x₀ R s f x - planarWeightedSchwartz a x₀ R t f x))
      (planarWeightedSchwartzDerivative a x₀ R t f x)
    calc
      ‖(s - t)⁻¹ • (planarWeightedSchwartz a x₀ R s f x - planarWeightedSchwartz a x₀ R t f x) -
        planarWeightedSchwartzDerivative a x₀ R t f x‖ ^ 2 ≤ (2 * C * ‖f x‖) ^ 2 := by
          gcongr
          linarith
      _ = (4 * C ^ 2) * ‖f x‖ ^ 2 := by ring

theorem memLp_top_complex_planarEnergyWeight (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    MemLp (fun x => (planarEnergyWeight a x₀ R t x : ℂ)) ⊤ volume := by
  apply memLp_top_of_bound
    (hasTemperateGrowth_complex_planarEnergyWeight a x₀ R t).1.continuous.aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (planarEnergyWeight_nonneg a x₀ R t x)]
        using planarEnergyWeight_le_one a x₀ R t x

/-- Continuous linear map for the planar weight operator, of type `SpatialL2 →L[ℂ] SpatialL2`. -/
noncomputable def planarWeightOperator (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    SpatialL2 →L[ℂ] SpatialL2 :=
  boundedL2Multiplier (fun x => (planarEnergyWeight a x₀ R t x : ℂ))
    (memLp_top_complex_planarEnergyWeight a x₀ R t)

theorem planarWeightOperator_toLp (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (f : SpatialSchwartz) :
    planarWeightOperator a x₀ R t (f.toLp 2) = (planarWeightedSchwartz a x₀ R t f).toLp 2 :=
  boundedL2Multiplier_toLp _ _ (hasTemperateGrowth_complex_planarEnergyWeight a x₀ R t) f

theorem norm_planarWeightOperator_le (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ) :
    ‖planarWeightOperator a x₀ R t‖ ≤ 1 := by
  apply norm_boundedL2Multiplier_le _ _ zero_le_one
  exact Eventually.of_forall fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (planarEnergyWeight_nonneg a x₀ R t x)]
        using planarEnergyWeight_le_one a x₀ R t x

/-- Product rule for the actual planar cutoff and any actual L²-differentiable
Schwartz curve. The statement does not assume differentiation in Schwartz space. -/
theorem hasDerivAt_planarWeighted_curve_toL2
    (a x₀ : EuclideanSpace ℝ (Fin 3)) (R t : ℝ)
    (F : ℝ → SpatialSchwartz) (G : SpatialSchwartz)
    (hF : HasDerivAt (fun s => (F s).toLp 2 volume) (G.toLp 2 volume) t) :
    HasDerivAt (fun s => (planarWeightedSchwartz a x₀ R s (F s)).toLp 2 volume)
      ((planarWeightedSchwartz a x₀ R t G).toLp 2 volume +
        (planarWeightedSchwartzDerivative a x₀ R t (F t)).toLp 2 volume) t := by
  have hfixed := hasDerivAt_planarWeightedSchwartz_toL2 a x₀ R t (F t)
  have hcont := (hasDerivAt_planarWeightedSchwartz_toL2 a x₀ R t G).continuousAt
  have ht := hasDerivAt_strong_operator_apply
    (fun s => (planarWeightOperator a x₀ R s).restrictScalars ℝ) hF
    (by simpa only [ContinuousLinearMap.coe_restrictScalars', planarWeightOperator_toLp]
      using hfixed)
    (by simpa only [ContinuousLinearMap.coe_restrictScalars', planarWeightOperator_toLp]
      using hcont)
    (Eventually.of_forall fun s => by
      simpa only [ContinuousLinearMap.norm_restrictScalars]
        using norm_planarWeightOperator_le a x₀ R s)
  simpa only [ContinuousLinearMap.coe_restrictScalars', planarWeightOperator_toLp] using ht

end VacuumBellSeparation
