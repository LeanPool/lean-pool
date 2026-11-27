/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzL2Differentiation

/-!
# Genuine L² differentiation of the real-time massive evolution

The phase difference is bounded by `|s-t| |ω|`. Consequently the squared
difference-quotient residual is dominated by `4 |ω f|²`, an integrable function
for the actual Schwartz datum. The resulting derivative is transported through
the genuine L² Fourier isometry. No uniform spatial Schwartz estimate or
complex-time power series is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology FourierTransform
open scoped SchwartzMap FourierTransform

theorem norm_massiveEvolutionPhase_sub_le (m s t : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖massiveEvolutionPhase m s ξ - massiveEvolutionPhase m t ξ‖ ≤
      |s - t| * |massiveSchwartzSymbol m 1 ξ| := by
  have heq : massiveEvolutionPhase m s ξ - massiveEvolutionPhase m t ξ =
      massiveEvolutionPhase m t ξ * (massiveEvolutionPhase m (s - t) ξ - 1) := by
    rw [mul_sub, mul_one, ← massiveEvolutionPhase_add, add_sub_cancel]
  rw [heq, norm_mul, norm_massiveEvolutionPhase, one_mul]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := (s - t) * massiveSchwartzSymbol m 1 ξ)
  simpa only [massiveEvolutionPhase, mul_comm Complex.I, Real.norm_eq_abs, abs_mul] using hb

/-- The actual frequency-space Schwartz evolution. -/
noncomputable def massiveFrequencyEvolution (m t : ℝ) (f : SpatialSchwartz) : SpatialSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (massiveEvolutionPhase m t) f

@[simp] theorem massiveFrequencyEvolution_apply (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveFrequencyEvolution m t f ξ = massiveEvolutionPhase m t ξ * f ξ := by
  rw [massiveFrequencyEvolution, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_massiveEvolutionPhase m t)]
  rfl

/-- Massive frequency energy defined as `SchwartzMap.smulLeftCLM ℂ (fun ξ => (massiveSchwartzSymbol
m 1 ξ : ℂ)) f`. -/
noncomputable def massiveFrequencyEnergy (m : ℝ) (f : SpatialSchwartz) : SpatialSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ => (massiveSchwartzSymbol m 1 ξ : ℂ)) f

@[simp] theorem massiveFrequencyEnergy_apply (m : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveFrequencyEnergy m f ξ = (massiveSchwartzSymbol m 1 ξ : ℂ) * f ξ := by
  rw [massiveFrequencyEnergy, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_complex_massiveSchwartzSymbol m 1)]
  rfl

/-- Massive frequency derivative obtained from `Complex.I`. -/
noncomputable def massiveFrequencyDerivative (m t : ℝ) (f : SpatialSchwartz) : SpatialSchwartz :=
  Complex.I • massiveFrequencyEvolution m t (massiveFrequencyEnergy m f)

theorem norm_massiveFrequencyDerivative (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖massiveFrequencyDerivative m t f ξ‖ = ‖massiveFrequencyEnergy m f ξ‖ := by
  simp only [massiveFrequencyDerivative, smul_apply, norm_smul,
    Complex.norm_I, massiveFrequencyEvolution_apply, norm_mul, norm_massiveEvolutionPhase,
    one_mul]

theorem hasDerivAt_massiveFrequencyEvolution_apply (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveFrequencyEvolution m s f ξ)
      (massiveFrequencyDerivative m t f ξ) t := by
  convert (hasDerivAt_massiveEvolutionPhase m t ξ).mul_const (f ξ) using 1
  · simp only [massiveFrequencyEvolution_apply]
  · simp only [massiveFrequencyDerivative, smul_apply, smul_eq_mul,
      massiveFrequencyEvolution_apply, massiveFrequencyEnergy_apply]
    ring

theorem norm_slope_massiveFrequencyEvolution_le (m s t : ℝ) (hst : s ≠ t)
    (f : SpatialSchwartz) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖(s - t)⁻¹ • (massiveFrequencyEvolution m s f ξ -
        massiveFrequencyEvolution m t f ξ)‖ ≤ ‖massiveFrequencyEnergy m f ξ‖ := by
  have hst' : |s - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hst)
  simp only [massiveFrequencyEvolution_apply, ← sub_mul, norm_smul, norm_inv,
    Real.norm_eq_abs, norm_mul, massiveFrequencyEnergy_apply, Complex.norm_real]
  calc
    |s - t|⁻¹ * (‖massiveEvolutionPhase m s ξ - massiveEvolutionPhase m t ξ‖ * ‖f ξ‖)
        ≤ |s - t|⁻¹ * ((|s - t| * |massiveSchwartzSymbol m 1 ξ|) * ‖f ξ‖) := by
          gcongr
          exact norm_massiveEvolutionPhase_sub_le m s t ξ
    _ = |massiveSchwartzSymbol m 1 ξ| * ‖f ξ‖ := by
      field_simp [hst']

theorem integrable_massiveFrequencyDerivative_bound (m : ℝ) (f : SpatialSchwartz) :
    Integrable (fun ξ => 4 * ‖massiveFrequencyEnergy m f ξ‖ ^ 2) := by
  have h := (memLp_two_iff_integrable_sq_norm
    (massiveFrequencyEnergy m f).continuous.aestronglyMeasurable).mp
      ((massiveFrequencyEnergy m f).memLp 2)
  exact h.const_mul 4

/-- The actual frequency evolution is differentiable as an L²-valued curve. -/
theorem hasDerivAt_massiveFrequencyEvolution_toL2 (m t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveFrequencyEvolution m s f).toLp 2)
      ((massiveFrequencyDerivative m t f).toLp 2) t := by
  apply hasDerivAt_spatialSchwartz_toL2_of_dominated
    (fun s => massiveFrequencyEvolution m s f) (massiveFrequencyDerivative m t f) t
    (hasDerivAt_massiveFrequencyEvolution_apply m t f)
    (fun ξ => 4 * ‖massiveFrequencyEnergy m f ξ‖ ^ 2)
    (integrable_massiveFrequencyDerivative_bound m f)
  filter_upwards [self_mem_nhdsWithin] with s hs
  refine Eventually.of_forall fun ξ => ?_
  have hst : s ≠ t := hs
  have hq := norm_slope_massiveFrequencyEvolution_le m s t hst f ξ
  have hr := norm_sub_le
    ((s - t)⁻¹ • (massiveFrequencyEvolution m s f ξ - massiveFrequencyEvolution m t f ξ))
    (massiveFrequencyDerivative m t f ξ)
  rw [norm_massiveFrequencyDerivative] at hr
  calc
    ‖(s - t)⁻¹ • (massiveFrequencyEvolution m s f ξ -
      massiveFrequencyEvolution m t f ξ) - massiveFrequencyDerivative m t f ξ‖ ^ 2
        ≤ (2 * ‖massiveFrequencyEnergy m f ξ‖) ^ 2 := by
          gcongr
          linarith
    _ = 4 * ‖massiveFrequencyEnergy m f ξ‖ ^ 2 := by ring

/-- In physical position space the same derivative is the actual inverse Fourier
transform of `i ω exp(i t ω) f̂`, interpreted in L². -/
theorem hasDerivAt_massiveSchwartzEvolution_toL2 (m t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveSchwartzEvolution m s f).toLp 2)
      ((𝓕⁻ (massiveFrequencyDerivative m t (𝓕 f))).toLp 2) t := by
  have ht := (((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ
    (Fin 3)) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_massiveFrequencyEvolution_toL2 m t (𝓕 f))
  change HasDerivAt (fun s => 𝓕⁻ ((massiveFrequencyEvolution m s (𝓕 f)).toLp 2))
    (𝓕⁻ ((massiveFrequencyDerivative m t (𝓕 f)).toLp 2)) t at ht
  simpa only [SchwartzMap.toLp_fourierInv_eq, massiveFrequencyEvolution,
    massiveSchwartzEvolution, SchwartzMap.fourierMultiplierCLM_apply] using ht

end VacuumBellSeparation
