/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialMassShellBound
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Actual Fourier bounds from the support volume

The transform is the original exp(-i p.x) integral. The coefficient is
the actual Lebesgue support volume; no unitary normalization is silently
inserted. This supplies the low-frequency absorption in the joint norm.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory Set Filter
open scoped InnerProductSpace

theorem spatialFourier_norm_le_support_integral (f : SpatialTestFunction)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hf : Function.support f.1 ⊆ S)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖spatialFourier f p‖ ≤ ∫ x in S, ‖spatialSchwartz f x‖ := by
  have hout (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∉ S) : f.1 x = 0 := by
    by_contra h
    exact hx (hf h)
  have heq := setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := S) (μ := volume)
    (f := fun x => Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (f.1 x : ℂ))
    (fun x hx => by simp [hout x hx])
  rw [spatialFourier, ← heq]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp [Complex.norm_exp, spatialSchwartz_apply]

/-- Cauchy-Schwarz on the actual finite support set. -/
theorem spatialFourier_norm_sq_le_support_volume (f : SpatialTestFunction)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : volume S < ⊤)
    (hf : Function.support f.1 ⊆ S) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖spatialFourier f p‖ ^ 2 ≤ (volume S).toReal * ∫ x, (f.1 x) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS⟩
  have hf2 : MemLp (spatialSchwartz f) (ENNReal.ofReal 2) (volume.restrict S) := by
    simpa using ((spatialSchwartz f).memLp 2).restrict S
  have h12 : MemLp (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℂ))
      (ENNReal.ofReal 2) (volume.restrict S) := memLp_const 1
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf2 h12
  have hout (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∉ S) : f.1 x = 0 := by
    by_contra h
    exact hx (hf h)
  have hsquare : (∫ x in S, (f.1 x) ^ 2) = ∫ x, (f.1 x) ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hout x hx])
  have hcs' : (∫ x in S, ‖spatialSchwartz f x‖) ≤
      Real.sqrt (∫ x, (f.1 x) ^ 2) * Real.sqrt (volume S).toReal := by
    simpa only [norm_one, mul_one, Real.rpow_two, Real.one_rpow, one_pow, integral_const,
      smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
      spatialSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      hsquare, ← Real.sqrt_eq_rpow] using hcs
  have hnorm := (spatialFourier_norm_le_support_integral f S hf p).trans hcs'
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt ENNReal.toReal_nonneg] at hsq
  simpa only [mul_comm] using hsq

/-- Integrating a uniform actual Fourier bound over the unit frequency ball. -/
theorem spatialFourier_low_frequency_le_support_volume (f : SpatialTestFunction)
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : volume S < ⊤)
    (hf : Function.support f.1 ⊆ S) :
    (∫ p in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖spatialFourier f p‖ ^ 2) ≤
      ((4 * Real.pi / 3) * (volume S).toReal) * ∫ x, (f.1 x) ^ 2 := by
  let C := (volume S).toReal * ∫ x, (f.1 x) ^ 2
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (measure_ball_lt_top (μ := volume) (x :=
      (0 : EuclideanSpace ℝ (Fin 3))) (r := 1))⟩
  have h : (∫ p in B, ‖spatialFourier f p‖ ^ 2) ≤ ∫ _ in B, C :=
    integral_mono_ae (integrable_spatialFourier_norm_sq f).integrableOn
      (integrable_const C)
      (Eventually.of_forall (spatialFourier_norm_sq_le_support_volume f S hS hf))
  calc
    _ ≤ ∫ _ in B, C := h
    _ = _ := by
      rw [integral_const]
      simp only [B, C, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
        EuclideanSpace.volume_ball_fin_three,
        ENNReal.ofReal_one, one_pow, one_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
      ring

end VacuumBellSeparation
