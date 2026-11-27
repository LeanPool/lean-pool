/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialMomentumHeatSubordination
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Genuine time derivative of the spatial heat pairing

The derivative is taken under the original momentum integral using the
integrable quadratic Fourier moment. No differentiability or boundary
condition is assumed for a putative kernel representation.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

/-- Spatial heat Fourier pairing given by `∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2)
: ℂ) * (conj (spatialFourier f p) * spatialFourier g p)`. -/
noncomputable def spatialHeatFourierPairing (f g : SpatialTestFunction) (t : ℝ) : ℂ :=
  ∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
    (conj (spatialFourier f p) * spatialFourier g p)

/-- Spatial heat Fourier derivative. -/
noncomputable def spatialHeatFourierDerivative (f g : SpatialTestFunction) (t : ℝ) : ℂ :=
  ∫ p : EuclideanSpace ℝ (Fin 3), (-(‖p‖ ^ 2 : ℝ) : ℂ) *
    ((Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
      (conj (spatialFourier f p) * spatialFourier g p))

theorem integrable_spatialHeatFourier_pairing {t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialTestFunction) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
      (conj (spatialFourier f p) * spatialFourier g p)) := by
  apply (integrable_spatialFourier_product f g).norm.mono'
  · exact (show Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p)) by
      have hf := continuous_spatialFourier f
      have hg := continuous_spatialFourier g
      fun_prop).aestronglyMeasurable
  · refine Eventually.of_forall (fun p => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _)))

theorem spatialHeatFourier_derivative_integrand_bound {t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖(-(‖p‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
      (conj (spatialFourier f p) * spatialFourier g p))‖ ≤
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖ := by
  simp only [norm_mul, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖p‖), abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-t * ‖p‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
  calc
    _ ≤ ‖p‖ ^ 2 * (1 * (‖spatialFourier f p‖ * ‖spatialFourier g p‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right he (by positivity)) (sq_nonneg _)
    _ = _ := by ring

theorem hasDerivAt_spatialHeatFourier_pairing {t : ℝ} (ht : 0 < t)
    (f g : SpatialTestFunction) :
    HasDerivAt (spatialHeatFourierPairing f g) (spatialHeatFourierDerivative f g t) t := by
  have hc : ∀ s : ℝ, Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      (Real.exp (-s * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p)) := by
    intro s
    have hf := continuous_spatialFourier f
    have hg := continuous_spatialFourier g
    fun_prop
  have hd : ∀ p : EuclideanSpace ℝ (Fin 3), ∀ s : ℝ,
      HasDerivAt (fun x : ℝ => (Real.exp (-x * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p))
        ((-(‖p‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-s * ‖p‖ ^ 2) : ℂ) *
          (conj (spatialFourier f p) * spatialFourier g p))) s := by
    intro p s
    have h := (((hasDerivAt_id s).neg.mul_const (‖p‖ ^ 2)).exp.ofReal_comp).mul_const
      (conj (spatialFourier f p) * spatialFourier g p)
    simpa only [Pi.neg_def, id_eq, neg_one_mul, Complex.ofReal_mul, Complex.ofReal_neg,
      mul_assoc, mul_comm, mul_left_comm] using h
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s p => (Real.exp (-s * ‖p‖ ^ 2) : ℂ) *
      (conj (spatialFourier f p) * spatialFourier g p))
    (F' := fun s p => (-(‖p‖ ^ 2 : ℝ) : ℂ) *
      ((Real.exp (-s * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p)))
    (bound := fun p => (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖)
    (Ioi_mem_nhds ht) (Eventually.of_forall (fun s => (hc s).aestronglyMeasurable))
    (integrable_spatialHeatFourier_pairing ht.le f g)
    (show AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (-(‖p‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p))) volume from
      ((Complex.continuous_ofReal.comp (continuous_norm.pow 2)).neg.mul
        (hc t)).aestronglyMeasurable)
    (Eventually.of_forall (fun p s hs => spatialHeatFourier_derivative_integrand_bound hs.le f g p))
    (integrable_pow_norm_spatialFourier_product f g 2)
    (Eventually.of_forall (fun p s _ => hd p s))
  exact h.2

theorem spatialHeatFourierPairing_norm_le {t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialTestFunction) :
    ‖spatialHeatFourierPairing f g t‖ ≤
      ∫ p : EuclideanSpace ℝ (Fin 3), ‖conj (spatialFourier f p) * spatialFourier g p‖ := by
  apply norm_integral_le_of_norm_le (integrable_spatialFourier_product f g).norm
  refine Eventually.of_forall (fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _)))

theorem spatialHeatFourierPairing_zero_of_separated {d : ℝ} (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    spatialHeatFourierPairing f g 0 = 0 := by
  simp only [spatialHeatFourierPairing, neg_zero, zero_mul, Real.exp_zero,
    Complex.ofReal_one, one_mul]
  rw [integral_spatialFourier_product]
  have hfg : (fun x : EuclideanSpace ℝ (Fin 3) => (f.1 x : ℂ) * (g.1 x : ℂ)) = 0 := by
    funext x
    by_cases hf : f.1 x = 0
    · simp [hf]
    by_cases hg : g.1 x = 0
    · simp [hg]
    have h := hsep x x hf hg
    simp only [sub_self, norm_zero] at h
    exact (not_le_of_gt hd h).elim
  rw [hfg, integral_zero', mul_zero]

end VacuumBellSeparation
