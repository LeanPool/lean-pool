/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatTimeDerivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing boundary terms for the separated heat pairing

The original Fourier pairing has a linear difference bound at time zero.
Disjoint test supports make its value at zero vanish by Parseval. Thus
the singular half-power primitive tends to zero at both endpoints.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

theorem spatialHeatFourierPairing_sub_zero_norm_le {t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialTestFunction) :
    ‖spatialHeatFourierPairing f g t - spatialHeatFourierPairing f g 0‖ ≤
      t * ∫ p : EuclideanSpace ℝ (Fin 3),
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖ := by
  unfold spatialHeatFourierPairing
  rw [← integral_sub (integrable_spatialHeatFourier_pairing ht f g)
    (integrable_spatialHeatFourier_pairing le_rfl f g), ← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((integrable_pow_norm_spatialFourier_product f g 2).const_mul t)
  refine Eventually.of_forall (fun p => ?_)
  simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [← sub_one_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have he : Real.exp (-t * ‖p‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
  rw [abs_of_nonpos (sub_nonpos.mpr he), norm_mul, Complex.norm_conj]
  have hb : -(Real.exp (-t * ‖p‖ ^ 2) - 1) ≤ t * ‖p‖ ^ 2 := by
    linarith [Real.add_one_le_exp (-t * ‖p‖ ^ 2)]
  calc
    _ ≤ (t * ‖p‖ ^ 2) * (‖spatialFourier f p‖ * ‖spatialFourier g p‖) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

/-- Spatial heat mass primitive. -/
noncomputable def spatialHeatMassPrimitive (m : ℝ) (f g : SpatialTestFunction) (t : ℝ) : ℂ :=
  ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
    spatialHeatFourierPairing f g t

theorem spatialHeatMassPrimitive_norm_le (m : ℝ) {t : ℝ} (ht : 0 < t)
    (f g : SpatialTestFunction) :
    ‖spatialHeatMassPrimitive m f g t‖ ≤
      (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t)) *
        ∫ p : EuclideanSpace ℝ (Fin 3), ‖conj (spatialFourier f p) * spatialFourier g p‖ := by
  rw [spatialHeatMassPrimitive, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (spatialHeatFourierPairing_norm_le ht.le f g) (by positivity)

theorem spatialHeatMassPrimitive_norm_le_at_zero (m : ℝ) {t d : ℝ}
    (ht : 0 < t) (hd : 0 < d) (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    ‖spatialHeatMassPrimitive m f g t‖ ≤
      t ^ (1 / 2 : ℝ) * ∫ p : EuclideanSpace ℝ (Fin 3),
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖ := by
  have hC := spatialHeatFourierPairing_sub_zero_norm_le ht.le f g
  rw [spatialHeatFourierPairing_zero_of_separated hd f g hsep, sub_zero] at hC
  have he : Real.exp (-(m ^ 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg m)) ht.le)
  have hpower : t ^ (-(1 / 2 : ℝ)) * t = t ^ (1 / 2 : ℝ) := by
    calc
      _ = t ^ (-(1 / 2 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add ht _ _).symm
      _ = _ := by norm_num
  rw [spatialHeatMassPrimitive, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ t ^ (-(1 / 2 : ℝ)) * ‖spatialHeatFourierPairing f g t‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_of_le_one_right (Real.rpow_nonneg ht.le _) he
    _ ≤ t ^ (-(1 / 2 : ℝ)) * (t * ∫ p : EuclideanSpace ℝ (Fin 3),
        (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖) :=
      mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [← mul_assoc, hpower]

theorem spatialHeatMassPrimitive_tendsto_zero_right (m : ℝ) {d : ℝ} (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    Tendsto (spatialHeatMassPrimitive m f g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      (Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by positivity))).tendsto.mono_left
        nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ (by simpa only [zero_mul] using
    (hp.mul_const (∫ p : EuclideanSpace ℝ (Fin 3),
      (‖p‖ ^ 2 * ‖spatialFourier f p‖) * ‖spatialFourier g p‖)))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact spatialHeatMassPrimitive_norm_le_at_zero m ht hd f g hsep

theorem spatialHeatMassPrimitive_tendsto_zero_atTop {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    Tendsto (spatialHeatMassPrimitive m f g) atTop (𝓝 0) := by
  have hp := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-(1 / 2 : ℝ))
    (m ^ 2) (by positivity)
  apply squeeze_zero_norm' _ (by simpa only [zero_mul] using
    (hp.mul_const (∫ p : EuclideanSpace ℝ (Fin 3), ‖conj
      (spatialFourier f p) * spatialFourier g p‖)))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact spatialHeatMassPrimitive_norm_le m ht f g

end VacuumBellSeparation
