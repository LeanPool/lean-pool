/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatConvolution
public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatFourierFubini

/-!
# Absolute convergence of the separated heat/spatial covariance integral

Actual separation is used only where both original tests are nonzero.
It bounds the full joint integrand by the product of a convergent
off-diagonal heat moment and the two absolute test functions.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set

/-- Separated heat pairing. -/
noncomputable def separatedHeatPairing (m : ℝ) (f g : SpatialTestFunction)
    (txy : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) : ℂ :=
  (((1 / (2 * Real.sqrt Real.pi)) *
      (txy.1 ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * txy.1)) *
        spatialHeatKernel txy.1 (txy.2.1 - txy.2.2) : ℝ) : ℂ) *
      (f.1 txy.2.1 : ℂ) * (g.1 txy.2.2 : ℂ)

theorem heatBesselIntegrand_one_nonneg (m r : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ heatBesselIntegrand 1 m r t := by
  unfold heatBesselIntegrand
  positivity

theorem heatBesselIntegrand_one_mono_radius (m : ℝ) {d r t : ℝ}
    (hd : 0 ≤ d) (hdr : d ≤ r) (ht : 0 < t) :
    heatBesselIntegrand 1 m r t ≤ heatBesselIntegrand 1 m d t := by
  unfold heatBesselIntegrand
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : d ^ 2 ≤ r ^ 2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * t by positivity)
  linarith

theorem norm_separatedHeatPairing_le {m d : ℝ} (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖)
    {t : ℝ} (ht : 0 < t)
    (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ‖separatedHeatPairing m f g (t, xy)‖ ≤
      ((1 / (16 * Real.pi ^ 2)) * heatBesselIntegrand 1 m d t) *
        (‖f.1 xy.1‖ * ‖g.1 xy.2‖) := by
  simp only [separatedHeatPairing, spatialHeat_subordination_integrand ht,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ 1 / (16 * Real.pi ^ 2) by positivity),
    abs_of_nonneg (heatBesselIntegrand_one_nonneg _ _ ht)]
  by_cases hf : f.1 xy.1 = 0
  · simp [hf]
  by_cases hg : g.1 xy.2 = 0
  · simp [hg]
  have h := heatBesselIntegrand_one_mono_radius m hd.le (hsep _ _ hf hg) ht
  have hc := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (16 * Real.pi ^ 2) by positivity)
  simpa only [Real.norm_eq_abs, mul_assoc] using
    mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem integrable_separatedHeatPairing {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    Integrable (separatedHeatPairing m f g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
  have hf : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hg : Integrable g.1 := g.2.1.continuous.integrable_of_hasCompactSupport g.2.2
  have hmajor := ((integrableOn_heatBesselIntegrand 1 hm hd).const_mul
    (1 / (16 * Real.pi ^ 2))).mul_prod (hf.norm.mul_prod hg.norm)
  apply hmajor.mono'
  · exact (show Measurable (separatedHeatPairing m f g) by
      unfold separatedHeatPairing spatialHeatKernel
      have hfm := f.2.1.continuous.measurable
      have hgm := g.2.1.continuous.measurable
      fun_prop).aestronglyMeasurable
  · have htpos : ∀ᵐ txy : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)), 0 < txy.1 := by
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall (fun _ => ht)
    filter_upwards [htpos] with txy ht
    exact norm_separatedHeatPairing_le hd f g hsep ht txy.2

theorem integral_separatedHeatPairing_time {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖)
    (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (∫ t in Ioi (0 : ℝ), separatedHeatPairing m f g (t, xy)) =
      ((m / (4 * Real.pi ^ 2 * ‖xy.1 - xy.2‖) *
        besselKReal 1 (m * ‖xy.1 - xy.2‖) : ℝ) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) := by
  by_cases hf : f.1 xy.1 = 0
  · simp [separatedHeatPairing, hf]
  by_cases hg : g.1 xy.2 = 0
  · simp [separatedHeatPairing, hg]
  have hxy : xy.1 - xy.2 ≠ 0 := norm_pos_iff.mp (hd.trans_le (hsep _ _ hf hg))
  simp only [separatedHeatPairing]
  rw [integral_mul_const, integral_mul_const, integral_complex_ofReal,
    spatialHeat_integral_eq_fieldBessel hm _ hxy]

end VacuumBellSeparation
