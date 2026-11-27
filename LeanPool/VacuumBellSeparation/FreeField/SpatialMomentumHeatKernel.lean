/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatSeparatedIntegrability

/-!
# Actual separated momentum heat-kernel integrability

The negative three-halves heat weight has the prefactor −1/(32π²) in
this derivation. Its full time/position integral is absolutely convergent for
separated original tests, and its scalar time integral is the actual K2
kernel. The Fourier identification is assembled separately.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set

theorem spatialHeat_momentum_subordination_integrand {μ t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin 3)) :
    (-1 / (4 * Real.sqrt Real.pi)) *
        (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w =
      -(1 / (32 * Real.pi ^ 2)) * heatBesselIntegrand 2 μ ‖w‖ t := by
  have hp : t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) * t⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2 : ℝ) + (-1 : ℝ) by norm_num,
      Real.rpow_add ht, Real.rpow_neg_one]
  calc
    _ = (-1 / (2 * t)) * ((1 / (2 * Real.sqrt Real.pi)) *
        (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w) := by
      rw [hp]
      field_simp; ring
    _ = (-1 / (2 * t)) * ((1 / (16 * Real.pi ^ 2)) * heatBesselIntegrand 1 μ ‖w‖ t) := by
      rw [spatialHeat_subordination_integrand ht]
    _ = _ := by
      unfold heatBesselIntegrand
      norm_num only [Int.reduceNeg, Int.reduceAdd, zpow_neg, zpow_ofNat]
      field_simp [ht.ne', Real.pi_ne_zero]; ring

theorem spatialHeat_integral_eq_momentumBessel {μ : ℝ} (hμ : 0 < μ)
    (w : EuclideanSpace ℝ (Fin 3)) (hw : w ≠ 0) :
    (∫ t in Ioi (0 : ℝ), (-1 / (4 * Real.sqrt Real.pi)) *
      (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w) =
      -(μ ^ 2) / (4 * Real.pi ^ 2 * ‖w‖ ^ 2) * besselKReal 2 (μ * ‖w‖) := by
  have heq : (∫ t in Ioi (0 : ℝ), (-1 / (4 * Real.sqrt Real.pi)) *
      (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w) =
      ∫ t in Ioi (0 : ℝ), -(1 / (32 * Real.pi ^ 2)) * heatBesselIntegrand 2 μ ‖w‖ t :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => spatialHeat_momentum_subordination_integrand (μ := μ) ht w)
  rw [heq, integral_const_mul, heatMomentumKernel_eq_bessel hμ (norm_pos_iff.mpr hw)]

/-- Separated momentum heat pairing. -/
noncomputable def separatedMomentumHeatPairing (m : ℝ) (f g : SpatialTestFunction)
    (txy : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) : ℂ :=
  (((-1 / (4 * Real.sqrt Real.pi)) *
      (txy.1 ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * txy.1)) *
        spatialHeatKernel txy.1 (txy.2.1 - txy.2.2) : ℝ) : ℂ) *
      (f.1 txy.2.1 : ℂ) * (g.1 txy.2.2 : ℂ)

theorem heatBesselIntegrand_two_nonneg (m r : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ heatBesselIntegrand 2 m r t := by
  unfold heatBesselIntegrand
  positivity

theorem heatBesselIntegrand_two_mono_radius (m : ℝ) {d r t : ℝ}
    (hd : 0 ≤ d) (hdr : d ≤ r) (ht : 0 < t) :
    heatBesselIntegrand 2 m r t ≤ heatBesselIntegrand 2 m d t := by
  unfold heatBesselIntegrand
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : d ^ 2 ≤ r ^ 2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * t by positivity)
  linarith

theorem norm_separatedMomentumHeatPairing_le {m d : ℝ} (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖)
    {t : ℝ} (ht : 0 < t)
    (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ‖separatedMomentumHeatPairing m f g (t, xy)‖ ≤
      ((1 / (32 * Real.pi ^ 2)) * heatBesselIntegrand 2 m d t) *
        (‖f.1 xy.1‖ * ‖g.1 xy.2‖) := by
  simp only [separatedMomentumHeatPairing, spatialHeat_momentum_subordination_integrand ht,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_neg, abs_of_nonneg (show 0 ≤ 1 / (32 * Real.pi ^ 2) by positivity),
    abs_of_nonneg (heatBesselIntegrand_two_nonneg _ _ ht)]
  by_cases hf : f.1 xy.1 = 0
  · simp [hf]
  by_cases hg : g.1 xy.2 = 0
  · simp [hg]
  have h := heatBesselIntegrand_two_mono_radius m hd.le (hsep _ _ hf hg) ht
  have hc := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (32 * Real.pi ^ 2) by positivity)
  simpa only [Real.norm_eq_abs, mul_assoc] using
    mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem integrable_separatedMomentumHeatPairing {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    Integrable (separatedMomentumHeatPairing m f g)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
  have hf : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hg : Integrable g.1 := g.2.1.continuous.integrable_of_hasCompactSupport g.2.2
  have hmajor := ((integrableOn_heatBesselIntegrand 2 hm hd).const_mul
    (1 / (32 * Real.pi ^ 2))).mul_prod (hf.norm.mul_prod hg.norm)
  apply hmajor.mono'
  · exact (show Measurable (separatedMomentumHeatPairing m f g) by
      unfold separatedMomentumHeatPairing spatialHeatKernel
      have hfm := f.2.1.continuous.measurable
      have hgm := g.2.1.continuous.measurable
      fun_prop).aestronglyMeasurable
  · have htpos : ∀ᵐ txy : ℝ × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)), 0 < txy.1 := by
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall (fun _ => ht)
    filter_upwards [htpos] with txy ht
    exact norm_separatedMomentumHeatPairing_le hd f g hsep ht txy.2

theorem integral_separatedMomentumHeatPairing_time {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖)
    (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (∫ t in Ioi (0 : ℝ), separatedMomentumHeatPairing m f g (t, xy)) =
      ((-(m ^ 2) / (4 * Real.pi ^ 2 * ‖xy.1 - xy.2‖ ^ 2) *
        besselKReal 2 (m * ‖xy.1 - xy.2‖) : ℝ) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) := by
  by_cases hf : f.1 xy.1 = 0
  · simp [separatedMomentumHeatPairing, hf]
  by_cases hg : g.1 xy.2 = 0
  · simp [separatedMomentumHeatPairing, hg]
  have hxy : xy.1 - xy.2 ≠ 0 := norm_pos_iff.mp (hd.trans_le (hsep _ _ hf hg))
  simp only [separatedMomentumHeatPairing]
  rw [integral_mul_const, integral_mul_const, integral_complex_ofReal,
    spatialHeat_integral_eq_momentumBessel hm _ hxy]

end VacuumBellSeparation
