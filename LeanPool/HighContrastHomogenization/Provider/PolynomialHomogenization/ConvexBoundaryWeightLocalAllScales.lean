/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightLocalScaling

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryWeightLocalAllScales

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Homogeneous local boundary moments at every radius

Small radii use convex localization. Large radii are absorbed by the global
negative moment and the outer ball sandwich.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The homogeneous local negative boundary-distance moment holds for every
positive radius, with one structural constant. -/
theorem exists_bound_lintegral_local_euclideanBoundaryWeight_all_scales
    (hd : 1 ≤ d) {rho Rad p : ℝ} (hrho : 0 < rho) (hRad : 0 < Rad)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad → ∀ (z : Vec d) {r : ℝ}, 0 < r →
          (∫⁻ x in U ∩ euclideanBallAt z r,
            euclideanBoundaryWeight U p x ∂volume) ≤
              C * ENNReal.ofReal (r ^ ((d : ℝ) - p)) := by
  obtain ⟨Clocal, hClocalTop, hClocal⟩ :=
    exists_bound_lintegral_local_euclideanBoundaryWeight_scaled
      hd hrho hRad hp0 hp1
  let B : ℝ≥0∞ := ENNReal.ofReal ((2 * Rad) ^ d) *
    ENNReal.ofReal (((d : ℝ) / rho) ^ p / (1 - p))
  let Rpow : ℝ≥0∞ := ENNReal.ofReal (Rad ^ ((d : ℝ) - p))
  let C : ℝ≥0∞ := Clocal + B * Rpow⁻¹
  have hexp : 0 < (d : ℝ) - p := by
    have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hdreal, hp1]
  have hRpow0 : Rpow ≠ 0 := by
    dsimp only [Rpow]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hRad _)
  have hRpowTop : Rpow ≠ ⊤ := ENNReal.ofReal_ne_top
  have hBTop : B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨C, ENNReal.add_ne_top.mpr ⟨hClocalTop,
    ENNReal.mul_ne_top hBTop (ENNReal.inv_ne_top.mpr hRpow0)⟩, ?_⟩
  intro U hU hsand z r hr
  by_cases hrRad : r ≤ Rad
  · by_cases hne : (U ∩ euclideanBallAt z r).Nonempty
    · exact (hClocal U hU hsand z hr hrRad hne).trans
        (mul_le_mul_left (le_add_right le_rfl) _)
    · have hempty : U ∩ euclideanBallAt z r = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
      exact bot_le
  · have hRadR : Rad < r := lt_of_not_ge hrRad
    obtain ⟨_hrho, _hRad, c, _hinner, houter⟩ := hsand
    have hvol : volume U ≤ ENNReal.ofReal ((2 * Rad) ^ d) := by
      calc
        volume U ≤ volume (Metric.ball c Rad) := measure_mono fun x hx =>
          euclideanBallAt_subset_metricBall c hRad (houter hx)
        _ = ENNReal.ofReal ((2 * Rad) ^ d) := volume_ball_eq c hRad
    have hglobal : (∫⁻ x in U,
        euclideanBoundaryWeight U p x ∂volume) ≤ B := by
      calc
        (∫⁻ x in U, euclideanBoundaryWeight U p x ∂volume) ≤
            volume U * ENNReal.ofReal
              (((d : ℝ) / rho) ^ p / (1 - p)) :=
          lintegral_euclideanBoundaryWeight_le hd hU
            ⟨_hrho, _hRad, c, _hinner, houter⟩ hp0 hp1
        _ ≤ B := by
          exact mul_le_mul_left hvol _
    have hrpow : Rpow ≤ ENNReal.ofReal (r ^ ((d : ℝ) - p)) := by
      dsimp only [Rpow]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow hRad.le hRadR.le hexp.le)
    calc
      (∫⁻ x in U ∩ euclideanBallAt z r,
          euclideanBoundaryWeight U p x ∂volume) ≤
          ∫⁻ x in U, euclideanBoundaryWeight U p x ∂volume :=
        lintegral_mono_set Set.inter_subset_left
      _ ≤ B := hglobal
      _ = (B * Rpow⁻¹) * Rpow := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hRpow0 hRpowTop, mul_one]
      _ ≤ (B * Rpow⁻¹) *
          ENNReal.ofReal (r ^ ((d : ℝ) - p)) :=
        by simpa only [mul_comm] using mul_le_mul_left hrpow (B * Rpow⁻¹)
      _ ≤ C * ENNReal.ofReal (r ^ ((d : ℝ) - p)) :=
        mul_le_mul_left (le_add_left le_rfl) _

end

end HighContrast
end HCPolySupport
