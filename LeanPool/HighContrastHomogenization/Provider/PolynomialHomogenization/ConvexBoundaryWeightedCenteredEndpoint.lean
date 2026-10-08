/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalBallDomainMean
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightedEnergy

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.ConvexBoundaryWeightedCenteredEndpoint

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary-weighted centered fractional endpoint
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem ofReal_vecNormSq_sub_le_two_add
    (x m : Vec d) :
    ENNReal.ofReal (vecNormSq x) ≤
      2 * (ENNReal.ofReal (vecNormSq (x - m)) +
        ENNReal.ofReal (vecNormSq m)) := by
  have hreal : vecNormSq x ≤
      2 * (vecNormSq (x - m) + vecNormSq m) := by
    calc
      vecNormSq x = vecNormSq ((x - m) + m) := by congr 1; abel
      _ ≤ 2 * (vecNormSq (x - m) + vecNormSq m) := vecNormSq_add_le _ _
  calc
    ENNReal.ofReal (vecNormSq x) ≤
        ENNReal.ofReal (2 * (vecNormSq (x - m) + vecNormSq m)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (ENNReal.ofReal (vecNormSq (x - m)) +
        ENNReal.ofReal (vecNormSq m)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (vecNormSq_nonneg _) (vecNormSq_nonneg _)]

/-- Centering at the domain mean costs the weighted energy around any
reference vector plus its squared displacement from the domain mean. -/
theorem euclideanBoundaryWeightedCenteredEnergy_le_around_add_meanShift
    {U : Set (Vec d)} {G : Vec d → Vec d}
    (hG : Integrable G (volume.restrict U)) (p : ℝ) (m : Vec d) :
    euclideanBoundaryWeightedCenteredEnergy U p G ≤
      2 * euclideanBoundaryWeightedEnergyAround U p G m +
        2 * ENNReal.ofReal (vecNormSq (m - volumeAverageVec U G)) *
          euclideanBoundaryWeightMoment U p := by
  let q := m - volumeAverageVec U G
  let f : Vec d → ℝ≥0∞ := fun x =>
    euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (G x - m))
  let g : Vec d → ℝ≥0∞ := fun x =>
    euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq q)
  have hf : AEMeasurable f (volume.restrict U) :=
    (measurable_euclideanBoundaryWeight U p).aemeasurable.mul
      ((continuous_vecNormSq.measurable.comp_aemeasurable
        (hG.aestronglyMeasurable.aemeasurable.sub aemeasurable_const)).ennreal_ofReal)
  have hpoint : ∀ x,
      euclideanBoundaryWeight U p x *
          ENNReal.ofReal (vecNormSq (G x - volumeAverageVec U G)) ≤
        2 * (f x + g x) := by
    intro x
    have hnorm := ofReal_vecNormSq_sub_le_two_add
      (G x - volumeAverageVec U G) q
    rw [show (G x - volumeAverageVec U G) - q = G x - m by
      dsimp only [q]; abel] at hnorm
    have hmul := mul_le_mul_right hnorm (euclideanBoundaryWeight U p x)
    change euclideanBoundaryWeight U p x *
      ENNReal.ofReal (vecNormSq (G x - volumeAverageVec U G)) ≤ _
    calc
      _ ≤ euclideanBoundaryWeight U p x *
          (2 * (ENNReal.ofReal (vecNormSq (G x - m)) +
            ENNReal.ofReal (vecNormSq q))) := hmul
      _ = 2 * (f x + g x) := by
        dsimp only [f, g]
        ring
  unfold euclideanBoundaryWeightedCenteredEnergy
    euclideanBoundaryWeightedEnergyAround euclideanBoundaryWeightMoment
  calc
    eVolumeAverage U (fun x => euclideanBoundaryWeight U p x *
        ENNReal.ofReal (vecNormSq (G x - volumeAverageVec U G))) ≤
        eVolumeAverage U (fun x => 2 * (f x + g x)) :=
      ENNReal.div_le_div_right (lintegral_mono hpoint) _
    _ = 2 * (eVolumeAverage U f + eVolumeAverage U g) := by
      rw [eVolumeAverage_const_mul U 2 (by norm_num)]
      unfold eVolumeAverage
      rw [lintegral_add_left' hf]
      simp only [div_eq_mul_inv, add_mul, mul_add]
    _ = 2 * eVolumeAverage U f +
        2 * ENNReal.ofReal (vecNormSq q) *
          eVolumeAverage U (euclideanBoundaryWeight U p) := by
      have hqtop : ENNReal.ofReal (vecNormSq q) ≠ ∞ := ENNReal.ofReal_ne_top
      have hg : eVolumeAverage U g = ENNReal.ofReal (vecNormSq q) *
          eVolumeAverage U (euclideanBoundaryWeight U p) := by
        rw [show g = fun x => ENNReal.ofReal (vecNormSq q) *
          euclideanBoundaryWeight U p x by
            funext x
            dsimp only [g]
            rw [mul_comm]]
        exact eVolumeAverage_const_mul U _ hqtop _
      rw [hg]
      ring
    _ = _ := by rfl

end

end HighContrast
end HCPolySupport
