/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AntiVacuityInstances
public import LeanPool.HighContrastHomogenization.Analytic.SingularKernel
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightMoment
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyPositiveRow

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryWeightedEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centering the boundary-weighted energy

The boundary-weighted `L²` energy is split into its domain-centered part and
the contribution of the domain average. The latter is controlled by the
negative boundary-distance moment on a ball-sandwiched convex domain.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The normalized boundary-distance-weighted energy of a vector field. -/
@[expose]
def euclideanBoundaryWeightedEnergy (U : Set (Vec d)) (p : ℝ)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eVolumeAverage U fun x =>
    euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (F x))

/-- The normalized boundary-weighted energy after subtracting the domain
average. -/
@[expose]
def euclideanBoundaryWeightedCenteredEnergy (U : Set (Vec d)) (p : ℝ)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eVolumeAverage U fun x => euclideanBoundaryWeight U p x *
    ENNReal.ofReal (vecNormSq (F x - volumeAverageVec U F))

private theorem ofReal_vecNormSq_le_centered_add_mean_boundary
    (x m : Vec d) :
    ENNReal.ofReal (vecNormSq x) ≤
      2 * (ENNReal.ofReal (vecNormSq (x - m)) +
        ENNReal.ofReal (vecNormSq m)) := by
  have hreal : vecNormSq x ≤
      2 * (vecNormSq (x - m) + vecNormSq m) := by
    calc
      vecNormSq x = vecNormSq ((x - m) + m) := by congr 1; abel
      _ ≤ 2 * (vecNormSq (x - m) + vecNormSq m) :=
        vecNormSq_add_le _ _
  calc
    ENNReal.ofReal (vecNormSq x) ≤
        ENNReal.ofReal (2 * (vecNormSq (x - m) + vecNormSq m)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (ENNReal.ofReal (vecNormSq (x - m)) +
        ENNReal.ofReal (vecNormSq m)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (vecNormSq_nonneg _) (vecNormSq_nonneg _)]

/-- Centering separates the only genuinely analytic Hardy--Poincare term
from a spatially constant boundary moment. -/
theorem euclideanBoundaryWeightedEnergy_le_centered_add_mean
    {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict U)) (p : ℝ) :
    euclideanBoundaryWeightedEnergy U p F ≤
      2 * euclideanBoundaryWeightedCenteredEnergy U p F +
        2 * ENNReal.ofReal (vecNormSq (volumeAverageVec U F)) *
          euclideanBoundaryWeightMoment U p := by
  let m := volumeAverageVec U F
  let g : Vec d → ℝ≥0∞ := fun x =>
    euclideanBoundaryWeight U p x *
      ENNReal.ofReal (vecNormSq (F x - m))
  let h : Vec d → ℝ≥0∞ := fun x =>
    euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq m)
  have hg : AEMeasurable g (volume.restrict U) := by
    exact (measurable_euclideanBoundaryWeight U p).aemeasurable.mul
      ((continuous_vecNormSq.measurable.comp_aemeasurable
        (hF.aestronglyMeasurable.aemeasurable.sub aemeasurable_const)).ennreal_ofReal)
  have hpoint : ∀ x,
      euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (F x)) ≤
        2 * (g x + h x) := by
    intro x
    have hx := ofReal_vecNormSq_le_centered_add_mean_boundary (F x) m
    have hmul := mul_le_mul_right hx (euclideanBoundaryWeight U p x)
    change euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (F x)) ≤ _
    calc
      euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (F x)) ≤
          euclideanBoundaryWeight U p x *
            (2 * (ENNReal.ofReal (vecNormSq (F x - m)) +
              ENNReal.ofReal (vecNormSq m))) := hmul
      _ = 2 * (g x + h x) := by
        dsimp only [g, h]
        ring
  unfold euclideanBoundaryWeightedEnergy
    euclideanBoundaryWeightedCenteredEnergy euclideanBoundaryWeightMoment
  change eVolumeAverage U (fun x =>
      euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (F x))) ≤ _
  calc
    eVolumeAverage U (fun x =>
        euclideanBoundaryWeight U p x * ENNReal.ofReal (vecNormSq (F x))) ≤
        eVolumeAverage U (fun x => 2 * (g x + h x)) :=
      ENNReal.div_le_div_right (lintegral_mono hpoint) _
    _ = 2 * (eVolumeAverage U g + eVolumeAverage U h) := by
      rw [eVolumeAverage_const_mul U 2 (by norm_num)]
      unfold eVolumeAverage
      rw [lintegral_add_left' hg]
      simp only [div_eq_mul_inv, add_mul, mul_add]
    _ = 2 * eVolumeAverage U g +
        2 * ENNReal.ofReal (vecNormSq m) *
          eVolumeAverage U (euclideanBoundaryWeight U p) := by
      have hm : ENNReal.ofReal (vecNormSq m) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hh : eVolumeAverage U h =
          ENNReal.ofReal (vecNormSq m) *
            eVolumeAverage U (euclideanBoundaryWeight U p) := by
        rw [show h = fun x => ENNReal.ofReal (vecNormSq m) *
          euclideanBoundaryWeight U p x by
            funext x
            dsimp only [h]
            rw [mul_comm]]
        exact eVolumeAverage_const_mul U _ hm _
      rw [hh]
      ring
    _ = _ := by rfl

/-- The mean part of the fractional boundary-weighted energy has an explicit
ball-sandwich bound. -/
theorem euclideanBoundaryWeightedEnergy_le_centered_add_explicitMean
    (hd : 1 ≤ d) {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {rho Rad s : ℝ} (hsand : HasBallSandwich U rho Rad)
    (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U)) :
    euclideanBoundaryWeightedEnergy U (2 * s) F ≤
      2 * euclideanBoundaryWeightedCenteredEnergy U (2 * s) F +
        2 * ENNReal.ofReal (vecNormSq (volumeAverageVec U F)) *
          ENNReal.ofReal (((d : ℝ) / rho) ^ (2 * s) / (1 - 2 * s)) := by
  refine (euclideanBoundaryWeightedEnergy_le_centered_add_mean hF (2 * s)).trans ?_
  exact add_le_add le_rfl
    (mul_le_mul_right
      (euclideanBoundaryWeightMoment_two_mul_le hd hU hsand hs) _)

end

end HighContrast
end HCPolySupport
