/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleGradientGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcessRateSelection

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleExcessRigidityPrep

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-excess preparation for reverse Liouville rigidity

This module records the zero-slope terminal bound and the elementary choice of
an excess-decay exponent strictly above the frozen growth exponent.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- At the outer scale, the finite affine gradient excess is bounded by the
energy of the solution itself; the zero-boundary affine solution has zero
gradient a.e. by homogeneity. -/
theorem finiteAffineGradientExcess_self_le_solutionEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) :
    finiteAffineGradientExcess a m m u ≤
      ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1) := by
  have hzero : (finiteAffineSolution a m (0 : Vec d)).toH1.grad
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        fun _ => (0 : Vec d) := by
    have h := finiteAffineSolution_grad_smul a m 0 (0 : Vec d)
    simpa only [zero_smul] using! h
  have hfield : (fun x => u.toH1.grad x -
      (finiteAffineSolution a m (0 : Vec d)).toH1.grad x)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))] u.toH1.grad := by
    filter_upwards [hzero] with x hx
    simp only [hx, sub_zero]
  calc
    finiteAffineGradientExcess a m m u ≤
        weightedGradNorm
          (a.coeffOn (originCube d m)).toCoeffField
          (openCubeSet (originCube d m))
          (fun x => u.toH1.grad x -
            (finiteAffineSolution a m (0 : Vec d)).toH1.grad x) :=
      finiteAffineGradientExcess_le a m m u 0
    _ = weightedGradNorm
          (a.coeffOn (originCube d m)).toCoeffField
          (openCubeSet (originCube d m)) u.toH1.grad :=
      weightedGradNorm_congr_ae _ _ hfield
    _ = ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube _ _ _

/-- Every frozen exponent in `(0,1)` admits a decay exponent strictly above
both it and `1/2`, as required by the source-level reverse-Liouville argument. -/
theorem exists_excessDecayExponent_gt_max_half
    {theta : ℝ} (htheta : theta < 1) :
    ∃ eta : ℝ, max theta (1 / 2 : ℝ) < eta ∧ eta < 1 := by
  let eta : ℝ := (max theta (1 / 2 : ℝ) + 1) / 2
  have hmax : max theta (1 / 2 : ℝ) < 1 :=
    max_lt htheta (by norm_num)
  refine ⟨eta, ?_, ?_⟩ <;> dsimp only [eta] <;> linarith only [hmax]

end

end HighContrast
end HCPolySupport
