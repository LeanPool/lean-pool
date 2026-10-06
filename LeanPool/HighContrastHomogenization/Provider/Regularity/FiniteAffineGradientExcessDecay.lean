/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcessStep

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineGradientExcessDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Iteration of finite affine gradient excess

This module iterates the ruled fixed-gap contraction and controls the terminal
remainder band by normalized centered-cube restriction.
-/

namespace HCPolySupport
namespace HighContrast

open scoped ENNReal

noncomputable section

/-- Restricting the gradient excess by `N` centered scales loses at most the
corresponding normalized-volume factor. -/
theorem finiteAffineGradientExcess_sub_nat_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (N : ℕ)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    finiteAffineGradientExcess a (k - (N : ℤ)) m u ≤
      ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ))) *
        finiteAffineGradientExcess a k m u := by
  let q : ℝ≥0∞ := ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ)))
  have hqpos : 0 < (((((3 ^ d) ^ N : ℕ) : ℝ))) := by positivity
  have hqzero : q ≠ 0 := by
    dsimp [q]
    exact ENNReal.ofReal_ne_zero_iff.mpr hqpos
  have hqtop : q ≠ ∞ := by
    dsimp [q]
    exact ENNReal.ofReal_ne_top
  apply finiteAffineGradientExcess_le_mul_of_forall_candidate
    a u q hqzero hqtop
  intro e
  let v := finiteAffineGradientResidual a hkm u e
  let vR := finiteCubeSolutionRestriction a (by omega : k - (N : ℤ) ≤ k) v
  let w := finiteAffineGradientResidual a (by omega : k - (N : ℤ) ≤ m) u e
  have henergyEq : Book.Ch03.h1EnergyNormOnCube
        (originCube d (k - (N : ℤ))) a w.toH1 =
      Book.Ch03.h1EnergyNormOnCube
        (originCube d (k - (N : ℤ))) a vR.toH1 := by
    unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
    simp only [w, vR, v, finiteAffineGradientResidual_grad,
      finiteCubeSolutionRestriction_grad]
  have hrestrict := h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_nat_le
    a k N v
  have hpoint : finiteAffineGradientExcess a (k - (N : ℤ)) m u ≤
      ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ)) *
        Book.Ch03.h1EnergyNormOnCube (originCube d k) a v.toH1) := by
    calc
      finiteAffineGradientExcess a (k - (N : ℤ)) m u ≤
          ENNReal.ofReal
            (Book.Ch03.h1EnergyNormOnCube
              (originCube d (k - (N : ℤ))) a w.toH1) :=
        finiteAffineGradientExcess_le_residualEnergy a
          (by omega : k - (N : ℤ) ≤ m) u e
      _ = ENNReal.ofReal
            (Book.Ch03.h1EnergyNormOnCube
              (originCube d (k - (N : ℤ))) a vR.toH1) := by rw [henergyEq]
      _ ≤ ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ)) *
          Book.Ch03.h1EnergyNormOnCube (originCube d k) a v.toH1) :=
        ENNReal.ofReal_mono (by simpa only [vR, v] using hrestrict)
  calc
    finiteAffineGradientExcess a (k - (N : ℤ)) m u ≤
        ENNReal.ofReal (((((3 ^ d) ^ N : ℕ) : ℝ)) *
          Book.Ch03.h1EnergyNormOnCube (originCube d k) a v.toH1) := hpoint
    _ = q * ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d k) a v.toH1) := by
      dsimp [q]
      rw [ENNReal.ofReal_mul hqpos.le]
    _ = q * weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m e).toH1.grad x) := by
      rw [weightedGradNorm_finiteAffineGradientResidual a hkm u e]

end

end HighContrast
end HCPolySupport
