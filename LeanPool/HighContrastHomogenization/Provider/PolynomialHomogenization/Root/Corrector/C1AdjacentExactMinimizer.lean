/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1GradientMinimizerAttainment
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineAverageSlopeGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeCanonical
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBase
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Averages

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1AdjacentExactMinimizer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Adjacent exact finite-affine minimizers

Exact minimizers on two consecutive centered cubes have controlled boundary
slopes.  The proof reads the boundary slope from the average gradient of the
finite affine solution and estimates that average by the two residual energies.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- On a scale where the scalar-identity weak error is at most one, the
average gradient of a cube solution is controlled by its normalized
coefficient energy with a dimension-only constant. -/
theorem euclideanNorm_cubeAverageVec_solutionGradient_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (s : ℝ) (hs : 0 < s) (k : ℤ)
    (herror : scalarIdentityWeakError a s k ≤ 1)
    (w : Book.Ch03.CubeSolution (originCube d k) a) :
    euclideanNorm (cubeAverageVec (originCube d k) w.toH1.grad) ≤
      Real.sqrt (4 * (d : ℝ)) *
        Book.Ch03.h1EnergyNormOnCube (originCube d k) a w.toH1 := by
  let Q : TriadicCube d := originCube d k
  let U : Book.Ch02.Domain d := Book.Ch02.cubeDomain Q
  let aQ : Book.Ch02.CoeffOn U := a.coeffOn Q
  have hraw :=
    Book.Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
      U aQ w
  have hsigma : Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U aQ) ≤
      4 * (d : ℝ) := by
    calc
      Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U aQ) =
          Book.Ch02.coarseSigmaStarInvMatrixNorm Q a := by rfl
      _ ≤ (Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹ :=
        Book.Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q a hs (by norm_num)
      _ ≤ 4 * (d : ℝ) :=
        FiniteLipschitzCoreInternal.scalarIdentityWeakError_le_one_lowerEllipticity
          hs herror
  have hsigmaPos : 0 <
      Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U aQ) := by
    simpa only [U, aQ, Q, Book.Ch02.coarseSigmaStarInvMatrixNorm] using
      Book.Ch02.coarseSigmaStarInvMatrixNorm_pos Q a
  have hvariation : 0 ≤ Book.Ch02.variationEnergyValue U aQ w := by
    have hprod : 0 ≤
        Book.Ch02.matrixNorm (Book.Ch02.sigmaStarInvCoarse U aQ) *
          Book.Ch02.variationEnergyValue U aQ w :=
      (vecNormSq_nonneg _).trans hraw
    exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hprod) hsigmaPos
  have havg : Book.Ch02.averageGradient U aQ w =
      cubeAverageVec Q w.toH1.grad := by
    ext i
    rw [Book.Ch02.averageGradient, Book.Ch02.averageVec,
      Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
    rfl
  have henergy :
      Book.Ch03.h1EnergyNormOnCube Q a w.toH1 ^ 2 =
        Book.Ch02.variationEnergyValue U aQ w := by
    rw [← FiniteLipschitzCoreInternal.solutionEnergyNorm_eq_h1EnergyNormOnCube]
    exact Real.sq_sqrt hvariation
  have hsq :
      euclideanNorm (cubeAverageVec Q w.toH1.grad) ^ 2 ≤
        (Real.sqrt (4 * (d : ℝ)) *
          Book.Ch03.h1EnergyNormOnCube Q a w.toH1) ^ 2 := by
    rw [euclideanNorm_sq, ← havg, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 4 * (d : ℝ)), henergy]
    exact hraw.trans (mul_le_mul_of_nonneg_right hsigma hvariation)
  exact (sq_le_sq₀ (euclideanNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsq

end

end Root
end HighContrast
end HCPolySupport
