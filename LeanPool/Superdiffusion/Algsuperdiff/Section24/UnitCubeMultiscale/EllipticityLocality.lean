/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# EllipticityLocality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Root locality of CoarseGraining multiscale ellipticity

The lower and upper multiscale ellipticity values at the origin cube depend
only on the coefficient there, not on a chosen compatible global family.
-/

namespace Algsuperdiff.Section24.UnitCubeMultiscale

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

variable {d : ℕ}

private theorem coarseBMatrixNorm_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    coarseBMatrixNorm R F = coarseBMatrixNorm R G := by
  unfold coarseBMatrixNorm
  rw [bCoarse_eq_ofAEEq (coeffOn_aeeq_of_root_aeeq a F G hF hG hk hR)]

private theorem coarseSigmaStarInvMatrixNorm_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    coarseSigmaStarInvMatrixNorm R F = coarseSigmaStarInvMatrixNorm R G := by
  unfold coarseSigmaStarInvMatrixNorm
  rw [sigmaStarInvCoarse_eq_ofAEEq
    (coeffOn_aeeq_of_root_aeeq a F G hF hG hk hR)]

private theorem maxDescendantBMatrixNormAtScale_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (k : ℤ) (hk : k ≤ (originCube d 0).scale) :
    maxDescendantBMatrixNormAtScale (originCube d 0) k F =
      maxDescendantBMatrixNormAtScale (originCube d 0) k G := by
  unfold maxDescendantBMatrixNormAtScale
  exact finsetSupReal_congr _ fun R hR =>
    coarseBMatrixNorm_eq_of_root_aeeq a F G hF hG hk hR

private theorem maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (k : ℤ) (hk : k ≤ (originCube d 0).scale) :
    maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) k F =
      maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) k G := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale
  exact finsetSupReal_congr _ fun R hR =>
    coarseSigmaStarInvMatrixNorm_eq_of_root_aeeq a F G hF hG hk hR

/-- CoarseGraining's raw upper multiscale ellipticity at the origin depends only on
the origin coefficient. -/
theorem bigLambdaSq_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (s : ℝ) (q : Book.Ch02.MultiscaleExponent) :
    Book.Ch02.LambdaSq (originCube d 0) s q F =
      Book.Ch02.LambdaSq (originCube d 0) s q G := by
  cases q with
  | finite q =>
      unfold Book.Ch02.LambdaSq Book.Ch02.LambdaSqFinite
      apply congrArg (fun z : ℝ => Real.rpow z (2 / q))
      apply tsum_congr
      intro n
      rw [maxDescendantBMatrixNormAtScale_eq_of_root_aeeq a F G hF hG
        ((originCube d 0).scale - (n : ℤ))
        (sub_le_self _ (Int.natCast_nonneg n))]
  | infinity =>
      unfold Book.Ch02.LambdaSq Book.Ch02.LambdaSqInfinity
      refine congrArg sSup ?_
      ext M
      constructor <;> rintro ⟨n, rfl⟩ <;> refine ⟨n, ?_⟩
      all_goals
        rw [maxDescendantBMatrixNormAtScale_eq_of_root_aeeq a F G hF hG
          ((originCube d 0).scale - (n : ℤ))
          (sub_le_self _ (Int.natCast_nonneg n))]

/-- CoarseGraining's raw lower multiscale ellipticity at the origin depends only on
the origin coefficient. -/
theorem lambdaSq_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (s : ℝ) (q : Book.Ch02.MultiscaleExponent) :
    Book.Ch02.lambdaSq (originCube d 0) s q F =
      Book.Ch02.lambdaSq (originCube d 0) s q G := by
  cases q with
  | finite q =>
      unfold Book.Ch02.lambdaSq Book.Ch02.lambdaSqFinite
      apply congrArg (fun z : ℝ => Real.rpow z (-(2 / q)))
      apply tsum_congr
      intro n
      rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_root_aeeq
        a F G hF hG ((originCube d 0).scale - (n : ℤ))
        (sub_le_self _ (Int.natCast_nonneg n))]
  | infinity =>
      unfold Book.Ch02.lambdaSq Book.Ch02.lambdaSqInfinity
      apply congrArg (fun z : ℝ => z⁻¹)
      refine congrArg sSup ?_
      ext M
      constructor <;> rintro ⟨n, rfl⟩ <;> refine ⟨n, ?_⟩
      all_goals
        rw [maxDescendantSigmaStarInvMatrixNormAtScale_eq_of_root_aeeq
          a F G hF hG ((originCube d 0).scale - (n : ℤ))
          (sub_le_self _ (Int.natCast_nonneg n))]

end Algsuperdiff.Section24.UnitCubeMultiscale
