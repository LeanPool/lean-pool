/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MagicIdentities.MuOrdering.EllipticConsequences.SigmaStarPosDef
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Symmetric.CompletedSquare

/-!
# Coarse-graining support: Support.CoarseGraining.Symmetric.OpenBoundedConvex

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

noncomputable section

/-!
# Symmetric response wrappers on open bounded convex domains

The core symmetric response identities require the determinant guard
`IsUnit sigmaStar.det`. On open bounded convex domains, elliptic recovery data
supplies this guard from the usual deterministic hypotheses.
-/

/--
Open-bounded-convex wrapper for the symmetric split quadratic response formula.
-/
theorem responseJ_eq_half_dot_sigmaCoarse_add_half_dot_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (ha : IsSymmetricCoeffField a) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) -
        vecDot p q := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := U) (a := a) R hConv hEll hvol compat hS
  exact
    responseJ_eq_half_dot_sigmaCoarse_add_half_dot_sigmaStarInvCoarse_sub_dot
      ha hA hS hK hSigma hdet p q

/--
Open-bounded-convex wrapper for the symmetric completed-square identity.
-/
theorem responseJ_completedSquare_of_symmetricEllipticOnConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (ha : IsSymmetricCoeffField a) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p q : Vec d) :
    ResponseJ U p q a =
      (1 / 2 : ℝ) * vecDot p (matVecMul (sigma - sigmaStar) p) +
        (1 / 2 : ℝ) *
          vecDot (q - matVecMul sigmaStar p)
            (matVecMul sigmaStar⁻¹ (q - matVecMul sigmaStar p)) := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := U) (a := a) R hConv hEll hvol compat hS
  exact responseJ_completedSquare_of_isSymmetricCoeffField
    ha hA hS hK hSigma hdet p q

/--
Open-bounded-convex wrapper for the canonical symmetric gap identity at
`q = sigmaStarCoarse p`.
-/
theorem responseJ_sigmaStarCoarse_mul_eq_half_gap_of_of_isSymmetricCoeffField
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U) (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ}
    (ha : IsSymmetricCoeffField a) (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (p : Vec d) :
    ResponseJ U p (matVecMul (sigmaStarCoarse U a) p) a =
      (1 / 2 : ℝ) *
        vecDot p (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p) := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (U := U) (a := a) R hConv hEll hvol compat hS
  exact responseJ_sigmaStarCoarse_mul_eq_half_gap_of_isSymmetricCoeffField
    ha hA hS hK hSigma hdet p

end

end HCPolySupport
