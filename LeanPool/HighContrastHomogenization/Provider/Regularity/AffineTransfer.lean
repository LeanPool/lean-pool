/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineFields
public import LeanPool.HighContrastHomogenization.Analytic.AffineNormalization
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakSolution
public import LeanPool.HighContrastHomogenization.Analytic.SkewGauge
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMetric

/-!
# High-contrast homogenization: Provider.Regularity.AffineTransfer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine transfer for large-scale regularity

This file collects the elementary interfaces that move between physical
coordinates and the scalar coordinates determined by the symmetric square
root of the homogenized coefficient.  The results compose the constant-skew
gauge with affine covariance of weak gradients, weak solutions,
normalized norms, and fluxes.

The geometric results identify the pullback of an adapted ellipsoid exactly
and compare it with centered Euclidean cubes under explicit scale inequalities.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The symmetric square root may be moved between the two entries of the
Euclidean pairing. -/
theorem vecDot_matSqrt_mulVec (S : Mat d) (e y : Vec d) :
    vecDot e (matVecMul (matSqrt S) y) =
      vecDot (matVecMul (matSqrt S) e) y := by
  have hsymm : matTranspose (matSqrt S) = matSqrt S :=
    (isSymm_matSqrt S).eq
  calc
    vecDot e (matVecMul (matSqrt S) y) =
        vecDot (matVecMul (matSqrt S) y) e := vecDot_comm _ _
    _ = vecDot y (matVecMul (matTranspose (matSqrt S)) e) :=
      (vecDot_matVecMul_transpose y e (matSqrt S)).symm
    _ = vecDot y (matVecMul (matSqrt S) e) := by rw [hsymm]
    _ = vecDot (matVecMul (matSqrt S) e) y := vecDot_comm _ _

/-- The Euclidean norm of a square-root-transformed vector is the square root
of its quadratic energy. -/
theorem euclideanNorm_matSqrt_eq_sqrt_vecDot {S : Mat d}
    (hS : S.PosSemidef) (e : Vec d) :
    euclideanNorm (matVecMul (matSqrt S) e) =
      Real.sqrt (vecDot e (matVecMul S e)) := by
  have hsymm : matTranspose (matSqrt S) = matSqrt S :=
    (isSymm_matSqrt S).eq
  unfold euclideanNorm
  congr 1
  change vecDot (matVecMul (matSqrt S) e) (matVecMul (matSqrt S) e) = _
  calc
    vecDot (matVecMul (matSqrt S) e) (matVecMul (matSqrt S) e) =
        vecDot e
          (matVecMul (matTranspose (matSqrt S))
            (matVecMul (matSqrt S) e)) :=
      (vecDot_matVecMul_transpose e
        (matVecMul (matSqrt S) e) (matSqrt S)).symm
    _ = vecDot e (matVecMul S e) := by
      rw [hsymm, matVecMul_mul, (matSqrt_spec hS).2]

/-- Pulling an adapted ellipsoid back by the symmetric square root gives its
exact Euclidean quadratic sublevel set. -/
theorem matImage_matSqrt_inv_ellipsoid_eq {abar : Mat d}
    (hS : (symmPart abar).PosDef) (r : ℝ) :
    matImage (matSqrt (symmPart abar))⁻¹ (ellipsoid abar r) =
      {y : Vec d | vecNormSq y ≤
        specBound ((symmPart abar)⁻¹) * r ^ 2} := by
  rw [matImage_inv_eq_preimage (isUnit_det_matSqrt hS)]
  ext y
  change vecDot (matVecMul (matSqrt (symmPart abar)) y)
      (matVecMul (symmPart abar)⁻¹
        (matVecMul (matSqrt (symmPart abar)) y)) ≤
        specBound ((symmPart abar)⁻¹) * r ^ 2 ↔
      vecNormSq y ≤ specBound ((symmPart abar)⁻¹) * r ^ 2
  rw [vecDot_matVecMul_inv_matSqrt hS]

/-- A physical weak solution is equivalent to the square-root pullback of its
skew-centered weak equation.  The Sobolev data are explicit because the skew
gauge acts only on actual weak gradients. -/
theorem isWeakSolutionOn_skewCentered_matSqrtPullback_iff
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpen U) (a : CoeffField d) {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (hu : MemScalarL2 U u)
    (hDu : ∀ i, MemScalarL2 U fun x ↦ Du x i)
    (hweak : HasWeakGradientOn U u Du) :
    IsWeakSolutionOn a U Du ↔
      IsWeakSolutionOn
        (affineCoefficient (matSqrt (symmPart abar))
          (isUnit_det_matSqrt hS) (fun x ↦ a x - skewPart abar))
        (matImage (matSqrt (symmPart abar))⁻¹ U)
        (fun y ↦ matVecMul (matSqrt (symmPart abar))
          (Du (matVecMul (matSqrt (symmPart abar)) y))) := by
  let b : CoeffField d := fun x ↦ a x - skewPart abar
  have hk : IsSkewMat (skewPart abar) := matTranspose_skewPart abar
  have hfield : (fun x ↦ b x + skewPart abar) = a := by
    funext x
    simp only [b, sub_add_cancel]
  have hgauge :=
    isWeakSolutionOn_add_constSkew_iff hU b hu hDu hweak (skewPart abar) hk
  rw [hfield] at hgauge
  have haffine := isWeakSolutionOn_affinePullback_iff
    (isUnit_det_matSqrt hS) hU.measurableSet b Du
  have htranspose : matTranspose (matSqrt (symmPart abar)) =
      matSqrt (symmPart abar) := (isSymm_matSqrt _).eq
  simpa only [b, htranspose] using hgauge.trans haffine

/-- A gradient difference in physical coordinates becomes the difference of
the two square-root-transformed gradients. -/
theorem matSqrt_gradient_difference_affinePullback
    {abar : Mat d} (F G : Vec d → Vec d) :
    (fun y ↦ matVecMul (matSqrt (symmPart abar))
      (F (matVecMul (matSqrt (symmPart abar)) y) -
        G (matVecMul (matSqrt (symmPart abar)) y))) =
      fun y ↦
        matVecMul (matSqrt (symmPart abar))
            (F (matVecMul (matSqrt (symmPart abar)) y)) -
          matVecMul (matSqrt (symmPart abar))
            (G (matVecMul (matSqrt (symmPart abar)) y)) := by
  funext y
  exact (matSqrt_gradient_difference_eq _ _ _).symm

/-- The normalized flux difference is exactly the inverse-square-root image
of the physical skew-centered flux difference. -/
theorem skewCenteredFlux_affinePullback {abar : Mat d}
    (hS : (symmPart abar).PosDef) (a : CoeffField d)
    (F G : Vec d → Vec d) :
    (fun y ↦
      matVecMul
          (affineCoefficient (matSqrt (symmPart abar))
            (isUnit_det_matSqrt hS) (fun x ↦ a x - skewPart abar) y)
          (matVecMul (matSqrt (symmPart abar))
            (F (matVecMul (matSqrt (symmPart abar)) y))) -
        matVecMul (matSqrt (symmPart abar))
          (G (matVecMul (matSqrt (symmPart abar)) y))) =
      fun y ↦
        matVecMul (matSqrt (symmPart abar))⁻¹
          (matVecMul
              (a (matVecMul (matSqrt (symmPart abar)) y) - skewPart abar)
              (F (matVecMul (matSqrt (symmPart abar)) y)) -
            matVecMul (symmPart abar)
              (G (matVecMul (matSqrt (symmPart abar)) y))) := by
  funext y
  simpa only [affineCoefficient_apply] using
    matSqrt_inv_skewCentered_flux_difference_eq
      (abar := abar) (A := a (matVecMul (matSqrt (symmPart abar)) y))
      hS (F (matVecMul (matSqrt (symmPart abar)) y))
        (G (matVecMul (matSqrt (symmPart abar)) y))

end

end HighContrast
end HCPolySupport
