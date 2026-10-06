/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldedAnchoredResponseFrame
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DirichletCapstoneBoundary
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CdualUnconditional
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.PhysicalFrameTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The physical-frame pair from the gauge pair

The frozen Dirichlet conjunct is written in the **physical** frame, at the
`L`-conjugated pair

```
negSobolevNorm U s (L (∇u − ∇h)) + negSobolevNorm U s (L⁻¹ (a ∇u − ā ∇h))
```

with `L = matSqrt (symmPart abar)`, while the terminal Seam-2 bound is produced
in the **gauge** frame, on `Uhat = matImage L⁻¹ U`, at the pair

```
negSobolevNorm Uhat s (∇û − ∇ĥ) + negSobolevNorm Uhat s (â ∇û − ∇ĥ).
```

The step between them is the affine dual comparison
`negSobolevNorm_matImage_le_opNorm` (`HCPoly.Analytic.AffineNegSobolevNorm`)
applied twice, with the two pullback identities
`matSqrt_gradient_difference_affinePullback` and `skewCenteredFlux_affinePullback`
(`HCPoly.Provider.Regularity.AffineTransfer`) identifying the
pulled-back physical fields with the gauge fields.  This is exactly the
`Kout` half of the anisotropic flux defect, isolated from its
descendant-cube context.

**The frame factor does not need to be folded.**  Its constant is
`√(hsAffineFactor L⁻¹ s ‖L‖)`, which is precisely the `outputFactor` that the
terminal bound carries on its *left*-hand side as a free parameter.  Instantiated
there, the two occurrences are the same term and cancel; no bound on `‖L‖`,
`‖L⁻¹‖` or the eccentricity is spent here.  That is why `outputFactor` was left
free there in the first place.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory

open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The physical pair is the gauge pair at the output factor.**  Both frozen
negative-Sobolev terms transport at the single constant
`√(hsAffineFactor L⁻¹ s ‖L‖)`, with no other loss. -/
theorem negSobolevPhysicalPair_le_outputFactor_mul_gaugePair [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {Uphys Uhat : Set (Vec d)}
    (hUhat : Uhat = matImage (matSqrt (symmPart abar))⁻¹ Uphys)
    (hUmeas : MeasurableSet Uhat) (hU0 : volume Uhat ≠ 0)
    {s : ℝ} (hs : 0 ≤ (d : ℝ) + 2 * s)
    (aPhysical : CoeffField d) (uGrad hGrad : Vec d → Vec d)
    (uHat hHat : H1Function Uhat)
    (huHat : uHat.grad = fun y ↦ matVecMul (matSqrt (symmPart abar))
      (uGrad (matVecMul (matSqrt (symmPart abar)) y)))
    (hhHat : hHat.grad = fun y ↦ matVecMul (matSqrt (symmPart abar))
      (hGrad (matVecMul (matSqrt (symmPart abar)) y)))
    {aHat : CoeffField d}
    (haHat : aHat = affineCoefficient (matSqrt (symmPart abar))
      (isUnit_det_matSqrt hS) (fun z ↦ aPhysical z - skewPart abar)) :
    negSobolevNorm Uphys s
        (fun y ↦ matVecMul (matSqrt (symmPart abar)) (uGrad y - hGrad y)) +
      negSobolevNorm Uphys s
        (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
          (matVecMul (aPhysical y - skewPart abar) (uGrad y) -
            matVecMul (symmPart abar) (hGrad y))) ≤
      ENNReal.ofReal (Real.sqrt
          (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
            ‖matSqrt (symmPart abar)‖)) *
        (negSobolevNorm Uhat s (fun y ↦ uHat.grad y - hHat.grad y) +
          negSobolevNorm Uhat s (fun y ↦
            matVecMul (aHat y) (uHat.grad y) - hHat.grad y)) := by
  have hL : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hcell : matImage (matSqrt (symmPart abar)) Uhat = Uphys := by
    rw [hUhat]
    exact matImage_matImage_inv hL Uphys
  have hgrad := negSobolevNorm_matImage_le_opNorm hL hUmeas hU0 hs
    (fun y ↦ matVecMul (matSqrt (symmPart abar)) (uGrad y - hGrad y))
  rw [hcell] at hgrad
  have hflux := negSobolevNorm_matImage_le_opNorm hL hUmeas hU0 hs
    (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
      (matVecMul (aPhysical y - skewPart abar) (uGrad y) -
        matVecMul (symmPart abar) (hGrad y)))
  rw [hcell] at hflux
  have hgradId : (fun y ↦ matVecMul (matSqrt (symmPart abar))
        (uGrad (matVecMul (matSqrt (symmPart abar)) y) -
          hGrad (matVecMul (matSqrt (symmPart abar)) y))) =
      fun y ↦ uHat.grad y - hHat.grad y := by
    rw [matSqrt_gradient_difference_affinePullback uGrad hGrad, huHat, hhHat]
  have hfluxId : (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
        (matVecMul
            (aPhysical (matVecMul (matSqrt (symmPart abar)) y) - skewPart abar)
            (uGrad (matVecMul (matSqrt (symmPart abar)) y)) -
          matVecMul (symmPart abar)
            (hGrad (matVecMul (matSqrt (symmPart abar)) y)))) =
      fun y ↦ matVecMul (aHat y) (uHat.grad y) - hHat.grad y := by
    rw [haHat, ← skewCenteredFlux_affinePullback hS aPhysical uGrad hGrad,
      huHat, hhHat]
  have hgradOut := hgrad
  have hfluxOut := hflux
  simp only [hgradId] at hgradOut
  simp only [hfluxId] at hfluxOut
  refine (add_le_add hgradOut hfluxOut).trans (le_of_eq ?_)
  rw [mul_add]

end

end RowSupply
end HighContrast
end HCPolySupport
