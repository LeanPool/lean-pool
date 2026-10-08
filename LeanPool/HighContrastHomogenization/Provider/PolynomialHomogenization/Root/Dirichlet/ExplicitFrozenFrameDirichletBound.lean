/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitGaugeWitnessCapstone
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.PhysicalFrameTransport

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitFrozenFrameDirichletBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (δ), part three: the frozen Dirichlet conclusion body at an explicit `C₀`

The module composes the physical-frame transport from the modules named above with the gauge-side
terminal bound from the modules named above, at
`outputFactor := √(hsAffineFactor (matSqrt (symmPart abar))⁻¹ s ‖matSqrt (symmPart abar)‖)`.
The composition is unchanged here; only the terminal bound is swapped for module
that module's, which carries `C₀` as a parameter.

The result is the **conclusion body of the frozen Dirichlet conjunct**, at the
folded homogenization length and at a constant the caller chooses — which is
what the restated Dirichlet clause's binder order requires.  The Hardy-top
premise is not a
hypothesis.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **(δ), part three.**  The frozen Dirichlet conclusion at the folded length,
with the constant an explicit parameter. -/
theorem RowRetainingPrintOrderGoodScale.explicit_foldedFrozenFrameDirichletBound_of_energy
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x epsilon : ℝ}
    (hgood : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) (hscale : x ≤ epsilon⁻¹)
    (hd : 1 ≤ d)
    {Uphys Uhat : Set (Vec d)}
    (hUhat : Uhat = matImage (matSqrt (symmPart abar))⁻¹ Uphys)
    (hUhatMeas : MeasurableSet Uhat) (hUhat0 : volume Uhat ≠ 0)
    {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem Uhat rho Rad)
    (hU : IsOpenBoundedConvexDomain Uhat) (hUnonempty : Uhat.Nonempty)
    (hRad : 0 < Rad) (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hsRange : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hrateOrder : kappaRate ≤ s)
    (hGauge : Uhat ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹})
    (u h : H1Function Uphys) (uHat hHat : H1Function Uhat)
    (huHat : uHat.grad = fun y ↦ matVecMul (matSqrt (symmPart abar))
      (u.grad (matVecMul (matSqrt (symmPart abar)) y)))
    (hhHat : hHat.grad = fun y ↦ matVecMul (matSqrt (symmPart abar))
      (h.grad (matVecMul (matSqrt (symmPart abar)) y)))
    {aHat : CoeffField d}
    (haHat : aHat = affineCoefficient (matSqrt (symmPart abar))
      (isUnit_det_matSqrt hS)
      (fun z ↦ scaledCoeff epsilon a z - skewPart abar))
    (aObs aCell : system.CellIndex → CoeffFamily d)
    (hObs : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
      fun y ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun z ↦ scaledCoeff epsilon a z - skewPart abar)
        (y + ruledObservationCenter system i))
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (hfamily : RuledCellPhysicalForcedFamily system aHat uHat aCell wCell)
    {Kenergy : ℝ} {boundaryEnergy hardyConstant : ℝ≥0∞}
    (hEnergy : GaugePhysicalEnergyPriceAtWitness Uhat aHat uHat Kenergy
      boundaryEnergy)
    (hBoundaryTop : boundaryEnergy ≠ ⊤)
    (hHardy : ∀ G : Vec d → Vec d,
      Integrable G (volume.restrict Uhat) →
        PrintFaithfulPositiveTestRow system s G hardyConstant)
    (hFdefect : MemVectorL2 Uhat
      (fun y ↦ matVecMul (aHat y - 1) (uHat.grad y)))
    {cnorm : ℝ} (hcnorm : 0 < cnorm)
    (hInner : ellipsoid abar cnorm ⊆ Uphys)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ Uphys) rho Rad)
    {Cdual : ℝ}
    (hDual : PrintFaithfulDomainFluxDefectDuality Uhat s aHat uHat hHat Cdual)
    {C₀ : ℝ → ℝ → ℝ → ℝ} (hC₀ : 0 ≤ C₀ s rho Rad)
    (hhead : ∀ J : ℕ, 2 * Rad ≤ (3 : ℝ) ^ (J : ℤ) →
      (3 : ℝ) ^ (J : ℤ) ≤ 1 + 3 * (2 * Rad) →
      scheduledRateHead d
          (Real.sqrt (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
            ‖matSqrt (symmPart abar)‖)) Cdual
          ((Real.rpow (3 : ℝ) (responseWindowOrder g) *
              foldedAnchoredFrameConstant d g kappaRate s
                (coarseFluxResponseConstant d) Rad cnorm hgood.delta
                ((J : ℕ) : ℝ)) ^ 2 * Kenergy)
          hardyConstant ≤
        ENNReal.ofReal (C₀ s rho Rad))
    (uGrad : Vec d → Vec d) (huGrad : u.grad = uGrad) :
    negSobolevNorm Uphys s
        (fun y ↦ matVecMul (matSqrt (symmPart abar))
          (uGrad y - h.grad y)) +
      negSobolevNorm Uphys s
        (fun y ↦ matVecMul (matSqrt (symmPart abar))⁻¹
          (matVecMul (scaledCoeff epsilon a y - skewPart abar) (uGrad y) -
            matVecMul (symmPart abar) (h.grad y))) ≤
      ENNReal.ofReal (C₀ s rho Rad *
          (epsilon * (x * eccentricityFoldFactor abar
            (foldedFrameEccentricityExponent g kappaRate))) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ) := by
  have hterm :=
    hgood.explicit_foldedGaugeWitnessTerminalBound_of_energy hS hg hkappa hx
      hepsilon hscale hd system hU hUnonempty hRad hs hsHalf hsRange hrateOrder
      hGauge uHat hHat haHat aObs aCell hObs wCell hfamily hEnergy hBoundaryTop
      hHardy hFdefect hcnorm hInner hSandwich
      (Real.sqrt (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s
        ‖matSqrt (symmPart abar)‖))
      hDual hC₀ hhead
  refine le_trans ?_ hterm
  subst huGrad
  have hsdim : (0 : ℝ) ≤ (d : ℝ) + 2 * s := by positivity
  exact negSobolevPhysicalPair_le_outputFactor_mul_gaugePair hS hUhat hUhatMeas
    hUhat0 hsdim (scaledCoeff epsilon a) u.grad h.grad uHat hHat huHat hhHat
    haHat

end

end RowSupply
end HighContrast
end HCPolySupport
