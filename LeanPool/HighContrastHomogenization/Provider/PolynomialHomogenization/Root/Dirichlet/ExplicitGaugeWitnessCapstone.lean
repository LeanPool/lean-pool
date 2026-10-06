/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitScheduledRate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldedAnchoredResponseFrame
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CdualUnconditional
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DirichletCapstoneBoundary
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitGaugeWitnessCapstone

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (δ), part two: the gauge-witness terminal bound at an explicit `C₀`

The module concludes `∃ C₀ : ℝ → ℝ → ℝ → ℝ, 0 ≤ C₀ s ρ Rad ∧ …` with the
constant bound **inside** `∀ abar U s ρ Rad`, because the scheduled-rate
producer hides its own witness.  The restated clause fixes `C₀` **before**
`∀ g` and demands `0 < C₀ s₀ ρ Rad`, which that module does not provide.

This module re-derives that module with `C₀` a **parameter**: the flux constant comes
from the module as a named term, the scheduled rate from the module at any
`C₀` dominating the head, and the terminal step is
`rowConvertedTerminalBound_of_domainDuality`, which already took `C₀` as a
parameter.

Two further changes make the result usable from the hole:

* `Cdual` is **not** obtained inside.  It is `d`-only, so the inhabitant obtains
  it once, before choosing `C₀`, and passes the instantiated duality here.
* the head hypothesis is stated `∀ J` with the bracket
  `2 Rad ≤ 3^J ≤ 1 + 3(2 Rad)` as its premise, because the bracket generation is
  existential from the modules named above.  The module discharges it uniformly in `J`.

The Hardy-top premise is not needed by that module.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **(δ), part two.**  The folded-length gauge-witness terminal bound with the
constant an explicit parameter rather than an existential witness. -/
theorem RowRetainingPrintOrderGoodScale.explicit_foldedGaugeWitnessTerminalBound_of_energy
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x epsilon : ℝ}
    (hgood : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) (hscale : x ≤ epsilon⁻¹)
    (hd : 1 ≤ d)
    {Uhat : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem Uhat rho Rad)
    (hU : IsOpenBoundedConvexDomain Uhat) (hUnonempty : Uhat.Nonempty)
    (hRad : 0 < Rad) (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hsRange : s ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hrateOrder : kappaRate ≤ s)
    (hGauge : Uhat ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹})
    (uHat hHat : H1Function Uhat)
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
    {Uphys : Set (Vec d)} {cnorm : ℝ} (hcnorm : 0 < cnorm)
    (hInner : ellipsoid abar cnorm ⊆ Uphys)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ Uphys) rho Rad)
    (outputFactor : ℝ) {Cdual : ℝ}
    (hDual : PrintFaithfulDomainFluxDefectDuality Uhat s aHat uHat hHat Cdual)
    {C₀ : ℝ → ℝ → ℝ → ℝ} (hC₀ : 0 ≤ C₀ s rho Rad)
    (hhead : ∀ J : ℕ, 2 * Rad ≤ (3 : ℝ) ^ (J : ℤ) →
      (3 : ℝ) ^ (J : ℤ) ≤ 1 + 3 * (2 * Rad) →
      scheduledRateHead d outputFactor Cdual
          ((Real.rpow (3 : ℝ) (responseWindowOrder g) *
              foldedAnchoredFrameConstant d g kappaRate s
                (coarseFluxResponseConstant d) Rad cnorm hgood.delta
                ((J : ℕ) : ℝ)) ^ 2 * Kenergy)
          hardyConstant ≤
        ENNReal.ofReal (C₀ s rho Rad)) :
    ENNReal.ofReal outputFactor *
        (negSobolevNorm Uhat s (fun z ↦ uHat.grad z - hHat.grad z) +
          negSobolevNorm Uhat s (fun z ↦
            matVecMul (aHat z) (uHat.grad z) - hHat.grad z)) ≤
      ENNReal.ofReal (C₀ s rho Rad *
          (epsilon * (x * eccentricityFoldFactor abar
            (foldedFrameEccentricityExponent g kappaRate))) ^ kappaRate) *
        boundaryEnergy ^ (1 / 2 : ℝ) := by
  have hWindow : responseWindowOrder g < s :=
    responseWindowOrder_lt_exponent hg hsRange
  obtain ⟨J, hJ, hJupper, hFluxRate⟩ :=
    hgood.explicit_foldedAnchoredPhysicalFluxDefectRate hS hg hkappa hx hepsilon
      hscale hd system hU hRad hGauge hWindow hrateOrder
      (hsHalf.trans (by norm_num)) aHat haHat aObs aCell hObs uHat wCell
      hfamily hEnergy.1 hEnergy.2 hcnorm hInner hSandwich
  have hF0 : (0 : ℝ) ≤ eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate) :=
    le_trans zero_le_one (one_le_eccentricityFoldFactor abar _)
  have hbase : 0 ≤ epsilon * (x * eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate)) :=
    mul_nonneg hepsilon.le (mul_nonneg (zero_le_one.trans hx) hF0)
  have hKflux0 : (0 : ℝ) ≤
      (Real.rpow (3 : ℝ) (responseWindowOrder g) *
          foldedAnchoredFrameConstant d g kappaRate s
            (coarseFluxResponseConstant d) Rad cnorm hgood.delta
            ((J : ℕ) : ℝ)) ^ 2 * Kenergy :=
    mul_nonneg (sq_nonneg _) hEnergy.1
  have hRate := rowConvertedFluxScheduledRateAtWitness_of_head_le
    (d := d) (g := g) (kappaRate := kappaRate) (Cdual := Cdual)
    (hardyConstant := hardyConstant) (boundaryEnergy := boundaryEnergy)
    (s := s) (rho := rho) (Rad := Rad) (epsilon := epsilon)
    (Xval := x * eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate))
    (outputFactor := outputFactor) (C₀ := C₀)
    hbase hBoundaryTop hKflux0 hFluxRate hC₀ (hhead J hJ hJupper)
  exact rowConvertedTerminalBound_of_domainDuality system hU hUnonempty hs hsHalf
    aHat uHat hHat hFdefect (hardyConstant := hardyConstant)
    (boundaryEnergy := boundaryEnergy) (Cdual := Cdual) le_rfl hHardy hDual
    hRate

end

end RowSupply
end HighContrast
end HCPolySupport
