/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FoldedAnchoredResponseFrame
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredObservationToPhysicalFluxRate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxRateAggregationReduction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.ExplicitFoldedFluxConstant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# (α) part one: the flux constant of the folded row, made explicit

The aggregation concludes `∃ Kflux, 0 ≤ Kflux ∧ …`, because it hides its own
constant behind an existential. *read off* from
`PhysicalFluxRateAggregationConditional:55` that the witness is
`(3 ^ b · Kframe) ^ 2 · Kenergy`, and recorded that reading as
not available as a theorem.

This module repeats the same three steps — the observation-to-physical response
transfer, the response/energy aggregation and the cap comparison — without the
existential, so the constant is a **named term** in the conclusion:

```
Kflux = (3 ^ responseWindowOrder g · foldedAnchoredFrameConstant …) ^ 2 · Kenergy
```

with `foldedAnchoredFrameConstant` definitionally the exported frame
constant, explicit in `(d, g, κ, r, Cflux, Rad, cnorm, h.delta, J)`.  The
bracket `2 Rad ≤ 3 ^ J ≤ 1 + 3 (2 Rad)` is exported alongside it, so the `J` can
be traded for `Rad` downstream; no hypothesis of the aggregation is added,
removed or weakened.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The frame constant, named.**  Definitionally the constant that
`RowRetainingPrintOrderGoodScale.exists_foldedAnchoredResidualFrameResponseRate`
exports: explicit in the dimension, the printed orders, the rate, the flux
constant, the outer sandwich radius, the normalization radius, the
certificate's amplitude and the bracket generation. -/
@[expose]
noncomputable def foldedAnchoredFrameConstant (d : ℕ)
    (g kappaRate r Cflux Rad cnorm delta J : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (-responseWindowOrder g) *
        Real.rpow (2 * Rad) (r - responseWindowOrder g) * Cflux * r⁻¹ *
        Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
        responseOneFromTwoGapFactor (responseWindowOrder g) r *
    (foldedAnchoredResponseConstant d g kappaRate delta J *
      max 1 ((Rad / cnorm) ^ (1 / 2 : ℝ)))

/-- **(α), part one.**  The physical flux-defect row at the folded length, with
the flux constant an explicit term rather than an existential witness. -/
theorem RowRetainingPrintOrderGoodScale.explicit_foldedAnchoredPhysicalFluxDefectRate
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x epsilon : ℝ}
    (h : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) (hscale : x ≤ epsilon⁻¹)
    {U : Set (Vec d)} {rho Rad r : ℝ}
    (hd : 1 ≤ d)
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) (hRad : 0 < Rad)
    (hGauge : U ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹})
    (hresponseOrder : responseWindowOrder g < r)
    (hrateOrder : kappaRate ≤ r) (hrOne : r < 1)
    (aPhysical : CoeffField d)
    (haPhysical : aPhysical =
      affineCoefficient (matSqrt (symmPart abar))
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
    (u : H1Function U)
    (wCell : ∀ i, ForcedCubeSolution
      (whitneyCellCube system i) (aCell i) (0 : Vec d → Vec d))
    (hfamily : RuledCellPhysicalForcedFamily system aPhysical u aCell wCell)
    {Kenergy : ℝ} {boundaryEnergy : ℝ≥0∞}
    (hKenergy : 0 ≤ Kenergy)
    (hglobalEnergy : eVolumeAverage U (fun z =>
        ENNReal.ofReal (coefficientEnergyDensity aPhysical u.grad z)) ≤
      ENNReal.ofReal Kenergy * boundaryEnergy)
    {Uphys : Set (Vec d)} {cnorm : ℝ} (hcnorm : 0 < cnorm)
    (hInner : ellipsoid abar cnorm ⊆ Uphys)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ Uphys) rho Rad) :
    ∃ J : ℕ,
      2 * Rad ≤ (3 : ℝ) ^ (J : ℤ) ∧
      (3 : ℝ) ^ (J : ℤ) ≤ 1 + 3 * (2 * Rad) ∧
      normalizedWhitneyRowEnergy system
          (physicalFullDualWhitneyFamilyCellEnergy system r
            (ruledPhysicalFluxDefectOnCell system aPhysical
              (fun _ ↦ identityConstantCoeffMatrix d) u)) ≤
        ENNReal.ofReal
            (((Real.rpow (3 : ℝ) (responseWindowOrder g) *
                  foldedAnchoredFrameConstant d g kappaRate r
                    (coarseFluxResponseConstant d) Rad cnorm
                    h.delta ((J : ℕ) : ℝ)) ^ 2 * Kenergy) *
              (epsilon * (x * eccentricityFoldFactor abar
                (foldedFrameEccentricityExponent g kappaRate))) ^
                (2 * kappaRate)) * boundaryEnergy := by
  have hCflux : (0 : ℝ) ≤ coarseFluxResponseConstant d := by
    dsimp only [coarseFluxResponseConstant]
    positivity
  obtain ⟨J, responseBound, hJ, hJupper, hObservationResponse, hFrame⟩ :=
    h.exists_foldedAnchoredResidualFrameResponseRate hS hg hkappa hx hepsilon
      hscale system hU hRad hGauge hresponseOrder hrateOrder hCflux aObs hObs
      hcnorm hInner hSandwich
  refine ⟨J, hJ, hJupper, ?_⟩
  have hObsTranslate : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
          translateCoeffField (ruledObservationCenter system i) aPhysical := by
    intro i
    rw [haPhysical]
    simpa only [translateCoeffField] using! hObs i
  have hF0 : (0 : ℝ) ≤ eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate) :=
    le_trans zero_le_one (one_le_eccentricityFoldFactor abar _)
  have hbase : 0 ≤ epsilon * (x * eccentricityFoldFactor abar
      (foldedFrameEccentricityExponent g kappaRate)) :=
    mul_nonneg hepsilon.le (mul_nonneg (zero_le_one.trans hx) hF0)
  have hb0 : 0 < responseWindowOrder g :=
    responseWindow_pos hg (responseWindowOrder_mem hg).1
  have hfactor : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (responseWindowOrder g) :=
    Real.rpow_nonneg (by norm_num) _
  have hphysicalFrame :=
    physicalFluxEpsilonFrameBound_const_mul system responseBound hfactor hFrame
  have hCell : ∀ i,
      ((aCell i).coeffOn (whitneyCellCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (whitneyCellCube system i))]
          aPhysical := by
    intro i
    simpa only [openCubeSet_whitneyCellCube] using hfamily.1 i
  have hPhysicalResponse :=
    physicalCellHomogenizationError_le_of_observationBound system hb0 aObs aCell
      (fun _ ↦ aPhysical) responseBound hObsTranslate hCell hObservationResponse
  have henergy := physicalCellSolutionEnergyRow_le_of_physicalEnergyAverage_le
    hd system hU aPhysical u aCell wCell hfamily hglobalEnergy
  have hagg := physicalFluxResponseRateAggregation system
    (fun i ↦ Real.rpow (3 : ℝ) (responseWindowOrder g) * responseBound i)
    aCell wCell hbase hphysicalFrame hKenergy henergy
  have hcap := physicalFluxResponseCap_le_responseBoundEnergyRow system
    (fun i ↦ Real.rpow (3 : ℝ) (responseWindowOrder g) * responseBound i)
    aCell wCell hb0 hresponseOrder hCflux hPhysicalResponse
  exact (physicalFluxDefectRow_le_coarseResponseRow system
    (hb0.trans hresponseOrder) hrOne aPhysical u
    (fun _ ↦ identityConstantCoeffMatrix d) aCell wCell hfamily).trans
      (hcap.trans hagg.2)

end

end RowSupply
end HighContrast
end HCPolySupport
