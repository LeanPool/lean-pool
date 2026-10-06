/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FixedParentResponsePriceAlgebra
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicRowLevelWindowTailComposition
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.AnchoredCommonResidualParent

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredResidualFrameRate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Row-level residual-frame rate provider

The physical block row is transported through the exact triadic dilation and
converted to the response-window order before the all-depth sum.  One common
normalized-reference parent is then used for every ruled observation cell.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Row-level order conversion followed by fixed-parent aggregation supplies
both the cellwise response bounds and the physical-frame RATE-AGG premise. -/
theorem RowRetainingPrintOrderGoodScale.exists_formulaicAnchoredResidualFrameResponseRate
    [NeZero d] {g c kappaRate : ℝ} {abar : Mat d}
    {a : CoeffSpace d} {x epsilon : ℝ}
    (h : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
    (hS : (symmPart abar).PosDef)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hkappa : 0 < kappaRate)
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon) (hscale : x ≤ epsilon⁻¹)
    {U : Set (Vec d)} {rho Rad r Cflux : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hU : IsOpenBoundedConvexDomain U) (hRad : 0 < Rad)
    (hGauge : U ⊆ {z : Vec d |
      vecNormSq z ≤ specBound (symmPart abar)⁻¹})
    (hresponseOrder : responseWindowOrder g < r)
    (hrateOrder : kappaRate ≤ r)
    (hCflux : 0 ≤ Cflux)
    (aObs : system.CellIndex → Book.Ch03.CoeffFamily d)
    (hObs : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
      fun y ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun z ↦ scaledCoeff epsilon a z - skewPart abar)
        (y + ruledObservationCenter system i)) :
    ∃ (N G J : ℕ) (lambda deltaScaled : ℝ)
        (aScaled : CoeffSpace d) (aRef : Book.Ch03.CoeffFamily d) (L : ℕ)
        (M : ℤ) (responseBound : system.CellIndex → ℝ) (Kframe : ℝ),
      lambda = epsilon * (3 : ℝ) ^ N ∧
      lambda ∈ Set.Icc (1 : ℝ) 3 ∧
      aScaled = Quenched.physical_scale_coeff N a ∧
      deltaScaled = triadicallyScaledRowAmplitude h.delta
        (h.activationScale a) N (2 * kappaRate) ∧
      witnessEccentricity (symmPart abar) * Real.sqrt d ≤
          (3 : ℝ) ^ (G : ℤ) ∧
      (3 : ℝ) ^ (G : ℤ) ≤
          1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) ∧
      L = Certificate.formulaicNormalizedReferenceTailShift d
          (responseWindowOrder g) (Certificate.printRowOrder g)
            (2 * kappaRate) G ∧
      (L : ℝ) < max 0 (Real.logb 3
          (Certificate.shiftedTailAbsorptionPrefactor d
            (responseWindowOrder g) (Certificate.printRowOrder g) G) /
              (2 * kappaRate)) + 1 ∧
      2 * Rad ≤ (3 : ℝ) ^ (J : ℤ) ∧
      (3 : ℝ) ^ (J : ℤ) ≤ 1 + 3 * (2 * Rad) ∧
      M = max (max (L : ℤ) ((J : ℤ) + 1)) 1 ∧
      Kframe =
        Cflux * r⁻¹ *
          Book.Ch03.constantCoeffMatrixNormHalf
            (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor (responseWindowOrder g) r *
          Real.sqrt
            (observationFillingCoefficient d lambda abar *
              (Book.Ch02.geometricDiscount
                (1 - 2 * responseWindowOrder g) 1)⁻¹) *
          Real.rpow (3 : ℝ)
            ((r - kappaRate) * (M : ℝ) + kappaRate * (L : ℝ) - r) *
          Real.sqrt h.delta ∧
      (∀ Q : TriadicCube d,
        (aRef.coeffOn Q).toCoeffField =
          affineCoefficient (Selection.normalizedRoot (symmPart abar))
            ((Matrix.isUnit_iff_isUnit_det _).mp
              (normalizedRoot_posDef_of_posDef hS).isUnit)
            ⇑(normalizedCenteredCoeff aScaled abar hS).1) ∧
      ScalarIdentityPowerTail aRef (responseWindowOrder g)
        (Real.sqrt deltaScaled) kappaRate ((3 : ℝ) ^ (L : ℤ)) ∧
      (L : ℤ) ≤ M ∧
      (∀ i, (ruledObservationCube system i).scale ≤ M) ∧
      (∀ i, responseBound i =
        Real.sqrt
          (observationFillingCoefficient d lambda abar *
              (Book.Ch02.geometricDiscount
                (1 - 2 * responseWindowOrder g) 1)⁻¹) *
          Real.rpow (3 : ℝ)
            (responseWindowOrder g *
              ((M : ℝ) -
                (((ruledObservationCube system i).scale : ℤ) : ℝ))) *
          Real.sqrt deltaScaled *
          Real.rpow (3 : ℝ)
            (-kappaRate * ((M : ℝ) - (L : ℝ)))) ∧
      (∀ i,
        Book.Ch02.HomogenizationErrorOnCube
            (ruledObservationCube system i) (responseWindowOrder g)
            .infinity (.finite 2) (aObs i)
              (identityConstantCoeffMatrix d).matrix ≤ responseBound i) ∧
      PhysicalFluxEpsilonFrameBound system (responseWindowOrder g) r Cflux
        responseBound epsilon x kappaRate Kframe := by
  obtain ⟨N, G, lambda, deltaScaled, aScaled, aRef, L, hlambda,
    hlambdaRange, haScaled, hdeltaScaled, hG, hGupper, hLeq, hLupper,
      haRef, hTail⟩ :=
    h.exists_formulaicScaledResponseWindowTail hS hg hkappa hx hepsilon hscale
  have hscaledCoeff : scaledCoeff lambda aScaled =ᵐ[volume]
      scaledCoeff epsilon a := by
    rw [hlambda, haScaled]
    exact scaledCoeff_mul_pow_physicalScaleCoeff_ae hepsilon N a
  have hObsScaled : ∀ i,
      ((aObs i).coeffOn (ruledObservationCube system i)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (ruledObservationCube system i))]
      fun y ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun z ↦ scaledCoeff lambda aScaled z - skewPart abar)
        (y + ruledObservationCenter system i) := fun i ↦
    (hObs i).trans
      (affineTranslatedCenteredCoeff_congr_ae (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS) (skewPart abar) hscaledCoeff
        (ruledObservationCenter system i)
        (openCubeSet (ruledObservationCube system i))).symm
  have haRefLocal : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff aScaled abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) 0)).toCoeffField := by
    intro R
    simpa only [CoeffSpace.coeffOn_toCoeffField] using haRef R
  obtain ⟨J, hJ, hJupper⟩ :=
    Entry.exists_pow_three_bracket (x := 2 * Rad) (by positivity)
  have hcellScale : ∀ i : system.CellIndex, system.scale i ≤ (J : ℤ) := by
    intro i
    apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp
    exact (ruledCellScale_lt_two_mul_Rad hRad.le system hU.1 i).le.trans hJ
  let nStart : ℤ := max (L : ℤ) ((J : ℤ) + 1)
  obtain ⟨M, hMeq, hnM, hparent⟩ :=
    exists_anchored_common_matImage_enclosingParent hlambdaRange hS hGauge nStart
  have hLM : (L : ℤ) ≤ M := (le_max_left _ _).trans hnM
  have hKM : ∀ i, (ruledObservationCube system i).scale ≤ M := by
    intro i
    have hobs : (ruledObservationCube system i).scale = system.scale i + 1 := rfl
    rw [hobs]
    exact (add_le_add_left (hcellScale i) 1).trans
      ((le_max_right (L : ℤ) ((J : ℤ) + 1)).trans hnM)
  have hEnclose : ∀ i,
      adaptedCellTranslate (epsilonAffineGrid lambda abar)
          (ruledObservationCube system i).scale
          (lambda⁻¹ • matVecMul (matSqrt (symmPart abar))
              (ruledObservationCenter system i) +
            adaptedCellCenter (epsilonAffineGrid lambda abar)
              (ruledObservationCube system i).scale 0) ⊆
        adaptedCell (Selection.normalizedRoot (symmPart abar)) M := by
    intro i
    exact (residualObservationTarget_subset_matImage system abar i).trans hparent
  have hsData := midpointResponseOrder_margins hg
  let responseBound : system.CellIndex → ℝ := fun i ↦
    Real.sqrt
      (observationParentConvolutionFactor d (responseWindowOrder g)
          lambda abar M (ruledObservationCube system i).scale *
        (Real.sqrt deltaScaled *
          (((3 : ℝ) ^ M) / ((3 : ℝ) ^ (L : ℤ))) ^ (-kappaRate)) ^ 2)
  have hfixed : ∀ i,
      Book.Ch02.HomogenizationErrorOnCube
          (ruledObservationCube system i) (responseWindowOrder g)
          .infinity (.finite 2) (aObs i) (1 : Mat d) ≤ responseBound i := by
    intro i
    have hObsI : ((aObs i).coeffOn
        (originCube d (ruledObservationCube system i).scale)).toCoeffField
        =ᵐ[volumeMeasureOn
          (openCubeSet (originCube d (ruledObservationCube system i).scale))]
        fun y ↦ affineCoefficient (matSqrt (symmPart abar))
          (isUnit_det_matSqrt hS)
          (fun z ↦ scaledCoeff lambda aScaled z - skewPart abar)
          (y + ruledObservationCenter system i) := by
      simpa only [ruledObservationCube] using! hObsScaled i
    exact (observationHomogenizationError_le_referencePowerTail_fixedParent
      hsData.1 hsData.2.2.2.2.2 (lt_of_lt_of_le zero_lt_one hlambdaRange.1)
      (Real.sqrt_nonneg deltaScaled) (ruledObservationCenter system i)
      aScaled abar hS 0 aRef haRefLocal (L : ℤ)
      (ruledObservationCube system i).scale M hLM (hKM i) hTail
      (aObs i) hObsI (hEnclose i)).2.2
  have hresponseFormula : ∀ i, responseBound i =
      Real.sqrt
          (observationFillingCoefficient d lambda abar *
            (Book.Ch02.geometricDiscount
              (1 - 2 * responseWindowOrder g) 1)⁻¹) *
        Real.rpow (3 : ℝ)
          (responseWindowOrder g *
            ((M : ℝ) -
              (((ruledObservationCube system i).scale : ℤ) : ℝ))) *
        Real.sqrt deltaScaled *
        Real.rpow (3 : ℝ)
          (-kappaRate * ((M : ℝ) - (L : ℝ))) := by
    intro i
    dsimp only [responseBound]
    exact sqrt_observationParent_powerPrice_eq abar (hKM i)
      (Real.sqrt_nonneg deltaScaled) hsData.2.2.2.2.2.le
  have hN : epsilon⁻¹ ≤ (3 : ℝ) ^ N := by
    calc
      epsilon⁻¹ = epsilon⁻¹ * 1 := by ring
      _ ≤ epsilon⁻¹ * (epsilon * (3 : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left (by simpa only [← hlambda] using hlambdaRange.1)
          (inv_nonneg.mpr hepsilon.le)
      _ = (3 : ℝ) ^ N := by field_simp [hepsilon.ne']
  have hactivation0 : 0 ≤ h.activationScale a :=
    (zero_le_one.trans h.activation_one)
  have hAmplitudeRate : Real.sqrt deltaScaled ≤
      Real.sqrt h.delta * (epsilon * x) ^ kappaRate := by
    rw [hdeltaScaled]
    exact sqrt_triadicallyScaledRowAmplitude_le_physicalFrameRate
      h.delta_nonneg hactivation0 hepsilon hkappa.le
      h.activation_le_common hN
  let Cresponse : ℝ := Real.sqrt
    (observationFillingCoefficient d lambda abar *
      (Book.Ch02.geometricDiscount
        (1 - 2 * responseWindowOrder g) 1)⁻¹)
  let Kframe : ℝ :=
    Cflux * r⁻¹ *
      Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
      responseOneFromTwoGapFactor (responseWindowOrder g) r * Cresponse *
      Real.rpow (3 : ℝ)
        ((r - kappaRate) * (M : ℝ) + kappaRate * (L : ℝ) - r) *
      Real.sqrt h.delta
  have hFrame : PhysicalFluxEpsilonFrameBound system
      (responseWindowOrder g) r Cflux responseBound epsilon x kappaRate Kframe := by
    apply physicalFluxEpsilonFrameBound_of_residualResponsePower
      (epsilon := epsilon) (Xval := x) system
      hsData.1 hresponseOrder hrateOrder responseBound
      (fun _ ↦ M) L M Cresponse (Real.sqrt deltaScaled) (Real.sqrt h.delta)
      hCflux (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · exact hKM
    · intro i
      exact le_rfl
    · intro i
      exact Real.sqrt_nonneg _
    · intro i
      simpa only [Cresponse] using! (hresponseFormula i).le
    · exact hAmplitudeRate
  refine ⟨N, G, J, lambda, deltaScaled, aScaled, aRef, L, M, responseBound,
    Kframe, hlambda, hlambdaRange, haScaled, hdeltaScaled, hG, hGupper, hLeq,
    hLupper, hJ, hJupper, hMeq, rfl, haRef, hTail, hLM, hKM,
    hresponseFormula, ?_, hFrame⟩
  intro i
  simpa only [identityConstantCoeffMatrix_matrix] using hfixed i

end

end RowSupply
end HighContrast
end HCPolySupport
