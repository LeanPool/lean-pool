/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RowRetainingGoodScaleInterface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ObservationHomogenizationErrorPowerTail
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealTranslationCoeffSpace
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PhysicalFluxRateAggregationReduction

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.ResidualFrameResponseRateAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Residual-frame response-rate algebra

Once the stochastic row has been converted before aggregation, the remaining
scale bookkeeping is deterministic.  The observation filling grows at the
response order, while the physical dual norm contributes the larger target
order.  A common upper parent generation therefore gives a uniform cell
coefficient.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03

noncomputable section

variable {d : ℕ}

private theorem residual_frame_exponent_le
    {r b kappa K M Mmax L : ℝ}
    (hbr : b ≤ r) (hkr : kappa ≤ r)
    (hKM : K ≤ M) (hMM : M ≤ Mmax) :
    r * (K - 1) + b * (M - K) - kappa * (M - L) ≤
      (r - kappa) * Mmax + kappa * L - r := by
  by_cases hbk : b ≤ kappa
  · have hbk0 : b - kappa ≤ 0 := sub_nonpos.mpr hbk
    have hgap0 : 0 ≤ M - K := sub_nonneg.mpr hKM
    have hdrop : (b - kappa) * (M - K) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hbk0 hgap0
    have hrk : 0 ≤ r - kappa := sub_nonneg.mpr hkr
    have hKmax : K ≤ Mmax := hKM.trans hMM
    have hmono : (r - kappa) * K ≤ (r - kappa) * Mmax :=
      mul_le_mul_of_nonneg_left hKmax hrk
    linarith only [hdrop, hmono]
  · have hkb : kappa ≤ b := le_of_not_ge hbk
    have hbk0 : 0 ≤ b - kappa := sub_nonneg.mpr hkb
    have hgap : M - K ≤ Mmax - K := sub_le_sub_right hMM K
    have hgapMul : (b - kappa) * (M - K) ≤
        (b - kappa) * (Mmax - K) :=
      mul_le_mul_of_nonneg_left hgap hbk0
    have hrb : 0 ≤ r - b := sub_nonneg.mpr hbr
    have hKmax : K ≤ Mmax := hKM.trans hMM
    have hmono : (r - b) * K ≤ (r - b) * Mmax :=
      mul_le_mul_of_nonneg_left hKmax hrb
    linarith only [hgapMul, hmono]

private theorem physicalDualBesovScaleFactor_eq_rpow_rate
    (Q : TriadicCube d) (r : ℝ) :
    physicalDualBesovScaleFactor Q r =
      Real.rpow (3 : ℝ) (r * ((Q.scale : ℤ) : ℝ)) := by
  unfold physicalDualBesovScaleFactor
  have hneg : Real.rpow (3 : ℝ) (-(r * ((Q.scale : ℤ) : ℝ))) =
      (Real.rpow (3 : ℝ) (r * ((Q.scale : ℤ) : ℝ)))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [show -r * ((Q.scale : ℤ) : ℝ) =
    -(r * ((Q.scale : ℤ) : ℝ)) by ring, hneg, inv_inv]

private theorem residual_frame_three_power_le
    {r b kappa K M Mmax L : ℝ}
    (hbr : b ≤ r) (hkr : kappa ≤ r)
    (hKM : K ≤ M) (hMM : M ≤ Mmax) :
    Real.rpow (3 : ℝ) (r * (K - 1)) *
        Real.rpow (3 : ℝ) (b * (M - K)) *
        Real.rpow (3 : ℝ) (-kappa * (M - L)) ≤
      Real.rpow (3 : ℝ) ((r - kappa) * Mmax + kappa * L - r) := by
  calc
    Real.rpow (3 : ℝ) (r * (K - 1)) *
        Real.rpow (3 : ℝ) (b * (M - K)) *
        Real.rpow (3 : ℝ) (-kappa * (M - L)) =
      Real.rpow (3 : ℝ)
        (r * (K - 1) + b * (M - K) + -kappa * (M - L)) := by
          calc
            Real.rpow (3 : ℝ) (r * (K - 1)) *
                Real.rpow (3 : ℝ) (b * (M - K)) *
                Real.rpow (3 : ℝ) (-kappa * (M - L)) =
              Real.rpow (3 : ℝ)
                  (r * (K - 1) + b * (M - K)) *
                Real.rpow (3 : ℝ) (-kappa * (M - L)) := by
                  exact congrArg
                    (fun z : ℝ ↦ z *
                      Real.rpow (3 : ℝ) (-kappa * (M - L)))
                    (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                      (r * (K - 1)) (b * (M - K))).symm
            _ = Real.rpow (3 : ℝ)
                (r * (K - 1) + b * (M - K) + -kappa * (M - L)) := by
                  exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                    (r * (K - 1) + b * (M - K))
                    (-kappa * (M - L))).symm
    _ ≤ Real.rpow (3 : ℝ) ((r - kappa) * Mmax + kappa * L - r) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hexponent := residual_frame_exponent_le hbr hkr hKM hMM (L := L)
        have hleft :
            r * (K - 1) + b * (M - K) + -kappa * (M - L) =
              r * (K - 1) + b * (M - K) - kappa * (M - L) := by ring
        rw [hleft]
        exact hexponent)

/-- A common parent-generation cap and the transported row amplitude imply
the uniform physical-frame premise used by RATE-AGG.  This statement isolates
the geometric input from the stochastic order conversion. -/
theorem physicalFluxEpsilonFrameBound_of_residualResponsePower
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    {b r Cflux epsilon Xval kappaRate : ℝ}
    (hb : 0 < b) (hbr : b < r) (hkr : kappaRate ≤ r)
    (responseBound : system.CellIndex → ℝ)
    (M : system.CellIndex → ℤ) (L : ℕ) (Mmax : ℤ)
    (Cresponse amplitude Arate : ℝ)
    (hCflux : 0 ≤ Cflux) (hCresponse : 0 ≤ Cresponse)
    (hAmplitude : 0 ≤ amplitude) (hArate : 0 ≤ Arate)
    (hM : ∀ i, (ruledObservationCube system i).scale ≤ M i)
    (hMmax : ∀ i, M i ≤ Mmax)
    (hResponseNonneg : ∀ i, 0 ≤ responseBound i)
    (hResponse : ∀ i, responseBound i ≤
      Cresponse *
        Real.rpow (3 : ℝ)
          (b * (((M i : ℤ) : ℝ) -
            (((ruledObservationCube system i).scale : ℤ) : ℝ))) *
        amplitude *
        Real.rpow (3 : ℝ)
          (-kappaRate * (((M i : ℤ) : ℝ) - (L : ℝ))))
    (hAmplitudeRate : amplitude ≤ Arate * (epsilon * Xval) ^ kappaRate) :
    PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
      epsilon Xval kappaRate
        (Cflux * r⁻¹ *
          constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r * Cresponse *
          Real.rpow (3 : ℝ)
            ((r - kappaRate) * (Mmax : ℝ) + kappaRate * (L : ℝ) - r) *
          Arate) := by
  let Kframe : ℝ :=
    Cflux * r⁻¹ *
      constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
      responseOneFromTwoGapFactor b r * Cresponse *
      Real.rpow (3 : ℝ)
        ((r - kappaRate) * (Mmax : ℝ) + kappaRate * (L : ℝ) - r) *
      Arate
  have hr : 0 < r := hb.trans hbr
  have hmatrix : 0 ≤
      constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) := by
    unfold constantCoeffMatrixNormHalf
    exact Real.rpow_nonneg (Book.Ch02.matrixNorm_nonneg _) _
  have hgap : 0 ≤ responseOneFromTwoGapFactor b r :=
    responseOneFromTwoGapFactor_nonneg hb hbr
  have hfrontBase : 0 ≤
      Cflux * r⁻¹ *
        constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
        responseOneFromTwoGapFactor b r * Cresponse := by
    have h1 := mul_nonneg hCflux (inv_nonneg.mpr hr.le)
    have h2 := mul_nonneg h1 hmatrix
    have h3 := mul_nonneg h2 hgap
    exact mul_nonneg h3 hCresponse
  have hpowerConstant : 0 ≤
      Real.rpow (3 : ℝ)
        ((r - kappaRate) * (Mmax : ℝ) + kappaRate * (L : ℝ) - r) :=
    Real.rpow_nonneg (by norm_num) _
  have hKframe : 0 ≤ Kframe := by
    dsimp only [Kframe]
    have h5 := mul_nonneg hfrontBase hpowerConstant
    exact mul_nonneg h5 hArate
  change PhysicalFluxEpsilonFrameBound system b r Cflux responseBound
    epsilon Xval kappaRate Kframe
  refine ⟨hKframe, ?_⟩
  intro i
  have hscale0 : 0 ≤ physicalDualBesovScaleFactor
      (whitneyCellCube system i) r :=
    physicalDualBesovScaleFactor_nonneg _ _
  have hcoefficient0 : 0 ≤ ruledPhysicalFluxResponseCoefficient
      system b r Cflux responseBound i := by
    unfold ruledPhysicalFluxResponseCoefficient
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hscale0 hCflux) (inv_nonneg.mpr hr.le)) hmatrix)
          hgap)
      (hResponseNonneg i)
  refine ⟨hcoefficient0, ?_⟩
  let K : ℝ := (((ruledObservationCube system i).scale : ℤ) : ℝ)
  let Mi : ℝ := ((M i : ℤ) : ℝ)
  have hKM : K ≤ Mi := by
    dsimp only [K, Mi]
    exact_mod_cast hM i
  have hMM : Mi ≤ (Mmax : ℝ) := by
    dsimp only [Mi]
    exact_mod_cast hMmax i
  have hpower := residual_frame_three_power_le hbr.le hkr hKM hMM
    (L := (L : ℝ))
  have hcellScale : (((whitneyCellCube system i).scale : ℤ) : ℝ) = K - 1 := by
    simp only [K, ruledObservationCube, whitneyCellCube, originCube,
      translateCube, Int.cast_add, Int.cast_one]
    ring
  have hresponseScaled :
      physicalDualBesovScaleFactor (whitneyCellCube system i) r *
          responseBound i ≤
        Cresponse *
          Real.rpow (3 : ℝ)
            ((r - kappaRate) * (Mmax : ℝ) +
              kappaRate * (L : ℝ) - r) *
          amplitude := by
    rw [physicalDualBesovScaleFactor_eq_rpow_rate, hcellScale]
    calc
      Real.rpow (3 : ℝ) (r * (K - 1)) * responseBound i ≤
          Real.rpow (3 : ℝ) (r * (K - 1)) *
            (Cresponse * Real.rpow (3 : ℝ) (b * (Mi - K)) * amplitude *
              Real.rpow (3 : ℝ) (-kappaRate * (Mi - (L : ℝ)))) :=
        mul_le_mul_of_nonneg_left (by simpa only [K, Mi] using hResponse i)
          (Real.rpow_nonneg (by norm_num) _)
      _ = Cresponse *
          (Real.rpow (3 : ℝ) (r * (K - 1)) *
            Real.rpow (3 : ℝ) (b * (Mi - K)) *
            Real.rpow (3 : ℝ) (-kappaRate * (Mi - (L : ℝ)))) *
          amplitude := by ring
      _ ≤ Cresponse *
          Real.rpow (3 : ℝ)
            ((r - kappaRate) * (Mmax : ℝ) +
              kappaRate * (L : ℝ) - r) * amplitude := by
        gcongr
  unfold ruledPhysicalFluxResponseCoefficient
  calc
    physicalDualBesovScaleFactor (whitneyCellCube system i) r * Cflux * r⁻¹ *
          constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r * responseBound i =
        (Cflux * r⁻¹ *
          constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r) *
          (physicalDualBesovScaleFactor (whitneyCellCube system i) r *
            responseBound i) := by ring
    _ ≤ (Cflux * r⁻¹ *
          constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
          responseOneFromTwoGapFactor b r) *
        (Cresponse *
          Real.rpow (3 : ℝ)
            ((r - kappaRate) * (Mmax : ℝ) +
              kappaRate * (L : ℝ) - r) * amplitude) := by
      exact mul_le_mul_of_nonneg_left hresponseScaled (by positivity)
    _ ≤ Kframe * (epsilon * Xval) ^ kappaRate := by
      dsimp only [Kframe]
      have hfront : 0 ≤
          Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
            responseOneFromTwoGapFactor b r * Cresponse *
            Real.rpow (3 : ℝ)
              ((r - kappaRate) * (Mmax : ℝ) +
                kappaRate * (L : ℝ) - r) := by
        exact mul_nonneg hfrontBase hpowerConstant
      calc
        (Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
            responseOneFromTwoGapFactor b r) *
          (Cresponse *
            Real.rpow (3 : ℝ)
              ((r - kappaRate) * (Mmax : ℝ) +
                kappaRate * (L : ℝ) - r) * amplitude) =
          (Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
            responseOneFromTwoGapFactor b r * Cresponse *
            Real.rpow (3 : ℝ)
              ((r - kappaRate) * (Mmax : ℝ) +
                kappaRate * (L : ℝ) - r)) * amplitude := by ring
        _ ≤ (Cflux * r⁻¹ *
            constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d) *
            responseOneFromTwoGapFactor b r * Cresponse *
            Real.rpow (3 : ℝ)
              ((r - kappaRate) * (Mmax : ℝ) +
                kappaRate * (L : ℝ) - r)) *
              (Arate * (epsilon * Xval) ^ kappaRate) :=
          mul_le_mul_of_nonneg_left hAmplitudeRate hfront
        _ = Kframe * (epsilon * Xval) ^ kappaRate := by ring

end

end RowSupply
end HighContrast
end HCPolySupport
