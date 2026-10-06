/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineH10
public import LeanPool.HighContrastHomogenization.Analytic.AffineNegSobolevNorm
public import LeanPool.HighContrastHomogenization.Analytic.H1a0ToH10
public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CubeFractionalNormBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PhysicalFullDualBesovNorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledBufferedComparisonRealization
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledHardyPositiveRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledLocalizationAssembly
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CenteredIndicatorExtensionBasic
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.RealScaleTriadicBracket
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupplyAssembly.PrintDirectResponseWindowComposition
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.DatumRowAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.ResponseAttainabilityPricing
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.EnlargedMarginDatumRegularity
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderIdentityCubeDualRegularity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.CutoffProduct
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Dilation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Basic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Translation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.SobolevPublic
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.PositiveSeminorms.Definitions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.AECongruence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.DefinitionsAPI
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanGagliardoCoordinateBridgeP
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.OverlapCount
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.BufferToCell.PositiveBesovContinuousComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local positive Besov comparison

The Chapter-3 positive Besov norm is controlled by the continuous
Euclidean fractional square.  The explicit factor is the square of the cube
side length; it is retained here so that the ruled carrier can price it by its
outer radius.
-/

namespace HCPolySupport
namespace HighContrast
namespace BufferToCell

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

@[expose]
public noncomputable def normalizedDomainMeasure
    (V : Set (Vec d)) : Measure (Vec d) :=
  (volume V)⁻¹ • volume.restrict V

private theorem normalizedDomainMeasure_isProbability
    {V : Set (Vec d)} (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤) :
    IsProbabilityMeasure (normalizedDomainMeasure V) := by
  refine ⟨?_⟩
  rw [normalizedDomainMeasure, Measure.smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hVpos.ne' hVtop

private theorem eLpNorm_two_eq_rpow
    {A : Type*} [MeasurableSpace A]
    {E : Type*} [NormedAddCommGroup E] (f : A → E) (mu : Measure A)
    (hf : AEStronglyMeasurable f mu) :
    eLpNorm f 2 mu =
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  norm_num

private theorem integral_normalizedDomainMeasure_eq_volumeAverageVec
    {V : Set (Vec d)} {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict V)) :
    ∫ x, F x ∂normalizedDomainMeasure V = volumeAverageVec V F := by
  funext i
  have hproj : ∫ x in V, F x i ∂volume = (∫ x in V, F x ∂volume) i := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).integral_comp_comm hF
  rw [normalizedDomainMeasure, integral_smul_measure,
    volumeAverageVec, volumeAverage, Pi.smul_apply, smul_eq_mul,
    ENNReal.toReal_inv, hproj]

private theorem enorm_hilbertVec_sq (v : Vec d) :
    ‖HilbertVec.ofVec v‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq v) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simpa [vecNormSq, vecDot, HilbertVec.ofVec, PiLp.toLp_apply, pow_two] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec v)

theorem ofReal_vecNormSq_volumeAverageVec_le_eVolumeAverage
    {V : Set (Vec d)} (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict V)) :
    ENNReal.ofReal (vecNormSq (volumeAverageVec V F)) ≤
      eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (F x))) := by
  let mu := normalizedDomainMeasure V
  let FH : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  have : IsProbabilityMeasure mu :=
    normalizedDomainMeasure_isProbability hVpos hVtop
  have hFHvol : Integrable FH (volume.restrict V) :=
    (HilbertVec.ofVecL d).integrable_comp hF
  have hFHmu : Integrable FH mu := by
    change Integrable FH (normalizedDomainMeasure V)
    exact hFHvol.smul_measure (ENNReal.inv_ne_top.mpr hVpos.ne')
  have hFmu : Integrable F mu := by
    change Integrable F (normalizedDomainMeasure V)
    exact hF.smul_measure (ENNReal.inv_ne_top.mpr hVpos.ne')
  have hL1 : ‖∫ x, FH x ∂mu‖ₑ ≤ ∫⁻ x, ‖FH x‖ₑ ∂mu :=
    enorm_integral_le_lintegral_enorm _
  have hL2 : (∫⁻ x, ‖FH x‖ₑ ∂mu) ≤
      (∫⁻ x, ‖FH x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / (2 : ℝ)) := by
    have hcmp := eLpNorm_le_eLpNorm_of_exponent_le
      (μ := mu) (p := 1) (q := 2) (f := FH)
      (by norm_num)
    rwa [eLpNorm_one_eq_lintegral_enorm hFHmu.aestronglyMeasurable,
      eLpNorm_two_eq_rpow _ _ hFHmu.aestronglyMeasurable] at hcmp
  have hpow := ENNReal.rpow_le_rpow (hL1.trans hL2)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hmean : ∫ x, FH x ∂mu =
      HilbertVec.ofVec (volumeAverageVec V F) := by
    rw [show ∫ x, FH x ∂mu = HilbertVec.ofVec (∫ x, F x ∂mu) by
      simpa [FH] using (HilbertVec.ofVecL d).integral_comp_comm hFmu]
    rw [show ∫ x, F x ∂mu = volumeAverageVec V F by
      exact integral_normalizedDomainMeasure_eq_volumeAverageVec hF]
  rw [← ENNReal.rpow_mul] at hpow
  norm_num at hpow
  rw [hmean] at hpow
  dsimp only [FH] at hpow
  simp_rw [enorm_hilbertVec_sq] at hpow
  simpa [mu, normalizedDomainMeasure, eVolumeAverage,
    lintegral_smul_measure, ENNReal.div_eq_inv_mul, mul_comm] using hpow

private theorem cubeAverageVec_eq_volumeAverageVec_openCube
    (Q : TriadicCube d) (F : Vec d → Vec d) :
    cubeAverageVec Q F = volumeAverageVec (openCubeSet Q) F := by
  funext i
  unfold cubeAverageVec volumeAverageVec cubeAverage volumeAverage
  rw [volume_openCubeSet_toReal,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

theorem ofReal_vecNormSq_cubeAverageVec_le_eVolumeAverage
    (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict (openCubeSet Q))) :
    ENNReal.ofReal (vecNormSq (cubeAverageVec Q F)) ≤
      eVolumeAverage (openCubeSet Q)
        (fun x => ENNReal.ofReal (vecNormSq (F x))) := by
  rw [cubeAverageVec_eq_volumeAverageVec_openCube]
  have hVpos : 0 < volume (openCubeSet Q) := by
    exact (ENNReal.toReal_pos_iff.mp (by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos Q)).1
  exact ofReal_vecNormSq_volumeAverageVec_le_eVolumeAverage
    hVpos (volume_openCubeSet_lt_top Q).ne hF

private theorem scalarGagliardoKernel_aestronglyMeasurable
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hFnorm : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hFcube : AEStronglyMeasurable F (cubeMeasure Q)) (i : Fin d) :
    AEStronglyMeasurable
      (Gagliardo.gagliardoKernel s (2 : ℝ≥0∞) (fun x => F x i))
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let mu1 := normalizedCubeMeasure Q
  let mu2 := cubeMeasure Q
  have : SFinite mu2 := by
    dsimp only [mu2]
    unfold cubeMeasure
    infer_instance
  have hfirst : AEStronglyMeasurable (fun z : Vec d × Vec d => F z.1 i)
      (mu1.prod mu2) :=
    ((continuous_apply i).comp_aestronglyMeasurable hFnorm).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst
  have hsecond : AEStronglyMeasurable (fun z : Vec d × Vec d => F z.2 i)
      (mu1.prod mu2) :=
    ((continuous_apply i).comp_aestronglyMeasurable hFcube).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hdiff : AEStronglyMeasurable
      (fun z : Vec d × Vec d => F z.1 i - F z.2 i) (mu1.prod mu2) :=
    hfirst.sub hsecond
  have hweight : StronglyMeasurable
      (fun z : Vec d × Vec d =>
        dist z.1 z.2 ^ (-Gagliardo.kernelExponent d s (2 : ℝ≥0∞))) :=
    ((continuous_fst.dist continuous_snd).measurable.pow
      measurable_const).stronglyMeasurable
  unfold Gagliardo.gagliardoKernel Gagliardo.gagliardoCubeMeasure
  exact hweight.aestronglyMeasurable.smul hdiff

private theorem cubeAmbientHilbertWspKernel_two_aestronglyMeasurable
    (Q : TriadicCube d) (s : FractionalOrder) (F : Vec d → Vec d)
    (hFnorm : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hFcube : AEStronglyMeasurable F (cubeMeasure Q)) :
    AEStronglyMeasurable (cubeAmbientHilbertWspKernel s FiniteLpExponent.two F)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hfst := hFnorm.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst (ν := cubeMeasure Q))
  have hsnd := hFcube.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := normalizedCubeMeasure Q))
  exact ((continuous_fst.dist continuous_snd).measurable.pow
    measurable_const).aestronglyMeasurable.smul
      ((HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable (hfst.sub hsnd))

private theorem forceSobolevRegularity_of_hsNormSq_lt_top
    [NeZero d] (Q : TriadicCube d) (sF : FractionalOrder)
    (F : Vec d → Vec d)
    (hBesov : ForceBesovRegularity Q sF.1 F)
    (hFcube : MemVectorL2 (openCubeSet Q) F)
    (hHs : hsNormSq (openCubeSet Q) sF.1 F < ⊤) :
    Legacy.ForceSobolevRegularity Q sF.1 F := by
  intro i
  have hmem : MemLp (fun x => F x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hBesov.memLp
  refine ⟨hmem, ?_⟩
  rw [Gagliardo.memWsp_iff]
  constructor
  · exact scalarGagliardoKernel_aestronglyMeasurable Q sF.1 F
      hBesov.memLp.aestronglyMeasurable (by
        simpa [cubeMeasure,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hFcube.aestronglyMeasurable) i
  · have hcoord :
        (Gagliardo.cubeGagliardoESeminorm Q sF.1 (2 : ℝ≥0∞)
          (fun x => F x i)) ^ (2 : ℝ) ≤
          cubeCoordinateGagliardoPowerEnergy Q sF FiniteLpExponent.two F := by
      unfold cubeCoordinateGagliardoPowerEnergy
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d =>
          (Gagliardo.cubeGagliardoESeminorm Q sF.1 (2 : ℝ≥0∞)
            (fun x => F x j)) ^ (2 : ℝ))
        (fun _j _ => zero_le)
        (Finset.mem_univ i)
    have hamb := cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert
      Q sF FiniteLpExponent.two F
    have heuc := cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul
      Q sF FiniteLpExponent.two F
      (cubeAmbientHilbertWspKernel_two_aestronglyMeasurable Q sF F
        hBesov.memLp.aestronglyMeasurable (by
          simpa [cubeMeasure,
            volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
            hFcube.aestronglyMeasurable))
    have hfrac := cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq
      Q sF F hFcube.aestronglyMeasurable
    have hfrac_le : fracSeminormSq (openCubeSet Q) sF.1 F ≤
        hsNormSq (openCubeSet Q) sF.1 F := by
      unfold hsNormSq
      exact le_add_left le_rfl
    have hright :
        (d : ℝ≥0∞) * cubeEuclideanWspMetricComparisonConstant d
            FiniteLpExponent.two *
          fracSeminormSq (openCubeSet Q) sF.1 F < ⊤ := by
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by simp)
          (cubeEuclideanWspMetricComparisonConstant_lt_top d
            FiniteLpExponent.two))
        (lt_of_le_of_lt hfrac_le hHs)
    have hpow :
        (Gagliardo.cubeGagliardoESeminorm Q sF.1 (2 : ℝ≥0∞)
          (fun x => F x i)) ^ (2 : ℝ) < ⊤ := by
      refine lt_of_le_of_lt (hcoord.trans (hamb.trans ?_)) hright
      calc
        (d : ℝ≥0∞) *
            cubeAmbientHilbertWspESeminorm Q sF FiniteLpExponent.two F ^
              FiniteLpExponent.two.exponent.toReal ≤
          (d : ℝ≥0∞) *
            (cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two *
              cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two F ^
                FiniteLpExponent.two.exponent.toReal) :=
          mul_le_mul_right heuc _
        _ = (d : ℝ≥0∞) *
            cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two *
              fracSeminormSq (openCubeSet Q) sF.1 F := by
          norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
          rw [ENNReal.rpow_two, hfrac]
          ring_nf
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp hpow

/-- The dimension-only comparison coefficient between the Chapter-3
positive Besov norm and the continuous Euclidean fractional square. -/
@[expose]
noncomputable def positiveBesovContinuousComparisonConstant (d : ℕ) : ℝ :=
  2 * (1 +
    ((3 : ℝ) ^ ((d : ℝ) / 2) * Book.Ch01.Legacy.wspVsBsppConstant d) ^ 2 *
      (d : ℝ) ^ 2 *
      (cubeEuclideanWspMetricComparisonConstant d
        FiniteLpExponent.two).toReal)

theorem positiveBesovContinuousComparisonConstant_pos (d : ℕ) :
    0 < positiveBesovContinuousComparisonConstant d := by
  unfold positiveBesovContinuousComparisonConstant
  have hmetric : 0 ≤ (cubeEuclideanWspMetricComparisonConstant d
      FiniteLpExponent.two).toReal := ENNReal.toReal_nonneg
  positivity

private theorem cube_hsScale_eq_ofReal [NeZero d]
    (Q : TriadicCube d) (s : ℝ) :
    volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) =
      ENNReal.ofReal ((cubeScaleFactor Q) ^ (-2 * s)) := by
  have hell : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hvol : volume (openCubeSet Q) =
      ENNReal.ofReal ((cubeScaleFactor Q) ^ d) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (volume_openCubeSet_lt_top Q).ne ENNReal.ofReal_ne_top).mp
    rw [volume_openCubeSet_toReal,
      ENNReal.toReal_ofReal (by positivity), cubeVolume_eq_scaleFactor_pow]
  rw [hvol, ENNReal.ofReal_rpow_of_pos (pow_pos hell d)]
  apply congrArg ENNReal.ofReal
  rw [← Real.rpow_natCast, ← Real.rpow_mul hell.le]
  congr 1
  field_simp

/-- A local Chapter-3 positive Besov square is bounded by the Euclidean
fractional square, with the exact side-length factor exposed. -/
theorem positiveBesovNorm_sq_le_continuousFractionalSquare
    [NeZero d] (Q : TriadicCube d) (sF : FractionalOrder)
    (F : Vec d → Vec d)
    (hBesov : ForceBesovRegularity Q sF.1 F)
    (hFcube : MemVectorL2 (openCubeSet Q) F) :
    ENNReal.ofReal
        (scaleNormalizedPositiveBesovVectorNormTwo Q sF.1 F) ^ 2 ≤
      ENNReal.ofReal (positiveBesovContinuousComparisonConstant d) *
        ENNReal.ofReal ((cubeScaleFactor Q) ^ (2 * sF.1)) *
          hsNormSq (openCubeSet Q) sF.1 F := by
  let E : ℝ≥0∞ := hsNormSq (openCubeSet Q) sF.1 F
  let L : ℝ≥0∞ := eVolumeAverage (openCubeSet Q)
    (fun x => ENNReal.ofReal (vecNormSq (F x)))
  let W2 : ℝ≥0∞ := fracSeminormSq (openCubeSet Q) sF.1 F
  let ell : ℝ := cubeScaleFactor Q
  let K : ℝ := (3 : ℝ) ^ ((d : ℝ) / 2) *
    Book.Ch01.Legacy.wspVsBsppConstant d
  let M : ℝ := (cubeEuclideanWspMetricComparisonConstant d
    FiniteLpExponent.two).toReal
  have hell : 0 < ell := by
    dsimp only [ell]
    exact cubeScaleFactor_pos' Q
  have hC : 0 < positiveBesovContinuousComparisonConstant d :=
    positiveBesovContinuousComparisonConstant_pos d
  by_cases hEtop : E = ⊤
  · have hscale : 0 < ell ^ (2 * sF.1) := Real.rpow_pos_of_pos hell _
    change _ ≤ ENNReal.ofReal (positiveBesovContinuousComparisonConstant d) *
      ENNReal.ofReal (ell ^ (2 * sF.1)) * E
    rw [hEtop]
    simp [hscale, hC]
  have hElt : E < ⊤ := lt_top_iff_ne_top.mpr hEtop
  have hSob : Legacy.ForceSobolevRegularity Q sF.1 F :=
    forceSobolevRegularity_of_hsNormSq_lt_top Q sF F hBesov hFcube hElt
  have hLle : L ≤ E * ENNReal.ofReal (ell ^ (2 * sF.1)) := by
    have hterm : ENNReal.ofReal (ell ^ (-2 * sF.1)) * L ≤ E := by
      dsimp only [E, L]
      unfold hsNormSq
      rw [cube_hsScale_eq_ofReal Q sF.1]
      exact le_add_right le_rfl
    have hcancel : ENNReal.ofReal (ell ^ (2 * sF.1)) *
        ENNReal.ofReal (ell ^ (-2 * sF.1)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hell.le _),
        ← Real.rpow_add hell]
      ring_nf
      simp only [Real.rpow_zero, ENNReal.ofReal_one]
    calc
      L = 1 * L := by rw [one_mul]
      _ = (ENNReal.ofReal (ell ^ (2 * sF.1)) *
          ENNReal.ofReal (ell ^ (-2 * sF.1))) * L := by rw [hcancel]
      _ = ENNReal.ofReal (ell ^ (2 * sF.1)) *
          (ENNReal.ofReal (ell ^ (-2 * sF.1)) * L) := mul_assoc _ _ _
      _ ≤ ENNReal.ofReal (ell ^ (2 * sF.1)) * E :=
        mul_le_mul_right hterm _
      _ = E * ENNReal.ofReal (ell ^ (2 * sF.1)) := mul_comm _ _
  have hW2le : W2 ≤ E := by
    dsimp only [W2, E]
    unfold hsNormSq
    exact le_add_left le_rfl
  have hLtop : L ≠ ⊤ := (lt_of_le_of_lt hLle (ENNReal.mul_lt_top hElt
    ENNReal.ofReal_lt_top)).ne
  have hW2top : W2 ≠ ⊤ := (lt_of_le_of_lt hW2le hElt).ne
  let : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by simpa using volume_openCubeSet_lt_top Q⟩
  have hmeanENN := ofReal_vecNormSq_cubeAverageVec_le_eVolumeAverage Q
    (hFcube.integrable (by norm_num))
  have hmean : vecNormSq (cubeAverageVec Q F) ≤ L.toReal := by
    have hmean0 := ENNReal.toReal_mono hLtop
      (by simpa only [L] using hmeanENN)
    simpa [ENNReal.toReal_ofReal (vecNormSq_nonneg _)] using hmean0
  have hLreal : L.toReal ≤ ell ^ (2 * sF.1) * E.toReal := by
    have hrightTop : E * ENNReal.ofReal (ell ^ (2 * sF.1)) ≠ ⊤ :=
      (ENNReal.mul_lt_top hElt ENNReal.ofReal_lt_top).ne
    have := ENNReal.toReal_mono hrightTop hLle
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg hell.le _), mul_comm] using this
  have hW2real : W2.toReal ≤ E.toReal :=
    ENNReal.toReal_mono hEtop hW2le
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Book.Ch01.Legacy.wspVsBsppConstant_pos d).le
  have hMnonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hSemi :=
    Book.Ch03.Legacy.scaleNormalizedPositiveBesovVectorSeminormTwo_le_const_mul_sobolev
      Q F sF.2.1 sF.2.2.le hSob
  have hSeminonneg : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      Q sF.1 F :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      hBesov
  have hWnonneg : 0 ≤ Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
      Q sF.1 F := Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo_nonneg Q sF.1 F
  have hSemiSq :
      scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 F ^ 2 ≤
        K ^ 2 *
          (Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
            Q sF.1 F) ^ 2 := by
    have hp := pow_le_pow_left₀ hSeminonneg hSemi 2
    simpa only [K, mul_pow] using hp
  have hcoord := cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert
    Q sF FiniteLpExponent.two F
  have heuc := cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul
    Q sF FiniteLpExponent.two F
    (cubeAmbientHilbertWspKernel_two_aestronglyMeasurable Q sF F
      hBesov.memLp.aestronglyMeasurable (by
        simpa [cubeMeasure,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
          hFcube.aestronglyMeasurable))
  have hfrac := cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq
    Q sF F hFcube.aestronglyMeasurable
  let Coord : ℝ≥0∞ := cubeCoordinateGagliardoPowerEnergy
    Q sF FiniteLpExponent.two F
  have hCoordle : Coord ≤ (d : ℝ≥0∞) *
      cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two * W2 := by
    dsimp only [Coord]
    calc
      cubeCoordinateGagliardoPowerEnergy Q sF FiniteLpExponent.two F ≤
          (d : ℝ≥0∞) *
            cubeAmbientHilbertWspESeminorm Q sF FiniteLpExponent.two F ^
              FiniteLpExponent.two.exponent.toReal := hcoord
      _ ≤ (d : ℝ≥0∞) *
          (cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two *
            cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two F ^
              FiniteLpExponent.two.exponent.toReal) :=
        mul_le_mul_right heuc _
      _ = (d : ℝ≥0∞) *
          cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two * W2 := by
        norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
        rw [ENNReal.rpow_two, hfrac]
        dsimp only [W2]
        exact (mul_assoc _ _ _).symm
  have hCoordTop : Coord ≠ ⊤ := (lt_of_le_of_lt hCoordle
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by simp)
        (cubeEuclideanWspMetricComparisonConstant_lt_top d FiniteLpExponent.two))
      (lt_top_iff_ne_top.mpr hW2top))).ne
  let G : Fin d → ℝ := fun i =>
    Gagliardo.cubeGagliardoSeminorm Q sF.1 (2 : ℝ≥0∞) (fun x => F x i)
  have hGnonneg : ∀ i, 0 ≤ G i := fun _ => ENNReal.toReal_nonneg
  have hsumSq : (∑ i, G i) ^ 2 ≤ (d : ℝ) * ∑ i, (G i) ^ 2 := by
    simpa [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := G))
  have hCoordReal : (∑ i, (G i) ^ 2) = Coord.toReal := by
    dsimp only [Coord, G]
    unfold cubeCoordinateGagliardoPowerEnergy Gagliardo.cubeGagliardoSeminorm
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i _hi
      norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
      rw [ENNReal.rpow_two, ENNReal.toReal_pow]
    · intro i _hi
      exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (hSob i).2.eSeminorm_lt_top.ne).ne
  have hCoordRealLe : Coord.toReal ≤ (d : ℝ) * M * W2.toReal := by
    have hrightTop : (d : ℝ≥0∞) *
        cubeEuclideanWspMetricComparisonConstant d FiniteLpExponent.two * W2 ≠ ⊤ :=
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by simp)
          (cubeEuclideanWspMetricComparisonConstant_lt_top d FiniteLpExponent.two))
        (lt_top_iff_ne_top.mpr hW2top)).ne
    have := ENNReal.toReal_mono hrightTop hCoordle
    simpa [M, ENNReal.toReal_mul] using this
  have hsumLe : (∑ i, G i) ^ 2 ≤ (d : ℝ) ^ 2 * M * W2.toReal := by
    calc
      (∑ i, G i) ^ 2 ≤ (d : ℝ) * ∑ i, (G i) ^ 2 := hsumSq
      _ = (d : ℝ) * Coord.toReal := by rw [hCoordReal]
      _ ≤ (d : ℝ) * ((d : ℝ) * M * W2.toReal) :=
        mul_le_mul_of_nonneg_left hCoordRealLe (Nat.cast_nonneg d)
      _ = (d : ℝ) ^ 2 * M * W2.toReal := by ring_nf
  have hWformula :
      Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo Q sF.1 F =
        ell ^ sF.1 * ∑ i, G i := by
    unfold Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
      cubeBesovScaleWeight
    dsimp only [ell, G]
    congr 1
    ring_nf
  have hWSq :
      (Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo Q sF.1 F) ^ 2 ≤
        ell ^ (2 * sF.1) * ((d : ℝ) ^ 2 * M * W2.toReal) := by
    rw [hWformula, mul_pow]
    have hscale0 : 0 ≤ ell ^ (2 * sF.1) := Real.rpow_nonneg hell.le _
    calc
      (ell ^ sF.1) ^ 2 * (∑ i, G i) ^ 2 =
          ell ^ (2 * sF.1) * (∑ i, G i) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hell.le]
        congr 2
        ring_nf
      _ ≤ ell ^ (2 * sF.1) * ((d : ℝ) ^ 2 * M * W2.toReal) :=
        mul_le_mul_of_nonneg_left hsumLe hscale0
  have hBsemi :
      scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 F ^ 2 ≤
        K ^ 2 * (ell ^ (2 * sF.1) *
          ((d : ℝ) ^ 2 * M * E.toReal)) := by
    calc
      scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 F ^ 2 ≤
          K ^ 2 *
            (Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
              Q sF.1 F) ^ 2 := hSemiSq
      _ ≤ K ^ 2 * (ell ^ (2 * sF.1) *
          ((d : ℝ) ^ 2 * M * W2.toReal)) :=
        mul_le_mul_of_nonneg_left hWSq (sq_nonneg K)
      _ ≤ K ^ 2 * (ell ^ (2 * sF.1) *
          ((d : ℝ) ^ 2 * M * E.toReal)) := by
        gcongr
  have hmeanSq : (Real.sqrt (vecNormSq (cubeAverageVec Q F))) ^ 2 ≤
      ell ^ (2 * sF.1) * E.toReal := by
    rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    exact hmean.trans hLreal
  have hreal :
      (scaleNormalizedPositiveBesovVectorNormTwo Q sF.1 F) ^ 2 ≤
        positiveBesovContinuousComparisonConstant d *
          ell ^ (2 * sF.1) * E.toReal := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    calc
      (Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
          scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 F) ^ 2 ≤
          2 * ((Real.sqrt (vecNormSq (cubeAverageVec Q F))) ^ 2 +
            scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 F ^ 2) :=
        add_sq_le
      _ ≤ 2 * (ell ^ (2 * sF.1) * E.toReal +
          K ^ 2 * (ell ^ (2 * sF.1) *
            ((d : ℝ) ^ 2 * M * E.toReal))) := by
        gcongr
      _ = positiveBesovContinuousComparisonConstant d *
          ell ^ (2 * sF.1) * E.toReal := by
        unfold positiveBesovContinuousComparisonConstant
        dsimp only [K, M]
        ring_nf
  have hBnonneg : 0 ≤
      scaleNormalizedPositiveBesovVectorNormTwo Q sF.1 F := by
    unfold scaleNormalizedPositiveBesovVectorNormTwo
    exact add_nonneg (Real.sqrt_nonneg _) hSeminonneg
  calc
    ENNReal.ofReal
        (scaleNormalizedPositiveBesovVectorNormTwo Q sF.1 F) ^ 2 =
      ENNReal.ofReal
        ((scaleNormalizedPositiveBesovVectorNormTwo Q sF.1 F) ^ 2) := by
        rw [ENNReal.ofReal_pow hBnonneg]
    _ ≤
      ENNReal.ofReal
        (positiveBesovContinuousComparisonConstant d *
          ell ^ (2 * sF.1) * E.toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (positiveBesovContinuousComparisonConstant d) *
        ENNReal.ofReal (ell ^ (2 * sF.1)) * E := by
      rw [ENNReal.ofReal_mul
          (mul_nonneg hC.le (Real.rpow_nonneg hell.le _)),
        ENNReal.ofReal_mul hC.le,
        ENNReal.ofReal_toReal hEtop]
    _ = _ := by rfl

end

end BufferToCell
end HighContrast
end HCPolySupport
