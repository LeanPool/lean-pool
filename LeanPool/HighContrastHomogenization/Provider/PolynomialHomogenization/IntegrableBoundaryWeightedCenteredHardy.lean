/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightedCenteredEndpoint
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.IntegrableBoundaryWeightedCenteredHardy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Boundary-weighted Hardy estimate for integrable fields

The endpoint estimate is extended from continuous fields to integrable fields.
The only pointwise input in the available proof is convergence of averages on
the shrinking convex chain.  Lebesgue differentiation supplies that
convergence almost everywhere, because the displaced Euclidean chain balls
have uniformly bounded eccentricity relative to ambient metric balls.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

@[expose]
public noncomputable def normalizedChainMeasure
    (c x : Vec d) (rho : ℝ) (n : ℕ) : Measure (Vec d) :=
  (volume (convexFractionalChainBall c x rho n))⁻¹ •
    volume.restrict (convexFractionalChainBall c x rho n)

private theorem volume_chainBall_pos_integrable
    (c x : Vec d) {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    0 < volume (convexFractionalChainBall c x rho n) := by
  unfold convexFractionalChainBall
  exact IsOpen.measure_pos volume (isOpen_euclideanBallAt _ _)
    ⟨_, center_mem_euclideanBallAt _
      (mul_pos (convexFractionalChainScale_pos n) hrho)⟩

private theorem volume_chainBall_ne_top_integrable
    (c x : Vec d) {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    volume (convexFractionalChainBall c x rho n) ≠ ⊤ := by
  exact (isOpenBoundedConvexDomain_euclideanBallAt _
    (mul_pos (convexFractionalChainScale_pos n) hrho)).volume_lt_top.ne

private theorem normalizedChainMeasure_isProbability
    (c x : Vec d) {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    IsProbabilityMeasure (normalizedChainMeasure c x rho n) := by
  refine ⟨?_⟩
  rw [normalizedChainMeasure, Measure.smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (volume_chainBall_pos_integrable c x hrho n).ne'
    (volume_chainBall_ne_top_integrable c x hrho n)

private theorem integral_normalizedChainMeasure_eq_mean
    (c x : Vec d) {rho : ℝ} (hrho : 0 < rho) (n : ℕ)
    {F : Vec d → Vec d}
    (hF : Integrable F
      (volume.restrict (convexFractionalChainBall c x rho n))) :
    ∫ y, HilbertVec.ofVec (F y) ∂normalizedChainMeasure c x rho n =
      HilbertVec.ofVec (convexFractionalChainMean c x rho F n) := by
  have hFnorm : Integrable F (normalizedChainMeasure c x rho n) :=
    hF.smul_measure (ENNReal.inv_ne_top.mpr
      (volume_chainBall_pos_integrable c x hrho n).ne')
  rw [show ∫ y, HilbertVec.ofVec (F y) ∂normalizedChainMeasure c x rho n =
      HilbertVec.ofVec (∫ y, F y ∂normalizedChainMeasure c x rho n) by
    simpa using (HilbertVec.ofVecL d).integral_comp_comm hFnorm]
  congr 1
  funext i
  have hproj :
      ∫ y in convexFractionalChainBall c x rho n, F y i ∂volume =
        (∫ y in convexFractionalChainBall c x rho n, F y ∂volume) i := by
    simpa using (ContinuousLinearMap.proj (R := ℝ) i).integral_comp_comm hF
  simp only [normalizedChainMeasure, integral_smul_measure,
    convexFractionalChainMean, volumeAverageVec, volumeAverage,
    Pi.smul_apply, smul_eq_mul, ENNReal.toReal_inv]
  rw [hproj]

private theorem volume_closedBall_vec {d : ℕ} (x : Vec d) {r : ℝ}
    (hr : 0 ≤ r) :
    volume (Metric.closedBall x r) = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [MeasureTheory.volume_pi_closedBall x hr]
  simp only [Real.volume_closedBall, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * r)]

private theorem normalizedChainMeasure_le_closedBallAverage
    (hd : 1 ≤ d) (c x : Vec d) {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    normalizedChainMeasure c x rho n ≤
      ENNReal.ofReal ((Real.sqrt d) ^ d) •
        ((volume (Metric.closedBall (convexFractionalChainCenter c x n)
          (convexFractionalChainScale n * rho)))⁻¹ •
          volume.restrict (Metric.closedBall (convexFractionalChainCenter c x n)
            (convexFractionalChainScale n * rho))) := by
  let z := convexFractionalChainCenter c x n
  let r := convexFractionalChainScale n * rho
  let A : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt d) ^ d)
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hr : 0 < r := mul_pos (convexFractionalChainScale_pos n) hrho
  have hsub : convexFractionalChainBall c x rho n ⊆ Metric.closedBall z r := by
    intro y hy
    have hy' : y ∈ Metric.ball z r := by
      exact euclideanBallAt_subset_metricBall z hr hy
    exact Metric.ball_subset_closedBall hy'
  have hsmall : Metric.ball z (r / Real.sqrt d) ⊆
      convexFractionalChainBall c x rho n := by
    simpa only [z, r, convexFractionalChainBall] using
      metricBall_subset_euclideanBallAt hdpos z hr
  have hvolLower : ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d) ≤
      volume (convexFractionalChainBall c x rho n) := by
    rw [← volume_ball_eq z (div_pos hr hsqrt)]
    exact measure_mono hsmall
  have hvolClosed : volume (Metric.closedBall z r) =
      ENNReal.ofReal ((2 * r) ^ d) := volume_closedBall_vec z hr.le
  have hfactor : volume (Metric.closedBall z r) ≤
      A * volume (convexFractionalChainBall c x rho n) := by
    rw [hvolClosed]
    calc
      ENNReal.ofReal ((2 * r) ^ d) =
          A * ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt d) ^ d)]
        congr 1
        rw [show 2 * (r / Real.sqrt d) = (2 * r) / Real.sqrt d by
          field_simp]
        rw [div_pow]
        field_simp
      _ ≤ A * volume (convexFractionalChainBall c x rho n) :=
        mul_le_mul_right hvolLower A
  apply Measure.le_iff'.2
  intro S
  rw [normalizedChainMeasure, Measure.smul_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  have hrestr : (volume.restrict (convexFractionalChainBall c x rho n)) S ≤
      (volume.restrict (Metric.closedBall z r)) S :=
    Measure.restrict_mono_set volume hsub S
  have hEpos := volume_chainBall_pos_integrable c x hrho n
  have hEtop := volume_chainBall_ne_top_integrable c x hrho n
  have hBpos : 0 < volume (Metric.closedBall z r) :=
    Metric.measure_closedBall_pos volume z hr
  have hBtop : volume (Metric.closedBall z r) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hinv : (volume (convexFractionalChainBall c x rho n))⁻¹ ≤
      A * (volume (Metric.closedBall z r))⁻¹ := by
    rw [show (volume (convexFractionalChainBall c x rho n))⁻¹ =
      1 / volume (convexFractionalChainBall c x rho n) by simp]
    apply (ENNReal.div_le_iff hEpos.ne' hEtop).2
    calc
      1 = (volume (Metric.closedBall z r))⁻¹ *
          volume (Metric.closedBall z r) := by
        rw [ENNReal.inv_mul_cancel hBpos.ne' hBtop]
      _ ≤ (volume (Metric.closedBall z r))⁻¹ *
          (A * volume (convexFractionalChainBall c x rho n)) :=
        mul_le_mul_right hfactor _
      _ = (A * (volume (Metric.closedBall z r))⁻¹) *
          volume (convexFractionalChainBall c x rho n) := by ac_rfl
  calc
    (volume (convexFractionalChainBall c x rho n))⁻¹ *
        (volume.restrict (convexFractionalChainBall c x rho n)) S ≤
      (volume (convexFractionalChainBall c x rho n))⁻¹ *
        (volume.restrict (Metric.closedBall z r)) S :=
      mul_le_mul_right hrestr _
    _ ≤ (A * (volume (Metric.closedBall z r))⁻¹) *
        (volume.restrict (Metric.closedBall z r)) S :=
      by simpa only [mul_comm] using
        mul_le_mul_left hinv ((volume.restrict (Metric.closedBall z r)) S)
    _ = A * ((volume (Metric.closedBall z r))⁻¹ *
        (volume.restrict (Metric.closedBall z r)) S) := by ac_rfl

private theorem tendsto_chainRadius_zero {rho : ℝ} :
    Tendsto (fun n : ℕ => convexFractionalChainScale n * rho)
      atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  simpa only [convexFractionalChainScale, zero_mul] using hpow.mul_const rho

@[expose]
public def integrableZeroExtension
    (U : Set (Vec d)) (F : Vec d → Vec d) : Vec d → HilbertVec d :=
  fun y => U.indicator (HilbertVec.ofVec ∘ F) y

private theorem norm_integral_normalizedChainMeasure_le_closedBallAverage
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {c x : Vec d} {rho : ℝ}
    (hrho : 0 < rho) (hinner : euclideanBallAt c rho ⊆ U) (hxU : x ∈ U)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U)) (n : ℕ) :
    ‖∫ y, HilbertVec.ofVec (F y - F x)
        ∂normalizedChainMeasure c x rho n‖ ≤
      (ENNReal.ofReal ((Real.sqrt d) ^ d)).toReal *
        ⨍ y in Metric.closedBall (convexFractionalChainCenter c x n)
            (convexFractionalChainScale n * rho),
          ‖integrableZeroExtension U F y - integrableZeroExtension U F x‖ ∂volume := by
  let A : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt d) ^ d)
  let μn := normalizedChainMeasure c x rho n
  let νn := (volume
      (Metric.closedBall (convexFractionalChainCenter c x n)
        (convexFractionalChainScale n * rho)))⁻¹ •
    volume.restrict (Metric.closedBall (convexFractionalChainCenter c x n)
      (convexFractionalChainScale n * rho))
  have hμν : μn ≤ A • νn := by
    simpa only [μn, νn, A] using
      normalizedChainMeasure_le_closedBallAverage hd c x hrho n
  let E := convexFractionalChainBall c x rho n
  let g : Vec d → ℝ := E.indicator fun y => ‖HilbertVec.ofVec (F y - F x)‖
  let q : Vec d → ℝ := fun y =>
    ‖integrableZeroExtension U F y - integrableZeroExtension U F x‖
  let : IsProbabilityMeasure μn := by
    simpa only [μn] using normalizedChainMeasure_isProbability c x hrho n
  let : IsFiniteMeasure μn :=
    IsZeroOrProbabilityMeasure.toIsFiniteMeasure μn
  have hxcore : Integrable F
      (volume.restrict (convexFractionalChainBall c x rho n)) :=
    hF.mono_measure (Measure.restrict_mono_set volume
      (convexFractionalChainBall_subset hU hrho hinner hxU n))
  have hμint : Integrable (fun y => HilbertVec.ofVec (F y - F x)) μn := by
    exact ((HilbertVec.ofVecL d).integrable_comp
      (hxcore.smul_measure (ENNReal.inv_ne_top.mpr
        (volume_chainBall_pos_integrable c x hrho n).ne'))).sub
      (integrable_const (μ := μn) _)
  let : IsProbabilityMeasure νn := by
    refine ⟨?_⟩
    dsimp only [νn]
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (Metric.measure_closedBall_pos volume _
        (mul_pos (convexFractionalChainScale_pos n) hrho)).ne'
      measure_closedBall_lt_top.ne
  have hfint : Integrable (integrableZeroExtension U F) volume := by
    unfold integrableZeroExtension
    rw [integrable_indicator_iff hU.1.measurableSet]
    simpa only [Function.comp_apply] using!
      (HilbertVec.ofVecL d).integrable_comp hF
  have hqintν : Integrable q νn := by
    have hfν : Integrable (integrableZeroExtension U F) νn := by
      dsimp only [νn]
      exact (hfint.mono_measure volume.restrict_le_self).smul_measure
        (ENNReal.inv_ne_top.mpr
          (Metric.measure_closedBall_pos volume _
            (mul_pos (convexFractionalChainScale_pos n) hrho)).ne')
    exact (hfν.sub (integrable_const _)).norm
  have hAtop : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqintAν : Integrable q (A • νn) := hqintν.smul_measure hAtop
  have hgmeas : AEStronglyMeasurable g (A • νn) := by
    have hEmeas : MeasurableSet E := (isOpen_euclideanBallAt _ _).measurableSet
    have hFE : AEStronglyMeasurable
        (fun y => HilbertVec.ofVec (F y - F x)) (volume.restrict E) := by
      exact ((HilbertVec.ofVecL d).integrable_comp hxcore).aestronglyMeasurable.sub
        aestronglyMeasurable_const
    have hind : AEStronglyMeasurable
        (E.indicator fun y => HilbertVec.ofVec (F y - F x)) volume :=
      (aestronglyMeasurable_indicator_iff hEmeas).2 hFE
    have hac : A • νn ≪ volume := by
      exact Measure.smul_absolutelyContinuous.trans
        (Measure.smul_absolutelyContinuous.trans
          Measure.absolutelyContinuous_restrict)
    have hnorm := hind.norm.mono_ac hac
    convert hnorm using 1
    funext y
    change E.indicator (fun y => ‖HilbertVec.ofVec (F y - F x)‖) y =
      ‖E.indicator (fun y => HilbertVec.ofVec (F y - F x)) y‖
    by_cases hyE : y ∈ E
    · rw [Set.indicator_of_mem hyE, Set.indicator_of_mem hyE]
    · rw [Set.indicator_of_notMem hyE, Set.indicator_of_notMem hyE, norm_zero]
  have hgq : g ≤ᵐ[A • νn] q := by
    apply Eventually.of_forall
    intro y
    by_cases hyE : y ∈ E
    · have hyU : y ∈ U :=
        convexFractionalChainBall_subset hU hrho hinner hxU n hyE
      simp only [g, q, integrableZeroExtension, Set.indicator_of_mem hyE,
        Set.indicator_of_mem hxU, Set.indicator_of_mem hyU,
        Function.comp_apply]
      change ‖HilbertVec.ofVec (F y - F x)‖ ≤
        ‖HilbertVec.ofVec (F y - F x)‖
      exact le_rfl
    · simp only [g, Set.indicator_of_notMem hyE]
      exact norm_nonneg _
  have hgint : Integrable g (A • νn) :=
    hqintAν.mono' hgmeas (by
      filter_upwards [hgq] with y hy
      have hgnonneg : 0 ≤ g y := by
        by_cases hyE : y ∈ E
        · simp only [g, Set.indicator_of_mem hyE]
          exact norm_nonneg _
        · simp only [g, Set.indicator_of_notMem hyE]
          exact le_rfl
      rw [Real.norm_eq_abs, abs_of_nonneg hgnonneg]
      exact hy)
  have hgintegral : ∫ y, g y ∂μn ≤ ∫ y, g y ∂(A • νn) :=
    integral_mono_measure (μ := μn) (ν := A • νn) hμν
      (Eventually.of_forall fun y => by
        by_cases hyE : y ∈ E
        · simp only [g, Set.indicator_of_mem hyE]
          exact norm_nonneg _
        · simp only [g, Set.indicator_of_notMem hyE]
          exact le_rfl)
      hgint
  calc
    ‖∫ y, HilbertVec.ofVec (F y - F x) ∂μn‖ ≤
        ∫ y, ‖HilbertVec.ofVec (F y - F x)‖ ∂μn :=
      norm_integral_le_integral_norm _
    _ = ∫ y, g y ∂μn := by
      apply integral_congr_ae
      apply Measure.ae_smul_measure
      filter_upwards [ae_restrict_mem
        (isOpen_euclideanBallAt _ _).measurableSet] with y hy
      simp only [g, E, Set.indicator_of_mem hy]
    _ ≤ ∫ y, g y ∂(A • νn) := hgintegral
    _ ≤ ∫ y, q y ∂(A • νn) := integral_mono_ae hgint hqintAν hgq
    _ = A.toReal * ∫ y, q y ∂νn := by
      rw [integral_smul_measure]
      simp only [smul_eq_mul]
    _ = A.toReal *
        ⨍ y in Metric.closedBall (convexFractionalChainCenter c x n)
            (convexFractionalChainScale n * rho),
          ‖integrableZeroExtension U F y - integrableZeroExtension U F x‖ ∂volume := by
      rw [setAverage_eq']

private theorem tendsto_norm_integral_normalizedChainMeasure_zero
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {c x : Vec d} {rho : ℝ}
    (hrho : 0 < rho) (hinner : euclideanBallAt c rho ⊆ U) (hxU : x ∈ U)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U))
    (hclosed : Tendsto
      (fun n => ⨍ y in Metric.closedBall (convexFractionalChainCenter c x n)
          (convexFractionalChainScale n * rho),
        ‖integrableZeroExtension U F y - integrableZeroExtension U F x‖ ∂volume)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖∫ y, HilbertVec.ofVec (F y - F x)
      ∂normalizedChainMeasure c x rho n‖) atTop (𝓝 0) := by
  let A : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt d) ^ d)
  apply squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun n => by
      simpa only [A] using
        norm_integral_normalizedChainMeasure_le_closedBallAverage
          hd hU hrho hinner hxU hF n)
  simpa only [mul_zero] using tendsto_const_nhds.mul hclosed

private theorem integral_normalizedChainMeasure_sub_eq
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {c x : Vec d} {rho : ℝ} (hrho : 0 < rho)
    (hinner : euclideanBallAt c rho ⊆ U) (hxU : x ∈ U)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U)) (n : ℕ) :
    ∫ y, HilbertVec.ofVec (F y - F x)
        ∂normalizedChainMeasure c x rho n =
      HilbertVec.ofVec (convexFractionalChainMean c x rho F n) -
        HilbertVec.ofVec (F x) := by
  have hxcore : Integrable F
      (volume.restrict (convexFractionalChainBall c x rho n)) :=
    hF.mono_measure (Measure.restrict_mono_set volume
      (convexFractionalChainBall_subset hU hrho hinner hxU n))
  change ∫ y, HilbertVec.ofVec (F y) - HilbertVec.ofVec (F x)
      ∂normalizedChainMeasure c x rho n = _
  rw [integral_sub]
  · rw [integral_normalizedChainMeasure_eq_mean c x hrho n hxcore,
      integral_const]
    have := normalizedChainMeasure_isProbability c x hrho n
    simp only [probReal_univ, one_smul]
  · exact (HilbertVec.ofVecL d).integrable_comp
      (hxcore.smul_measure (ENNReal.inv_ne_top.mpr
        (volume_chainBall_pos_integrable c x hrho n).ne'))
  · have := normalizedChainMeasure_isProbability c x hrho n
    exact integrable_const _

private theorem tendsto_convexFractionalChainMean_of_closedBallAverage
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {c x : Vec d} {rho : ℝ}
    (hrho : 0 < rho) (hinner : euclideanBallAt c rho ⊆ U) (hxU : x ∈ U)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U))
    (hclosed : Tendsto
      (fun n => ⨍ y in Metric.closedBall (convexFractionalChainCenter c x n)
          (convexFractionalChainScale n * rho),
        ‖integrableZeroExtension U F y - integrableZeroExtension U F x‖ ∂volume)
      atTop (𝓝 0)) :
    Tendsto (fun n => HilbertVec.ofVec
      (convexFractionalChainMean c x rho F n)) atTop
      (𝓝 (HilbertVec.ofVec (F x))) := by
  have hnormzero : Tendsto
      (fun n => ‖∫ y, HilbertVec.ofVec (F y - F x)
          ∂normalizedChainMeasure c x rho n‖) atTop (𝓝 0) :=
    tendsto_norm_integral_normalizedChainMeasure_zero
      hd hU hrho hinner hxU hF hclosed
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [integral_normalizedChainMeasure_sub_eq
    hU hrho hinner hxU hF] using hnormzero

theorem ae_tendsto_convexFractionalChainMean_of_integrable
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {c : Vec d} {rho Rad : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad)
    {F : Vec d → Vec d} (hF : Integrable F (volume.restrict U)) :
    ∀ᵐ x ∂volume.restrict U,
      Tendsto (fun n => HilbertVec.ofVec
        (convexFractionalChainMean c x rho F n)) atTop
        (𝓝 (HilbertVec.ofVec (F x))) := by
  let f : Vec d → HilbertVec d := integrableZeroExtension U F
  have hfint : Integrable f volume := by
    dsimp only [f]
    unfold integrableZeroExtension
    rw [integrable_indicator_iff hU.1.measurableSet]
    simpa only [f, Function.comp_apply] using!
      (HilbertVec.ofVecL d).integrable_comp hF
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := volume) hfint.locallyIntegrable (Rad / rho)
  filter_upwards [ae_restrict_mem hU.1.measurableSet,
    ae_restrict_of_ae hdiff] with x hxU hxDiff
  have hdelta : Tendsto
      (fun n : ℕ => convexFractionalChainScale n * rho) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_chainRadius_zero, ?_⟩
    exact Eventually.of_forall fun n =>
      mul_pos (convexFractionalChainScale_pos n) hrho
  have hxmem : ∀ᶠ n : ℕ in atTop,
      x ∈ Metric.closedBall (convexFractionalChainCenter c x n)
        ((Rad / rho) * (convexFractionalChainScale n * rho)) := by
    apply Eventually.of_forall
    intro n
    rw [Metric.mem_closedBall]
    have hdist : dist x (convexFractionalChainCenter c x n) ≤
        euclideanDist x (convexFractionalChainCenter c x n) :=
      norm_le_sqrt_vecNormSq _
    have hxc : euclideanDist x c < Rad := by
      have hxball := houter hxU
      unfold euclideanDist euclideanNorm
      rw [← Real.sqrt_sq hRad.le,
        Real.sqrt_lt_sqrt_iff (vecNormSq_nonneg (x - c))]
      exact hxball
    calc
      dist x (convexFractionalChainCenter c x n) ≤
          euclideanDist x (convexFractionalChainCenter c x n) := hdist
      _ = convexFractionalChainScale n * euclideanDist x c :=
        euclideanDist_convexFractionalChainCenter c x n
      _ ≤ convexFractionalChainScale n * Rad :=
        mul_le_mul_of_nonneg_left hxc.le
          (convexFractionalChainScale_pos n).le
      _ = (Rad / rho) * (convexFractionalChainScale n * rho) := by
        field_simp
  have hclosed := hxDiff
    (fun n : ℕ => convexFractionalChainCenter c x n)
    (fun n : ℕ => convexFractionalChainScale n * rho) hdelta hxmem
  simpa only [f] using
    tendsto_convexFractionalChainMean_of_closedBallAverage
      hd hU hrho hinner hxU hF hclosed

private theorem edist_coreMean_le_fractionalRieszPotential_of_tendsto
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {c x : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U)
    {G : Vec d → Vec d} (hGmeas : Measurable G)
    (hGint : Integrable G (volume.restrict U))
    (hmean : Tendsto (fun n => HilbertVec.ofVec
      (convexFractionalChainMean c x rho G n)) atTop
      (𝓝 (HilbertVec.ofVec (G x))))
    (hsweight : 0 ≤ (d : ℝ) + 2 * s) (hsd : s < (d : ℝ)) :
    edist (HilbertVec.ofVec (volumeAverageVec (euclideanBallAt c rho) G))
        (HilbertVec.ofVec (G x)) ≤
      (convexFractionalChainJumpConstant d rho Rad s *
          convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s)) *
        ∫⁻ y in U, ENNReal.ofReal
          (euclideanDist x y ^ (s - (d : ℝ))) *
            fractionalGagliardoAmplitude U s G y ∂volume := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [← convexFractionalChainMean_zero c x rho G]
  apply (edist_convexFractionalChainMean_zero_le_tsum_jumps hmean).trans
  calc
    (∑' n : ℕ, edist
        (HilbertVec.ofVec (convexFractionalChainMean c x rho G n))
        (HilbertVec.ofVec (convexFractionalChainMean c x rho G (n + 1)))) ≤
        ∑' n : ℕ, convexFractionalChainJumpConstant d rho Rad s *
          (ENNReal.ofReal
            (convexFractionalChainScale n ^ (s - (d : ℝ))) *
            ∫⁻ z in convexFractionalChainBall c x rho n,
              fractionalGagliardoAmplitude U s G z ∂volume) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [mul_assoc] using
        edist_convexFractionalChainMean_succ_le_scale_amplitude
          hd hU hrho hRad.le hinner houter hx hGmeas hGint hsweight n
    _ = convexFractionalChainJumpConstant d rho Rad s *
        (∑' n : ℕ, ENNReal.ofReal
          (convexFractionalChainScale n ^ (s - (d : ℝ))) *
          ∫⁻ z in convexFractionalChainBall c x rho n,
            fractionalGagliardoAmplitude U s G z ∂volume) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ convexFractionalChainJumpConstant d rho Rad s *
        (convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s) *
          ∫⁻ y in U, ENNReal.ofReal
            (euclideanDist x y ^ (s - (d : ℝ))) *
              fractionalGagliardoAmplitude U s G y ∂volume) :=
      mul_le_mul_right (tsum_scaleWeight_mul_chainAmplitude_le_rieszPotential
        hd hU hrho hRad hinner houter hx hGmeas hsd) _
    _ = _ := by ac_rfl

private theorem boundaryWeighted_coreMean_pointwise_le_of_tendsto
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {c : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad)
    {G : Vec d → Vec d} (hGmeas : Measurable G)
    (hGint : Integrable G (volume.restrict U))
    (hs : 0 < s) (hsd : s < (d : ℝ)) {x : Vec d} (hx : x ∈ U)
    (hmean : Tendsto (fun n => HilbertVec.ofVec
      (convexFractionalChainMean c x rho G n)) atTop
      (𝓝 (HilbertVec.ofVec (G x)))) :
    euclideanBoundaryWeight U (2 * s) x *
        ENNReal.ofReal (vecNormSq
          (G x - volumeAverageVec (euclideanBallAt c rho) G)) ≤
      (convexFractionalChainJumpConstant d rho Rad s *
          convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s)) ^
        (2 : ℝ) *
        (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
          fractionalGagliardoAmplitude U s G y ∂volume) ^ (2 : ℝ) := by
  let K := convexFractionalChainJumpConstant d rho Rad s *
    convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s)
  let W := euclideanBoundaryWeight U s x
  let I := ∫⁻ y in U, ENNReal.ofReal
    (euclideanDist x y ^ (s - (d : ℝ))) *
      fractionalGagliardoAmplitude U s G y ∂volume
  have hdelta : 0 < euclideanBoundaryDistance U x :=
    euclideanBoundaryDistance_pos hd hU hx
  have hpoint := edist_coreMean_le_fractionalRieszPotential_of_tendsto
    hd hU hrho hRad hinner houter hx hGmeas hGint hmean
      (by have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d; positivity) hsd
  have hkernel :
      (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
          fractionalGagliardoAmplitude U s G y ∂volume) = W * I := by
    unfold fractionalBoundarySchurKernel W I
    have hWtop : euclideanBoundaryWeight U s x ≠ ∞ := by
      unfold euclideanBoundaryWeight
      exact ENNReal.ofReal_ne_top
    rw [← lintegral_const_mul' (μ := volume.restrict U)
      (euclideanBoundaryWeight U s x) _ hWtop]
    apply lintegral_congr
    intro y
    ac_rfl
  have hweighted : W * edist
      (HilbertVec.ofVec (volumeAverageVec (euclideanBallAt c rho) G))
      (HilbertVec.ofVec (G x)) ≤ K * (W * I) := by
    calc
      _ ≤ W * (K * I) := mul_le_mul_right hpoint W
      _ = _ := by ac_rfl
  have hsquared := ENNReal.rpow_le_rpow hweighted
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at hsquared
  rw [show ENNReal.ofReal (vecNormSq
      (G x - volumeAverageVec (euclideanBallAt c rho) G)) =
      edist (HilbertVec.ofVec (G x))
        (HilbertVec.ofVec (volumeAverageVec (euclideanBallAt c rho) G)) ^
          (2 : ℝ) by
    rw [edist_dist, dist_eq_norm, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply congrArg ENNReal.ofReal
    calc
      vecNormSq (G x - volumeAverageVec (euclideanBallAt c rho) G) =
          ‖HilbertVec.ofVec
            (G x - volumeAverageVec (euclideanBallAt c rho) G)‖ ^ 2 :=
        (HilbertVec.norm_sq_ofVec _).symm
      _ = ‖HilbertVec.ofVec (G x) -
          HilbertVec.ofVec (volumeAverageVec (euclideanBallAt c rho) G)‖ ^ 2 := by
        rfl]
  rw [show euclideanBoundaryWeight U (2 * s) x = W ^ (2 : ℝ) by
    rw [show 2 * s = s + s by ring]
    rw [← euclideanBoundaryWeight_mul hdelta]
    rw [ENNReal.rpow_two, pow_two]]
  rw [hkernel]
  rw [edist_comm (HilbertVec.ofVec (G x))]
  exact hsquared

private theorem convexFractionalChainJumpConstant_ne_top_integrable
    (hd : 1 ≤ d) {rho Rad s : ℝ} (hrho : 0 < rho) :
    convexFractionalChainJumpConstant d rho Rad s ≠ ∞ := by
  have hdreal : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hvE : convexHardyBallVolumeLower d rho ≠ 0 := by
    unfold convexHardyBallVolumeLower
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (pow_pos (mul_pos (by norm_num) (div_pos hrho hsqrt)) d)
  have hvF : convexHardyBallVolumeLower d ((1 / 2 : ℝ) * rho) ≠ 0 := by
    unfold convexHardyBallVolumeLower
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (pow_pos (mul_pos (by norm_num)
      (div_pos (mul_pos (by norm_num) hrho) hsqrt)) d)
  unfold convexFractionalChainJumpConstant convexFractionalChainLowerCoefficient
  simp only [convexFractionalChainScale, pow_zero, one_mul]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.inv_ne_top.mpr (by
          rw [show (1 / 2 : ℝ) * 1 * rho = (1 / 2 : ℝ) * rho by ring]
          exact hvF)))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
    (ENNReal.inv_ne_top.mpr hvE)

private theorem convexFractionalChainRieszConstant_ne_top_integrable
    (rho Rad a : ℝ) :
    convexFractionalChainRieszConstant rho Rad a ≠ ∞ := by
  unfold convexFractionalChainRieszConstant
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩

private theorem exists_euclideanBoundaryWeightedEnergyAround_coreMean_le_of_measurable
    (hd : 1 ≤ d) {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        ∀ (c : Vec d), euclideanBallAt c rho ⊆ U →
          U ⊆ euclideanBallAt c Rad →
          ∀ (G : Vec d → Vec d), Measurable G →
            Integrable G (volume.restrict U) →
            euclideanBoundaryWeightedEnergyAround U (2 * s) G
                (volumeAverageVec (euclideanBallAt c rho) G) ≤
              C * fracSeminormSq U s G := by
  obtain ⟨C, hCtop, hschur⟩ :=
    exists_euclideanBoundaryWeightedEnergyAround_le_of_pointwisePotential
      hd hrho hRad hs.1 hs.2 (by linarith only [hs.2])
  let K := convexFractionalChainJumpConstant d rho Rad s *
    convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s)
  let P := K ^ (2 : ℝ)
  have hKtop : K ≠ ∞ := ENNReal.mul_ne_top
    (convexFractionalChainJumpConstant_ne_top_integrable hd hrho)
    (convexFractionalChainRieszConstant_ne_top_integrable
      rho Rad ((d : ℝ) - s))
  have hPtop : P ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKtop
  refine ⟨P * C, ENNReal.mul_ne_top hPtop hCtop, ?_⟩
  intro U hU c hinner houter G hGmeas hGint
  have hsand : HasBallSandwich U rho Rad :=
    ⟨hrho, hRad.le, c, hinner, houter⟩
  apply hschur U hU hsand G hGmeas
    (volumeAverageVec (euclideanBallAt c rho) G) P hPtop
  have hmeans := ae_tendsto_convexFractionalChainMean_of_integrable
    hd hU hrho hRad hinner houter hGint
  filter_upwards [ae_restrict_mem hU.1.measurableSet, hmeans] with x hx hmean
  exact boundaryWeighted_coreMean_pointwise_le_of_tendsto
    hd hU hrho hRad hinner houter hGmeas hGint hs.1 (by
      have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
      exact hs.2.trans (lt_of_lt_of_le (by norm_num) hdreal)) hx hmean

private theorem convexHardyBallVolumeLower_ne_zero_integrable
    (hd : 1 ≤ d) {rho : ℝ} (hrho : 0 < rho) :
    convexHardyBallVolumeLower d rho ≠ 0 := by
  have hdreal : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hd
  unfold convexHardyBallVolumeLower
  rw [ne_eq, ENNReal.ofReal_eq_zero]
  exact not_le.mpr (pow_pos
    (mul_pos (by norm_num) (div_pos hrho (Real.sqrt_pos.2 hdreal))) d)

private theorem exists_euclideanBoundaryWeightedCenteredEnergy_le_fracSeminormSq_of_measurable
    (hd : 1 ≤ d) {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad →
        ∀ (G : Vec d → Vec d), Measurable G →
          Integrable G (volume.restrict U) →
          euclideanBoundaryWeightedCenteredEnergy U (2 * s) G ≤
            C * fracSeminormSq U s G := by
  obtain ⟨C, hCtop, hcore⟩ :=
    exists_euclideanBoundaryWeightedEnergyAround_coreMean_le_of_measurable
      hd hrho hRad hs
  let B : ℝ≥0∞ := 2 * (convexHardyBallVolumeLower d rho)⁻¹ *
    ENNReal.ofReal ((2 * Rad) ^ ((d : ℝ) + 2 * s))
  let M : ℝ≥0∞ := ENNReal.ofReal
    (((d : ℝ) / rho) ^ (2 * s) / (1 - 2 * s))
  have hBtop : B ≠ ∞ := by
    dsimp only [B]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.inv_ne_top.mpr
          (convexHardyBallVolumeLower_ne_zero_integrable hd hrho)))
      ENNReal.ofReal_ne_top
  have hMtop : M ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨2 * C + 2 * B * M,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hCtop,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hBtop) hMtop⟩, ?_⟩
  intro U hU hsand G hGmeas hGint
  have hmoment := euclideanBoundaryWeightMoment_two_mul_le hd hU hsand hs
  obtain ⟨_hrho, _hRad, c, hinner, houter⟩ := hsand
  have haround := hcore U hU c hinner houter G hGmeas hGint
  have hmean := ofReal_vecNormSq_coreMean_sub_domainMean_le
    hd hU hrho hRad hinner houter hGint hs.1.le
  have hmeanB : ENNReal.ofReal (vecNormSq
      (volumeAverageVec (euclideanBallAt c rho) G - volumeAverageVec U G)) ≤
      B * fracSeminormSq U s G := by
    simpa only [B] using hmean
  have hmomentM : euclideanBoundaryWeightMoment U (2 * s) ≤ M := by
    simpa only [M] using hmoment
  have hsplit := euclideanBoundaryWeightedCenteredEnergy_le_around_add_meanShift
    hGint (2 * s) (volumeAverageVec (euclideanBallAt c rho) G)
  apply hsplit.trans
  calc
    2 * euclideanBoundaryWeightedEnergyAround U (2 * s) G
          (volumeAverageVec (euclideanBallAt c rho) G) +
        2 * ENNReal.ofReal (vecNormSq
          (volumeAverageVec (euclideanBallAt c rho) G - volumeAverageVec U G)) *
            euclideanBoundaryWeightMoment U (2 * s) ≤
        2 * (C * fracSeminormSq U s G) +
          2 * (B * fracSeminormSq U s G) * M :=
      add_le_add (mul_le_mul_right haround 2)
        (by
          have hshift1 : 2 * ENNReal.ofReal (vecNormSq
                (volumeAverageVec (euclideanBallAt c rho) G -
                  volumeAverageVec U G)) *
                euclideanBoundaryWeightMoment U (2 * s) ≤
              2 * (B * fracSeminormSq U s G) *
                euclideanBoundaryWeightMoment U (2 * s) := by
            simpa only [mul_assoc, mul_comm, mul_left_comm] using
              mul_le_mul_right (mul_le_mul_right hmeanB 2)
                (euclideanBoundaryWeightMoment U (2 * s))
          have hshift2 : 2 * (B * fracSeminormSq U s G) *
                euclideanBoundaryWeightMoment U (2 * s) ≤
              2 * (B * fracSeminormSq U s G) * M :=
            mul_le_mul_right hmomentM (2 * (B * fracSeminormSq U s G))
          exact hshift1.trans hshift2)
    _ = (2 * C + 2 * B * M) * fracSeminormSq U s G := by ring

private theorem volumeAverageVec_congr_ae_integrable
    {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volume.restrict U] G) :
    volumeAverageVec U F = volumeAverageVec U G := by
  funext i
  unfold volumeAverageVec volumeAverage
  rw [integral_congr_ae]
  filter_upwards [hFG] with x hx
  rw [hx]

private theorem euclideanBoundaryWeightedCenteredEnergy_congr_ae_integrable
    {U : Set (Vec d)} {p : ℝ} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volume.restrict U] G) :
    euclideanBoundaryWeightedCenteredEnergy U p F =
      euclideanBoundaryWeightedCenteredEnergy U p G := by
  have hm := volumeAverageVec_congr_ae_integrable hFG
  unfold euclideanBoundaryWeightedCenteredEnergy eVolumeAverage
  apply congrArg (fun z : ℝ≥0∞ => z / volume U)
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx, hm]

private theorem fracSeminormSq_congr_ae_integrable
    {U : Set (Vec d)} {s : ℝ} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volume.restrict U] G) :
    fracSeminormSq U s F = fracSeminormSq U s G := by
  unfold fracSeminormSq eVolumeAverage
  apply congrArg (fun z : ℝ≥0∞ => z / volume U)
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  apply lintegral_congr_ae
  filter_upwards [hFG] with y hy
  rw [hx, hy]

/-- On every ball-sandwiched convex domain, the centered boundary-weighted
fractional energy of an integrable field is controlled by its Gagliardo
seminorm with a finite structural constant. -/
theorem exists_euclideanBoundaryWeightedCenteredEnergy_le_fracSeminormSq_of_integrable
    (hd : 1 ≤ d) {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad →
        ∀ (G : Vec d → Vec d), Integrable G (volume.restrict U) →
          euclideanBoundaryWeightedCenteredEnergy U (2 * s) G ≤
            C * fracSeminormSq U s G := by
  obtain ⟨C, hCtop, hcore⟩ :=
    exists_euclideanBoundaryWeightedCenteredEnergy_le_fracSeminormSq_of_measurable
      hd hrho hRad hs
  refine ⟨C, hCtop, ?_⟩
  intro U hU hsand G hG
  let Gm : Vec d → Vec d := hG.aestronglyMeasurable.mk G
  have hGmeas : Measurable Gm := hG.aestronglyMeasurable.measurable_mk
  have hGGm : G =ᵐ[volume.restrict U] Gm :=
    hG.aestronglyMeasurable.ae_eq_mk
  have hGmint : Integrable Gm (volume.restrict U) := hG.congr hGGm
  have hbound := hcore U hU hsand Gm hGmeas hGmint
  rw [← euclideanBoundaryWeightedCenteredEnergy_congr_ae_integrable hGGm,
    ← fracSeminormSq_congr_ae_integrable hGGm] at hbound
  exact hbound

end

end HighContrast
end HCPolySupport
