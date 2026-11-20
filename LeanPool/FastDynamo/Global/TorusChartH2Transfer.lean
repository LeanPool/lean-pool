/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartL2Operators
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Compactly supported `H²` transfer through the transverse torus chart

This file upgrades the bounded `L²` chart maps to a second-order
transfer on the subspace of whole-plane weak `H²` jets whose value and every
stored derivative vanish outside the canonical fundamental rectangle.

The analytic core is not postulated.  A fixed compactly supported Schwartz
cutoff, equal to one on the entire rectangle, turns every pulled-back torus
monomial into an admissible whole-plane weak-derivative test.  This proves the
periodic Fourier weak-derivative identities directly from the whole-plane
distributional identities.  Those identities then supply the weighted
Fourier certificate defining `TransverseC3H2`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped ENNReal LineDeriv SchwartzMap Topology

namespace TorusChartH2

open TorusChartL2
open ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate

/-! ## A Schwartz extension of every chart monomial -/

/-- A torus monomial pulled back to `WholePlane` through the raw coordinates. -/
def wholePlaneChartMonomial (frequency : TransverseFrequency)
    (x : WholePlane) : ℂ :=
  euclideanMonomial frequency (wholePlaneRawCoordinate x)

/-- The pulled-back chart monomial at `x` is the torus Fourier monomial evaluated at the quotient
image of `x`. -/
theorem wholePlaneChartMonomial_eq_mFourier
    (frequency : TransverseFrequency) (x : WholePlane) :
    wholePlaneChartMonomial frequency x =
      UnitAddTorus.mFourier frequency (wholePlaneTorusPoint x) := by
  exact euclideanMonomial_eq_mFourier frequency (wholePlaneRawCoordinate x)

/-- A pulled-back chart monomial is unimodular: `‖e^{2πi m·x}‖ = 1` everywhere on the plane. -/
@[simp] theorem norm_wholePlaneChartMonomial
    (frequency : TransverseFrequency) (x : WholePlane) :
    ‖wholePlaneChartMonomial frequency x‖ = 1 := by
  exact norm_euclideanMonomial frequency (wholePlaneRawCoordinate x)

/-- Pulled-back chart monomials are smooth, being products of exponentials of linear
coordinates. -/
theorem contDiff_wholePlaneChartMonomial
    (frequency : TransverseFrequency) :
    ContDiff ℝ (⊤ : ℕ∞) (wholePlaneChartMonomial frequency) := by
  unfold wholePlaneChartMonomial euclideanMonomial wholePlaneRawCoordinate
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦
    Complex.exp (2 * Real.pi * Complex.I * (frequency 0 : ℂ) *
      Complex.ofRealCLM (x.ofLp 0)) *
    Complex.exp (2 * Real.pi * Complex.I * (frequency 1 : ℂ) *
      Complex.ofRealCLM (x.ofLp 1)))
  fun_prop

/-- A radius-six bump has inner radius two, large enough to contain the
whole `(0,1]²` fundamental rectangle strictly in its constant core. -/
def chartSchwartzCutoffReal (x : WholePlane) : ℝ :=
  ParametrixExplicitCutoff.outputCutoff 0 6 (by norm_num) x

/-- Complex coercion of the fixed real Schwartz chart cutoff. -/
def chartSchwartzCutoffComplex (x : WholePlane) : ℂ :=
  (chartSchwartzCutoffReal x : ℂ)

/-- The complexified fixed chart cutoff is smooth. -/
theorem chartSchwartzCutoffComplex_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) chartSchwartzCutoffComplex := by
  exact Complex.ofRealCLM.contDiff.comp
    (ParametrixExplicitCutoff.outputCutoff_contDiff 0 6 (by norm_num))

/-- The complexified fixed chart cutoff has compact support, being built from a radius-six
bump. -/
theorem chartSchwartzCutoffComplex_hasCompactSupport :
    HasCompactSupport chartSchwartzCutoffComplex := by
  exact (ParametrixExplicitCutoff.outputCutoff_hasCompactSupport
    0 6 (by norm_num)).comp_left rfl

/-- The ordinary compactly supported product underlying the chart test. -/
def chartMonomialTestFunction (frequency : TransverseFrequency)
    (x : WholePlane) : ℂ :=
  chartSchwartzCutoffComplex x * wholePlaneChartMonomial frequency x

/-- The cutoff-times-monomial test function has compact support, inherited from the cutoff. -/
theorem chartMonomialTestFunction_hasCompactSupport
    (frequency : TransverseFrequency) :
    HasCompactSupport (chartMonomialTestFunction frequency) := by
  change HasCompactSupport
    (chartSchwartzCutoffComplex * wholePlaneChartMonomial frequency)
  exact chartSchwartzCutoffComplex_hasCompactSupport.mul_right

/-- The cutoff-times-monomial test function is smooth, being a product of two smooth
functions. -/
theorem chartMonomialTestFunction_contDiff
    (frequency : TransverseFrequency) :
    ContDiff ℝ (⊤ : ℕ∞) (chartMonomialTestFunction frequency) := by
  exact chartSchwartzCutoffComplex_contDiff.mul
    (contDiff_wholePlaneChartMonomial frequency)

/-- The compactly supported Schwartz test agreeing with a specified torus
monomial throughout the chart. -/
def chartMonomialSchwartz (frequency : TransverseFrequency) :
    SchwartzMap WholePlane ℂ :=
  (chartMonomialTestFunction_hasCompactSupport frequency).toSchwartzMap
    (chartMonomialTestFunction_contDiff frequency)

/-- The Schwartz chart test evaluates as the product of the fixed cutoff and the pulled-back
monomial. -/
@[simp] theorem chartMonomialSchwartz_apply
    (frequency : TransverseFrequency) (x : WholePlane) :
    chartMonomialSchwartz frequency x =
      chartSchwartzCutoffComplex x * wholePlaneChartMonomial frequency x :=
  rfl

/-- Every point of the fundamental rectangle `(0,1]²` has Euclidean norm less than `2`, so the
rectangle sits strictly inside the constant core of the radius-six cutoff. -/
theorem norm_lt_two_of_mem_wholePlaneFundamentalBox
    {x : WholePlane} (hx : x ∈ wholePlaneFundamentalBox) :
    ‖x‖ < 2 := by
  have hx0 := hx (0 : Fin 2)
  have hx1 := hx (1 : Fin 2)
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
  have hx0' : 0 < x.ofLp 0 ∧ x.ofLp 0 ≤ 1 := by
    simpa [wholePlaneRawCoordinate] using hx0
  have hx1' : 0 < x.ofLp 1 ∧ x.ofLp 1 ≤ 1 := by
    simpa [wholePlaneRawCoordinate] using hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hx0'.1.le, abs_of_nonneg hx1'.1.le]
  nlinarith [sq_nonneg (x.ofLp 0 - 1), sq_nonneg (x.ofLp 1 - 1)]

/-- The fixed chart cutoff equals `1` at every point of the fundamental rectangle, its constant
core having radius `2`. -/
theorem chartSchwartzCutoff_eq_one_of_mem_fundamentalBox
    {x : WholePlane} (hx : x ∈ wholePlaneFundamentalBox) :
    chartSchwartzCutoffComplex x = 1 := by
  have hnorm := (norm_lt_two_of_mem_wholePlaneFundamentalBox hx).le
  have hr : (6 : ℝ) / 3 = 2 := by norm_num
  have hdist : dist x (0 : WholePlane) ≤ (6 : ℝ) / 3 := by
    rw [hr, dist_zero_right]
    exact hnorm
  have hcut := ParametrixExplicitCutoff.outputCutoff_eq_one_of_dist_le
    0 6 (by norm_num) hdist
  change ((ParametrixExplicitCutoff.outputCutoff 0 6 (by norm_num) x : ℝ) : ℂ) = 1
  rw [hcut]
  norm_num

/-- On the fundamental rectangle the Schwartz chart test coincides with the pulled-back torus
monomial, the cutoff being `1` there. -/
theorem chartMonomialSchwartz_eq_of_mem_fundamentalBox
    (frequency : TransverseFrequency) {x : WholePlane}
    (hx : x ∈ wholePlaneFundamentalBox) :
    chartMonomialSchwartz frequency x =
      wholePlaneChartMonomial frequency x := by
  simp [chartSchwartzCutoff_eq_one_of_mem_fundamentalBox hx]

/-- Directional derivative of a pulled-back chart monomial: `∂_j e^{2πi m·x} = 2πi m_j e^{2πi m·x}`
at every point of the plane. -/
theorem wholePlaneChartMonomial_hasLineDerivAt
    (frequency : TransverseFrequency) (j : Fin 2) (x : WholePlane) :
    HasLineDerivAt ℝ (wholePlaneChartMonomial frequency)
      ((2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        wholePlaneChartMonomial frequency x)
      x (wholePlaneBasis j) := by
  have h := euclideanMonomial_hasLineDerivAt frequency j
    (wholePlaneRawCoordinate x)
  unfold HasLineDerivAt at h ⊢
  simpa [wholePlaneChartMonomial, wholePlaneRawCoordinate,
    wholePlaneBasis] using h

/-- The Schwartz chart test agrees with the pulled-back monomial on a whole neighbourhood of any
point of the fundamental rectangle, so their derivatives there agree as well. -/
theorem chartMonomialSchwartz_eventuallyEq
    (frequency : TransverseFrequency) {x : WholePlane}
    (hx : x ∈ wholePlaneFundamentalBox) :
    (chartMonomialSchwartz frequency : WholePlane → ℂ) =ᶠ[𝓝 x]
      wholePlaneChartMonomial frequency := by
  have hball : x ∈ Metric.ball (0 : WholePlane) (6 / 3 : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    norm_num
    exact norm_lt_two_of_mem_wholePlaneFundamentalBox hx
  have hcut := (ParametrixExplicitCutoff.outputBump
    (0 : WholePlane) 6 (by norm_num)).eventuallyEq_one_of_mem_ball hball
  filter_upwards [hcut] with y hy
  change chartSchwartzCutoffComplex y * wholePlaneChartMonomial frequency y =
    wholePlaneChartMonomial frequency y
  change ((ParametrixExplicitCutoff.outputCutoff 0 6 (by norm_num) y : ℝ) : ℂ) *
      wholePlaneChartMonomial frequency y = _
  have hy' : ParametrixExplicitCutoff.outputCutoff 0 6 (by norm_num) y = 1 := by
    simpa [ParametrixExplicitCutoff.outputCutoff] using hy
  rw [hy']
  simp

/-- At a point of the fundamental rectangle the Schwartz chart test has the monomial's directional
derivative `2πi m_j e^{2πi m·x}`. -/
theorem chartMonomialSchwartz_hasLineDerivAt_of_mem_fundamentalBox
    (frequency : TransverseFrequency) (j : Fin 2) {x : WholePlane}
    (hx : x ∈ wholePlaneFundamentalBox) :
    HasLineDerivAt ℝ (chartMonomialSchwartz frequency : WholePlane → ℂ)
      ((2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        wholePlaneChartMonomial frequency x)
      x (wholePlaneBasis j) := by
  exact (wholePlaneChartMonomial_hasLineDerivAt frequency j x).congr_of_eventuallyEq
    (chartMonomialSchwartz_eventuallyEq frequency hx)

/-- The Schwartz-map directional derivative of the chart test, evaluated on the fundamental
rectangle, equals `2πi m_j` times the pulled-back monomial.  This is what turns whole-plane
distributional identities into the periodic Fourier weak-derivative identities. -/
theorem lineDeriv_chartMonomialSchwartz_of_mem_fundamentalBox
    (frequency : TransverseFrequency) (j : Fin 2) {x : WholePlane}
    (hx : x ∈ wholePlaneFundamentalBox) :
    (∂_{wholePlaneBasis j} (chartMonomialSchwartz frequency)) x =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        wholePlaneChartMonomial frequency x := by
  rw [SchwartzMap.lineDerivOp_apply]
  exact (chartMonomialSchwartz_hasLineDerivAt_of_mem_fundamentalBox
    frequency j hx).lineDeriv

/-! ## From whole-plane distributional derivatives to integral identities -/

/-- The distributional and Schwartz-test formulations of a whole-plane
weak derivative agree in the direction needed for chart transfer. -/
theorem wholePlaneIntegralWeakDerivative_of_distributionIdentity
    {f df : WholePlaneC3L2} {j : Fin 2}
    (h : ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered C3 f) =
      wholePlaneL2ToTempered C3 df) :
    HasWholePlaneIntegralWeakDerivative f df j := by
  intro φ
  have hφ := congrArg (fun T : TemperedDistribution WholePlane C3 ↦ T φ) h
  simpa only [TemperedDistribution.lineDerivOp_apply_apply,
    wholePlaneL2ToTempered_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply] using hφ

/-! ## Exact Fourier coefficients of chart restriction -/

/-- Restricting a whole-plane `L²` field to the torus computes its Fourier
coefficient by integrating the pulled-back monomial over the fundamental
rectangle.  No support hypothesis is used here. -/
theorem transverseCoeffCLM_wholePlaneToTorusL2_eq_setIntegral
    (f : WholePlaneC3L2) (frequency : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM frequency i (wholePlaneToTorusL2 f) =
      ∫ x in wholePlaneFundamentalBox,
        wholePlaneChartMonomial (-frequency) x * (f x) i ∂volume := by
  rw [← transverseMonomialComponentPairing_eq_coeff,
    transverseMonomialComponentPairing_eq_integral]
  let g : WholePlane → ℂ := fun x ↦
    wholePlaneChartMonomial (-frequency) x * (f x) i
  have hmono : AEStronglyMeasurable
      (wholePlaneChartMonomial (-frequency)) volume :=
    (contDiff_wholePlaneChartMonomial (-frequency)).continuous.aestronglyMeasurable
  have hcoord : AEStronglyMeasurable (fun x : WholePlane ↦ (f x) i) volume := by
    exact (Lp.aestronglyMeasurable (wholePlaneCoordL2 i f)).congr
      ((EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f)
  have hg : AEStronglyMeasurable g
      (volume.restrict wholePlaneFundamentalBox) :=
    (hmono.mul hcoord).mono_measure Measure.restrict_le_self
  have hgmap : AEStronglyMeasurable g
      (Measure.map torusWholePlaneRepresentative transverseMeasure) := by
    rw [measurePreserving_torusWholePlaneRepresentative.map_eq]
    exact hg
  have hchange := MeasureTheory.integral_map
    measurePreserving_torusWholePlaneRepresentative.measurable.aemeasurable hgmap
  rw [measurePreserving_torusWholePlaneRepresentative.map_eq] at hchange
  calc
    ∫ q : TransverseTorus,
        starRingEnd ℂ ((transverseMonomialL2 frequency) q) *
          (transverseCoordL2 i (wholePlaneToTorusL2 f)) q
          ∂transverseMeasure =
        ∫ q : TransverseTorus,
          g (torusWholePlaneRepresentative q) ∂transverseMeasure := by
      apply integral_congr_ae
      filter_upwards [transverseMonomialL2_coe_ae frequency,
        (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
          (wholePlaneToTorusL2 f),
        wholePlaneToTorusL2_coe_ae f] with q hmon hproj hchart
      change ((transverseCoordL2 i (wholePlaneToTorusL2 f) :
        TransverseScalarL2) : TransverseTorus → ℂ) q = _ at hproj
      rw [hmon, hproj, hchart]
      rw [← UnitAddTorus.mFourier_neg]
      change UnitAddTorus.mFourier (-frequency) q * (f _) i =
        wholePlaneChartMonomial (-frequency) _ * (f _) i
      rw [wholePlaneChartMonomial_eq_mFourier,
        wholePlaneTorusPoint_torusWholePlaneRepresentative]
    _ = ∫ x in wholePlaneFundamentalBox, g x ∂volume := hchange.symm
    _ = ∫ x in wholePlaneFundamentalBox,
        wholePlaneChartMonomial (-frequency) x * (f x) i ∂volume := rfl

/-- For a field supported in the chart, the same Fourier coefficient is a
whole-plane integral. -/
theorem transverseCoeffCLM_wholePlaneToTorusL2_eq_integral
    {f : WholePlaneC3L2}
    (hf : IsSupportedInWholePlaneFundamentalBox f)
    (frequency : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM frequency i (wholePlaneToTorusL2 f) =
      ∫ x : WholePlane,
        wholePlaneChartMonomial (-frequency) x * (f x) i ∂volume := by
  rw [transverseCoeffCLM_wholePlaneToTorusL2_eq_setIntegral]
  apply (integral_indicator
    measurableSet_wholePlaneFundamentalBox).symm.trans
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  by_cases hbox : x ∈ wholePlaneFundamentalBox
  · rw [Set.indicator_of_mem hbox]
  · rw [Set.indicator_of_notMem hbox, hx hbox]
    simp

/-- Each coordinate of a Schwartz-weighted vector integral is the corresponding
scalar Schwartz-weighted integral. -/
theorem integral_schwartz_smul_l2_apply
    (f : WholePlaneC3L2) (phi : SchwartzMap WholePlane ℂ) (i : Fin 3) :
    (∫ x : WholePlane, phi x • (f x : C3) ∂volume) i =
      ∫ x : WholePlane, phi x * (f x) i ∂volume := by
  have hint : Integrable
      (fun x : WholePlane ↦ phi x • (f x : C3)) volume :=
    memLp_one_iff_integrable.mp <|
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] C3 →L[ℂ] C3).memLp_of_bilin
        1 (phi.memLp 2 volume) (Lp.memLp f)
  change (EuclideanSpace.proj i)
      (∫ x : WholePlane, phi x • (f x : C3) ∂volume) = _
  calc
    (EuclideanSpace.proj i)
        (∫ x : WholePlane, phi x • (f x : C3) ∂volume) =
        ∫ x : WholePlane,
          (EuclideanSpace.proj i) (phi x • (f x : C3)) ∂volume :=
      ((EuclideanSpace.proj i).integral_comp_comm hint).symm
    _ = ∫ x : WholePlane, phi x * (f x) i ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      simp

/-- Whole-plane weak integration by parts against the compact Schwartz
extension of a torus character.  The support of both representatives removes
every contribution from the cutoff annulus. -/
theorem integral_chartMonomial_mul_weakDerivative
    {f df : WholePlaneC3L2} {j : Fin 2}
    (hweak : HasWholePlaneIntegralWeakDerivative f df j)
    (hf : IsSupportedInWholePlaneFundamentalBox f)
    (hdf : IsSupportedInWholePlaneFundamentalBox df)
    (frequency : TransverseFrequency) (i : Fin 3) :
    (∫ x : WholePlane,
        wholePlaneChartMonomial (-frequency) x * (df x) i ∂volume) =
      transverseFourierDerivMultiplier j frequency *
        ∫ x : WholePlane,
          wholePlaneChartMonomial (-frequency) x * (f x) i ∂volume := by
  have hibp := hweak (chartMonomialSchwartz (-frequency))
  have hibpCoord := congrArg (fun z : C3 ↦ z i) hibp
  rw [integral_schwartz_smul_l2_apply,
    integral_schwartz_smul_l2_apply] at hibpCoord
  calc
    (∫ x : WholePlane,
        wholePlaneChartMonomial (-frequency) x * (df x) i ∂volume) =
        ∫ x : WholePlane,
          chartMonomialSchwartz (-frequency) x * (df x) i ∂volume := by
      apply integral_congr_ae
      filter_upwards [hdf] with x hx
      by_cases hbox : x ∈ wholePlaneFundamentalBox
      · rw [chartMonomialSchwartz_eq_of_mem_fundamentalBox _ hbox]
      · rw [hx hbox]
        simp
    _ = ∫ x : WholePlane,
        ((-∂_{wholePlaneBasis j} (chartMonomialSchwartz (-frequency))) x) *
          (f x) i ∂volume := hibpCoord.symm
    _ = ∫ x : WholePlane,
        transverseFourierDerivMultiplier j frequency *
          (wholePlaneChartMonomial (-frequency) x * (f x) i) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      by_cases hbox : x ∈ wholePlaneFundamentalBox
      · change -((∂_{wholePlaneBasis j}
            (chartMonomialSchwartz (-frequency))) x) * (f x) i = _
        rw [lineDeriv_chartMonomialSchwartz_of_mem_fundamentalBox
          (-frequency) j hbox]
        simp [transverseFourierDerivMultiplier]
        ring
      · rw [hx hbox]
        simp
    _ = transverseFourierDerivMultiplier j frequency *
        ∫ x : WholePlane,
          wholePlaneChartMonomial (-frequency) x * (f x) i ∂volume := by
      rw [integral_const_mul]

/-- Quotient descent of a compactly chart-supported whole-plane weak
derivative.  This is derived from Schwartz integration by parts, rather than
accepted as a Fourier certificate. -/
theorem hasTransverseFourierDerivative_wholePlaneToTorusL2
    {f df : WholePlaneC3L2} {j : Fin 2}
    (hweak : HasWholePlaneIntegralWeakDerivative f df j)
    (hf : IsSupportedInWholePlaneFundamentalBox f)
    (hdf : IsSupportedInWholePlaneFundamentalBox df) :
    HasTransverseFourierDerivative j
      (wholePlaneToTorusL2 f) (wholePlaneToTorusL2 df) := by
  intro frequency i
  rw [transverseCoeffCLM_wholePlaneToTorusL2_eq_integral hdf,
    transverseCoeffCLM_wholePlaneToTorusL2_eq_integral hf]
  simpa [transverseFourierDerivMultiplier] using
    integral_chartMonomial_mul_weakDerivative hweak hf hdf frequency i

/-! ## The compact-chart whole-plane `H²` source graph -/

/-- The zero field is supported in the whole-plane fundamental box. -/
private theorem supportedInFundamentalBox_zero :
    IsSupportedInWholePlaneFundamentalBox (0 : WholePlaneC3L2) := by
  filter_upwards [Lp.coeFn_zero C3 2 (volume : Measure WholePlane)] with x hx
  intro _
  exact hx

/-- Fields supported in the whole-plane fundamental box are closed under
addition. -/
theorem supportedInFundamentalBox_add
    {f g : WholePlaneC3L2}
    (hf : IsSupportedInWholePlaneFundamentalBox f)
    (hg : IsSupportedInWholePlaneFundamentalBox g) :
    IsSupportedInWholePlaneFundamentalBox (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx hadd hbox
  rw [hadd]
  change f x + g x = 0
  rw [hfx hbox, hgx hbox, add_zero]

/-- Fields supported in the whole-plane fundamental box are closed under scalar
multiplication. -/
theorem supportedInFundamentalBox_smul
    (c : ℂ) {f : WholePlaneC3L2}
    (hf : IsSupportedInWholePlaneFundamentalBox f) :
    IsSupportedInWholePlaneFundamentalBox (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hfx hsmul hbox
  rw [hsmul]
  change c • f x = 0
  rw [hfx hbox, smul_zero]

/-- Whole-plane `H²` jets for which the value, both first derivatives, and
all four ordered second derivatives vanish a.e. outside the chart.  Requiring
support of the complete jet is what excludes boundary delta terms after
quotient descent. -/
def chartSupportedWholePlaneH2Submodule : Submodule ℂ WholePlaneC3H2 where
  carrier := {u | ∀ q : WholePlaneJet2Index,
    IsSupportedInWholePlaneFundamentalBox (u.1 q)}
  zero_mem' := by
    intro q
    change IsSupportedInWholePlaneFundamentalBox (0 : WholePlaneC3L2)
    exact supportedInFundamentalBox_zero
  add_mem' := by
    intro u v hu hv q
    change IsSupportedInWholePlaneFundamentalBox (u.1 q + v.1 q)
    exact supportedInFundamentalBox_add (hu q) (hv q)
  smul_mem' := by
    intro c u hu q
    change IsSupportedInWholePlaneFundamentalBox (c • u.1 q)
    exact supportedInFundamentalBox_smul c (hu q)

/-- The normed source space for the bounded chart transfer, carrying the
inherited whole-plane `H²` graph norm. -/
abbrev ChartSupportedWholePlaneC3H2 := chartSupportedWholePlaneH2Submodule

/-- The value of a chart-supported whole-plane `H²` jet vanishes a.e. outside the fundamental
box. -/
theorem chartSupported_value
    (u : ChartSupportedWholePlaneC3H2) :
    IsSupportedInWholePlaneFundamentalBox
      (wholePlaneH2Embedding C3 u.1) := by
  exact u.2 (Sum.inl none)

/-- Each stored first derivative of a chart-supported jet vanishes a.e. outside the fundamental
box. -/
theorem chartSupported_firstDerivative
    (u : ChartSupportedWholePlaneC3H2) (j : Fin 2) :
    IsSupportedInWholePlaneFundamentalBox
      (wholePlaneH2FirstDerivative C3 j u.1) := by
  exact u.2 (Sum.inl (some j))

/-- Each stored ordered second derivative of a chart-supported jet vanishes a.e. outside the
fundamental box. -/
theorem chartSupported_secondDerivative
    (u : ChartSupportedWholePlaneC3H2) (j k : Fin 2) :
    IsSupportedInWholePlaneFundamentalBox
      (wholePlaneH2SecondDerivative C3 j k u.1) := by
  exact u.2 (Sum.inr (j, k))

/-- Torus value of a supported whole-plane `H²` jet. -/
def chartValueL2 : ChartSupportedWholePlaneC3H2 →L[ℂ] TransverseC3L2 :=
  wholePlaneToTorusL2.comp <|
    (wholePlaneH2Embedding C3).comp chartSupportedWholePlaneH2Submodule.subtypeL

/-- Torus descent of the `j`-th stored whole-plane first derivative. -/
def chartFirstDerivativeL2 (j : Fin 2) :
    ChartSupportedWholePlaneC3H2 →L[ℂ] TransverseC3L2 :=
  wholePlaneToTorusL2.comp <|
    (wholePlaneH2FirstDerivative C3 j).comp
      chartSupportedWholePlaneH2Submodule.subtypeL

/-- Torus descent of the ordered stored derivative `∂_k ∂_j`. -/
def chartSecondDerivativeL2 (j k : Fin 2) :
    ChartSupportedWholePlaneC3H2 →L[ℂ] TransverseC3L2 :=
  wholePlaneToTorusL2.comp <|
    (wholePlaneH2SecondDerivative C3 j k).comp
      chartSupportedWholePlaneH2Submodule.subtypeL

/-- The torus value of a chart-supported jet is the restriction of its whole-plane value. -/
@[simp] theorem chartValueL2_apply (u : ChartSupportedWholePlaneC3H2) :
    chartValueL2 u = wholePlaneToTorusL2 (wholePlaneH2Embedding C3 u.1) :=
  rfl

/-- The torus descent of the `j`-th stored derivative is the restriction of that whole-plane
derivative. -/
@[simp] theorem chartFirstDerivativeL2_apply
    (j : Fin 2) (u : ChartSupportedWholePlaneC3H2) :
    chartFirstDerivativeL2 j u =
      wholePlaneToTorusL2 (wholePlaneH2FirstDerivative C3 j u.1) :=
  rfl

/-- The torus descent of the ordered stored derivative `∂_k ∂_j` is the restriction of that
whole-plane derivative. -/
@[simp] theorem chartSecondDerivativeL2_apply
    (j k : Fin 2) (u : ChartSupportedWholePlaneC3H2) :
    chartSecondDerivativeL2 j k u =
      wholePlaneToTorusL2 (wholePlaneH2SecondDerivative C3 j k u.1) :=
  rfl

/-! ## First, ordered-second, and Laplacian weak identities on the torus -/

/-- The descended first derivative is the periodic Fourier weak derivative of the
descended value; the chart support removes the boundary terms that zero extension would otherwise
create. -/
theorem chartFirstDerivative_hasFourierDerivative
    (u : ChartSupportedWholePlaneC3H2) (j : Fin 2) :
    HasTransverseFourierDerivative j
      (chartValueL2 u) (chartFirstDerivativeL2 j u) := by
  exact hasTransverseFourierDerivative_wholePlaneToTorusL2
    (wholePlaneIntegralWeakDerivative_of_distributionIdentity
      (wholePlaneH2_firstDerivative_distribution C3 u.1 j))
    (chartSupported_value u) (chartSupported_firstDerivative u j)

/-- The descended ordered second derivative is the periodic Fourier weak derivative, in
direction `k`, of the descended first derivative in direction `j`. -/
theorem chartSecondDerivative_hasFourierDerivative
    (u : ChartSupportedWholePlaneC3H2) (j k : Fin 2) :
    HasTransverseFourierDerivative k
      (chartFirstDerivativeL2 j u) (chartSecondDerivativeL2 j k u) := by
  exact hasTransverseFourierDerivative_wholePlaneToTorusL2
    (wholePlaneIntegralWeakDerivative_of_distributionIdentity
      (wholePlaneH2_secondDerivative_distribution C3 u.1 j k))
    (chartSupported_firstDerivative u j)
    (chartSupported_secondDerivative u j k)

/-- Descent of the whole-plane weak Laplacian, expressed as the sum of the
two diagonal stored second derivatives. -/
def chartLaplacianL2 :
    ChartSupportedWholePlaneC3H2 →L[ℂ] TransverseC3L2 :=
  ∑ j : Fin 2, chartSecondDerivativeL2 j j

/-- The descended Laplacian written out as the sum of the two diagonal descended second
derivatives. -/
theorem chartLaplacianL2_apply (u : ChartSupportedWholePlaneC3H2) :
    chartLaplacianL2 u =
      chartSecondDerivativeL2 0 0 u + chartSecondDerivativeL2 1 1 u := by
  simp [chartLaplacianL2, Fin.sum_univ_two]

/-- The descended Laplacian is the torus restriction of the whole-plane weak Laplacian of the
jet. -/
theorem chartLaplacianL2_eq_wholePlaneLaplacian
    (u : ChartSupportedWholePlaneC3H2) :
    chartLaplacianL2 u =
      wholePlaneToTorusL2 (wholePlaneLaplacian C3 u.1) := by
  rw [chartLaplacianL2_apply, wholePlaneLaplacian_apply, map_add]
  rfl

/-- The descended diagonal sum is the Fourier weak Laplacian of the
descended value. -/
theorem chartLaplacian_hasFourierLaplacian
    (u : ChartSupportedWholePlaneC3H2) :
    HasTransverseFourierLaplacian (chartValueL2 u) (chartLaplacianL2 u) := by
  intro frequency i
  have h00 := chartSecondDerivative_hasFourierDerivative u
    (0 : Fin 2) (0 : Fin 2) frequency i
  have h11 := chartSecondDerivative_hasFourierDerivative u
    (1 : Fin 2) (1 : Fin 2) frequency i
  have h0 := chartFirstDerivative_hasFourierDerivative u
    (0 : Fin 2) frequency i
  have h1 := chartFirstDerivative_hasFourierDerivative u
    (1 : Fin 2) frequency i
  simp only [chartLaplacianL2_apply, map_add, h00, h11, h0, h1]
  unfold transverseFrequencyEnergy
  simp only [Fin.sum_univ_two]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Closing the periodic `H²` Fourier graph -/

/-- Coordinatewise Fourier analysis of a transverse `C3` field. -/
def chartTransverseC3FourierAnalysis :
    TransverseC3L2 →L[ℂ] WeightedTransverseC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦
      transverseScalarFourierAnalysis.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (transverseCoordL2 i))

/-- Coordinatewise Fourier analysis returns the usual coefficients: the `frequency` entry of
component `i` is `transverseCoeffCLM frequency i`. -/
theorem chartTransverseC3FourierAnalysis_coeff
    (f : TransverseC3L2) (frequency : TransverseFrequency) (i : Fin 3) :
    (chartTransverseC3FourierAnalysis f i) frequency =
      transverseCoeffCLM frequency i f :=
  rfl

/-- The weighted graph certificate is Fourier analysis of `(1 - Δ)u`. -/
def chartWeightedCertificate :
    ChartSupportedWholePlaneC3H2 →L[ℂ] WeightedTransverseC3Coeffs :=
  chartTransverseC3FourierAnalysis.comp
    (chartValueL2 - chartLaplacianL2)

/-- Ambient periodic `H²` graph map before restricting its range. -/
def chartH2GraphMap : ChartSupportedWholePlaneC3H2 →L[ℂ]
    (TransverseC3L2 × WeightedTransverseC3Coeffs) :=
  chartValueL2.prod chartWeightedCertificate

/-- The pair (value, weighted certificate) built from a chart-supported jet satisfies the
weighted-coefficient relation `\hat{((1-Δ)u)} = transverseH2Weight · \hat u`, hence lies in the
periodic Fourier `H²` graph submodule. -/
theorem chartH2GraphMap_mem (u : ChartSupportedWholePlaneC3H2) :
    chartH2GraphMap u ∈ transverseH2Submodule := by
  rw [mem_transverseH2Submodule_iff]
  intro frequency i
  change (chartWeightedCertificate u i) frequency =
    (transverseH2Weight frequency : ℂ) *
      transverseCoeffCLM frequency i (chartValueL2 u)
  rw [show chartWeightedCertificate u =
      chartTransverseC3FourierAnalysis
        (chartValueL2 u - chartLaplacianL2 u) from rfl,
    chartTransverseC3FourierAnalysis_coeff, map_sub,
    chartLaplacian_hasFourierLaplacian u frequency i]
  unfold transverseH2Weight
  push_cast
  ring

/-- Bounded descent of a complete, chart-supported whole-plane `H²` jet to
the repository's periodic Fourier-graph `H²` space. -/
def wholePlaneChartToTransverseH2 :
    ChartSupportedWholePlaneC3H2 →L[ℂ] TransverseC3H2 :=
  chartH2GraphMap.codRestrict transverseH2Submodule chartH2GraphMap_mem

/-- The physical `L²` value of the descended periodic `H²` element is the torus restriction of the
jet's whole-plane value, so the descent map does not alter the value row. -/
theorem transverseH2Embedding_wholePlaneChartToTransverseH2
    (u : ChartSupportedWholePlaneC3H2) :
    transverseH2Embedding (wholePlaneChartToTransverseH2 u) =
      chartValueL2 u :=
  rfl

/-- The first derivative synthesized from the periodic `H²` graph is exactly
the quotient descent of the actual whole-plane weak derivative. -/
theorem transverseDerivFromH2_wholePlaneChartToTransverseH2
    (u : ChartSupportedWholePlaneC3H2) (j : Fin 2) :
    transverseDerivFromH2 j (wholePlaneChartToTransverseH2 u) =
      chartFirstDerivativeL2 j u := by
  apply (transverseDerivFromH2_hasFourierDerivative j
    (wholePlaneChartToTransverseH2 u)).unique
  change HasTransverseFourierDerivative j
    (chartValueL2 u) (chartFirstDerivativeL2 j u)
  exact chartFirstDerivative_hasFourierDerivative u j

/-- The periodic `H²` Laplacian is exactly the descended whole-plane
diagonal second-derivative sum. -/
theorem transverseLaplacianFromH2_wholePlaneChartToTransverseH2
    (u : ChartSupportedWholePlaneC3H2) :
    transverseLaplacianFromH2 (wholePlaneChartToTransverseH2 u) =
      chartLaplacianL2 u := by
  apply (transverseLaplacianFromH2_hasFourierLaplacian
    (wholePlaneChartToTransverseH2 u)).unique
  change HasTransverseFourierLaplacian
    (chartValueL2 u) (chartLaplacianL2 u)
  exact chartLaplacian_hasFourierLaplacian u

end TorusChartH2

end

end FastDynamo
