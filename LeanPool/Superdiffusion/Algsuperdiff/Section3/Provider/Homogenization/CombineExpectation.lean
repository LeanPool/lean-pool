/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineGoodEvent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionSiteProducers

/-!
# CombineExpectation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The expectation lane of Step 1 of the corrected combine proposition

Step 1 of Proposition `p.combine.under.S` is printed as a chain of
expectations.  The two sample-by-sample halves are available separately: the
good-event display
`exists_cutoffGoodEvent_cutoffResponseJ_le_preVarianceSplitDisplay`
(`Provider/Homogenization/CombineGoodEvent.lean`) and the bad-event integral
bound `exists_relativeCutoff_observationScale_badEvent_bound`
(`Provider/Homogenization/CombineBadEvent.lean`).  This module carries the
passage from the first of them to expectations:

* *integrability* of the response observable `J(cu_n, sigmabar_L^{-1/2} e,
  sigmabar_L^{1/2} e; a_L)` at every observation scale of the printed corridor
  `L <= n <= m`, from the pathwise domination `J <= mathcal E^2`
  (`Provider/Homogenization/ResponseCommonDomination.lean`) against the
  `Gamma_{1/4}` control of the squared error;
* *stationarity* (`a.j.frd#stationary`): the mean of the response at a
  depth-`(m - n)` descendant of `cu_m` is the mean at the origin cube `cu_n`,
  so the mean of the deterministic defect average
  `WeakNormsMaximizer.responseDefectAverageAtScale m n` is the printed single
  cube difference `E[J(cu_n)] - E[J(cu_m)]`;
* *subadditivity in expectation*: `E[J(cu_m)] <= E[J(cu_{m-1})]`, which is the
  first line of the printed chain, obtained from the deterministic depth-one
  subadditivity `e.subaddJ.nosymm` through the same stationarity conversion;
* the *indicator split* `E[J(cu_{m-1})] = E[J(cu_{m-1}) 1_G] +
  E[J(cu_{m-1}) 1_B]` over the good event `G = B^c` with
  `B = observationScaleBadEvent M L m`, the integration of the good-event
  display over `G`, and the assembly with the bad-event contribution.

The last public also performs the printed reabsorption of `1/2 E[J(cu_m)]`,
which is legitimate here precisely because the integrability lane supplies
`E[J(cu_m)] < infinity` at the same hypotheses.

## What this module does *not* do

The variance split is not performed: the second and third blocks of the
right-hand side are still the *expectations of the deterministic field
quantities* `coarseMatrixVariationBlock` and `coarseScaleSeparationBlock` over
the good event, carrying one power of `sigmabar_L` and an `avsum`, not
`sigmabar_L^2` and the two variances of `e.initial.JL.bound`.  The *use* of the
`e.pq.normed` normalization inside that split (the passage from `6|q|^2` and
`6|p|^2` to `sigmabar_L^2`), the sandwich, `e.annealed.khom.zero`,
`d.mathcalS.def`, and the induction-regime hypotheses of the source node are
all absent here as well; the normalization itself is present, as the binder
`he`.

## References

* ABK26, Section 3.5, proof of `p.combine.under.S`, Step 1, and the corrected
  Step 4.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open _root_.HCPolySupport.Book.Ch05.Section53
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Besov
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-! ## The integrability lane

The response observable is nonnegative and dominated, off one null set, by the
square of the observation-cube homogenization error read from the same common
representative.  A `Gamma_{1/4}` upper-tail bound for that square therefore
gives a first-moment majorant.
-/

/-- **Integrability of the cutoff response from a `Gamma_{1/4}` bound on the
squared error.**  The observation cube `cu_n` and the coefficient cutoff scale
`L` remain separate arguments. -/
theorem integrable_cutoffResponseJ_of_isBigOWith_errorSq (M : ABKModel d) (n L : ℤ)
    {theta : ℝ} (htheta : 0 < theta) {e : Vec d} (he : Ch02.vecNorm e = 1) :
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
        (fun omega =>
          Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
            (Annealed.sigmaBar M L) omega ^ 2) theta →
      Integrable (Observable.cutoffResponseJ M n L e)
        (cutoffSampleLaw M).toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  intro hcov
  have hmeas : Measurable fun omega =>
      Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
        (Annealed.sigmaBar M L) omega ^ 2 :=
    (Observable.measurable_cutoffHomogenizationErrorRepresentative M L n eighth_pos
      (Annealed.sigmaBar M L)).pow_const 2
  have hrpow := integrable_rpow_of_isBigOWith_gammaSigma
    (μ := (cutoffSampleLaw M).toMeasure)
    (Y := fun omega =>
      Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
        (Annealed.sigmaBar M L) omega ^ 2)
    (K := theta) (σ := 1 / 4) (p := 1) (by norm_num) htheta le_rfl
    (fun _ => sq_nonneg _) hmeas.aemeasurable hcov
  have hmajor : Integrable (fun omega =>
      Observable.cutoffHomogenizationErrorRepresentative M L n eighth_pos
        (Annealed.sigmaBar M L) omega ^ 2) (cutoffSampleLaw M).toMeasure := by
    simpa only [Real.rpow_one] using hrpow
  refine hmajor.mono'
    (Observable.measurable_cutoffResponseJ M n L e).aestronglyMeasurable ?_
  filter_upwards [ae_forall_cutoffResponseJ_le_observationHomogenizationError_sq M n L
      eighth_pos, Observable.ae_forall_cutoffResponseJ_nonneg M n L]
    with omega hdom hnn
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn e)]
  exact hdom e he

/-- **Integrability along the printed corridor.**  At every observation scale
`L <= n <= m` the response is integrable under the genuine cutoff sample law.

At the diagonal `n = L` the datum is the frozen preceding-error clause
itself, through the proved per-site integrability producer; above the diagonal
it is the proved observation-scale finite cover, which merges the two lanes
into a single `Gamma_{1/4}` envelope -- enough for a first moment, although not
for the two-lane concentration display. -/
theorem integrable_cutoffResponseJ_of_precedingError (M : ABKModel d) (m L : ℤ)
    (hLm : L ≤ m - 1) (E : {E : ℝ // 1 ≤ E})
    (hLower : ∀ k : ℤ, k ≤ m - 1 →
      ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
        Probability.IsTwoTermBigOWith
          (cutoffSampleLaw M).toMeasure
          (gammaSigma 2) (gammaSigma (1 / 2))
          (Observable.cutoffHomogenizationError M k
            ⟨s,
              (mul_pos (by norm_num : (0 : ℝ) < 8)
                M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
          ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
          ((s⁻¹) ^ 2 * Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))
    (hwindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1)
    {e : Vec d} (he : Ch02.vecNorm e = 1) (n : ℤ) (hLn : L ≤ n) (hnm : n ≤ m) :
    Integrable (Observable.cutoffResponseJ M n L e)
      (cutoffSampleLaw M).toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  rcases eq_or_lt_of_le hLn with hEq | hLt
  · subst hEq
    exact integrable_siteResponseJ M L L (by norm_num : (0 : ℝ) < 1 / 16) 0 he
      (hLower L hLm (1 / 16) hwindow)
  · obtain ⟨Cobs, hCobs1, hCobs⟩ :=
      observationScaleFiniteCover_sq_isBigOWith_gammaQuarter d
    have hcov := hCobs M n E (fun k hk => hLower k (by omega)) hwindow L (by omega)
    have hCobsPos : (0 : ℝ) < Cobs := lt_of_lt_of_le zero_lt_one hCobs1
    have hBpos : (0 : ℝ) < ((1 / 16 : ℝ)⁻¹) ^ 2 *
        Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by positivity
    have hthetaPos : (0 : ℝ) < Cobs *
        (((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma) ^ 2 +
          (((1 / 16 : ℝ)⁻¹) ^ 2 *
            Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ^ 2) :=
      mul_pos hCobsPos (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hBpos 2))
    exact integrable_cutoffResponseJ_of_isBigOWith_errorSq M n L hthetaPos he hcov

/-- Integrability transports to every site cube of the same scale, because the
site observable is the origin observable of the translated sample and the
genuine cutoff sample law is translation invariant. -/
theorem integrable_siteResponseJ_of_integrable_cutoffResponseJ (M : ABKModel d)
    (L n : ℤ) (u : Fin d → ℤ) {e : Vec d}
    (hint : Integrable (Observable.cutoffResponseJ M n L e)
      (cutoffSampleLaw M).toMeasure) :
    Integrable (siteResponseJ M L n u e) (cutoffSampleLaw M).toMeasure := by
  have hpres : MeasurePreserving
      (translateCutoffSample (triadicCubeShift (siteCube n u)))
      (cutoffSampleLaw M).toMeasure (cutoffSampleLaw M).toMeasure :=
    ⟨measurable_translateCutoffSample _,
      map_translateCutoffSample_cutoffSampleLaw M _⟩
  refine (hpres.integrable_comp_of_integrable hint).congr ?_
  filter_upwards [ae_siteResponseJ_eq_comp_translate M L n u e] with omega homega
  exact homega.symm

/-! ## The stationarity conversion (`a.j.frd#stationary`) -/

/-- Every depth-`(m - n)` descendant of the `m`-cube is the site cube of its own
index at scale `n`, so the proved per-site producers apply to it verbatim. -/
private theorem siteCube_index_eq_of_mem_descendantsAtDepth {m n : ℤ} (hnm : n ≤ m)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d m) (m - n).toNat) :
    siteCube n R.index = R := by
  have hscale : R.scale = n := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hcast : (((m - n).toNat : ℤ)) = m - n := Int.toNat_of_nonneg (by omega)
    have hOrigin : (originCube d m).scale = m := rfl
    rw [hcast, hOrigin] at h
    omega
  rw [← hscale]
  rfl

/-- The descendant average of the literal response is, off one null set, the grid
average of the proved per-site observables. -/
private theorem ae_descendantsAverage_eq_gridSum (M : ABKModel d) (m n L : ℤ)
    (hnm : n ≤ m) (e : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      descendantsAverage (originCube d m) (m - n).toNat
          (fun R => Ch04.restrictionResponseJObservableCubeSet R
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (coefficientCutoff M.nu L omega)) =
        ((descendantsAtDepth (originCube d m) (m - n).toNat).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d m) (m - n).toNat,
            siteResponseJ M L n R.index e omega := by
  have hall : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ R ∈ descendantsAtDepth (originCube d m) (m - n).toNat,
        siteResponseJ M L n R.index e omega =
          Ch04.restrictionResponseJObservableCubeSet R
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (coefficientCutoff M.nu L omega) := by
    rw [eventually_all_finset]
    intro R hR
    filter_upwards [ae_siteResponseJ_eq_responseJ M L n R.index e] with omega homega
    rw [homega, siteCube_index_eq_of_mem_descendantsAtDepth hnm hR]
    rfl
  filter_upwards [hall] with omega homega
  rw [descendantsAverage]
  exact congrArg
    (fun t => ((descendantsAtDepth (originCube d m) (m - n).toNat).card : ℝ)⁻¹ * t)
    (Finset.sum_congr rfl fun R hR => (homega R hR).symm)

private theorem card_descendants_ne_zero (m n : ℤ) :
    (((descendantsAtDepth (originCube d m) (m - n).toNat).card : ℝ)) ≠ 0 := by
  have hpos : 0 < (descendantsAtDepth (originCube d m) (m - n).toNat).card :=
    (descendantsAtDepth_nonempty (originCube d m) _).card_pos
  exact_mod_cast hpos.ne'

/-- The descendant average of the literal response is integrable as soon as the
origin-cube response at the descendant scale is. -/
theorem integrable_descendantsAverage_restrictionResponseJ (M : ABKModel d)
    (m n L : ℤ) (hnm : n ≤ m) {e : Vec d}
    (hint : Integrable (Observable.cutoffResponseJ M n L e)
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega =>
        descendantsAverage (originCube d m) (m - n).toNat
          (fun R => Ch04.restrictionResponseJObservableCubeSet R
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (coefficientCutoff M.nu L omega)))
      (cutoffSampleLaw M).toMeasure := by
  have hsum : Integrable (fun omega =>
      ∑ R ∈ descendantsAtDepth (originCube d m) (m - n).toNat,
        siteResponseJ M L n R.index e omega) (cutoffSampleLaw M).toMeasure :=
    integrable_finsetSum _ fun R _ =>
      integrable_siteResponseJ_of_integrable_cutoffResponseJ M L n R.index hint
  refine Integrable.congr
    (hsum.const_mul
      (((descendantsAtDepth (originCube d m) (m - n).toNat).card : ℝ)⁻¹)) ?_
  filter_upwards [ae_descendantsAverage_eq_gridSum M m n L hnm e] with omega homega
  exact homega.symm

/-- **The stationarity conversion of the descendant average.**  All the
depth-`(m - n)` descendants of `cu_m` have the same response mean as the origin
cube `cu_n`, so the mean of the descendant average is `E[J(cu_n)]`.  This is the
form in which `a.j.frd#stationary` is used at this consumer. -/
theorem integral_descendantsAverage_restrictionResponseJ_eq (M : ABKModel d)
    (m n L : ℤ) (hnm : n ≤ m) {e : Vec d}
    (hint : Integrable (Observable.cutoffResponseJ M n L e)
      (cutoffSampleLaw M).toMeasure) :
    ∫ omega, descendantsAverage (originCube d m) (m - n).toNat
          (fun R => Ch04.restrictionResponseJObservableCubeSet R
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (coefficientCutoff M.nu L omega))
        ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega, Observable.cutoffResponseJ M n L e omega
        ∂(cutoffSampleLaw M).toMeasure := by
  rw [integral_congr_ae (ae_descendantsAverage_eq_gridSum M m n L hnm e),
    integral_const_mul,
    integral_finsetSum _ fun R _ =>
      integrable_siteResponseJ_of_integrable_cutoffResponseJ M L n R.index hint]
  simp only [integral_siteResponseJ_eq_integral_cutoffResponseJ M L n _ e]
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (card_descendants_ne_zero m n), one_mul]

/-- The deterministic parent-child defect of `e.subaddJ.nosymm` is integrable
along the corridor. -/
theorem integrable_responseDefectAverageAtScale (M : ABKModel d) (m n L : ℤ)
    (hnm : n ≤ m) {e : Vec d}
    (hintn : Integrable (Observable.cutoffResponseJ M n L e)
      (cutoffSampleLaw M).toMeasure)
    (hintm : Integrable (Observable.cutoffResponseJ M m L e)
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega =>
        WeakNormsMaximizer.responseDefectAverageAtScale m n
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega)) (cutoffSampleLaw M).toMeasure := by
  have hparentAe : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffResponseJ M m L e omega =
        Ch04.restrictionResponseJObservableCubeSet (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega) := by
    filter_upwards [Observable.ae_forall_cutoffResponseJ_eq_literal M m L]
      with omega homega
    exact homega e
  exact (integrable_descendantsAverage_restrictionResponseJ M m n L hnm hintn).sub
    (hintm.congr hparentAe)

/-- **The printed defect identity.**  Taking the expectation of the
deterministic depth-`(m - n)` defect average and using stationarity gives the
printed single-cube difference `E[J(cu_n)] - E[J(cu_m)]`. -/
theorem integral_responseDefectAverageAtScale_eq_sub (M : ABKModel d) (m n L : ℤ)
    (hnm : n ≤ m) {e : Vec d}
    (hintn : Integrable (Observable.cutoffResponseJ M n L e)
      (cutoffSampleLaw M).toMeasure)
    (hintm : Integrable (Observable.cutoffResponseJ M m L e)
      (cutoffSampleLaw M).toMeasure) :
    ∫ omega, WeakNormsMaximizer.responseDefectAverageAtScale m n
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega) ∂(cutoffSampleLaw M).toMeasure =
      (∫ omega, Observable.cutoffResponseJ M n L e omega
          ∂(cutoffSampleLaw M).toMeasure) -
        ∫ omega, Observable.cutoffResponseJ M m L e omega
          ∂(cutoffSampleLaw M).toMeasure := by
  have hparentAe : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffResponseJ M m L e omega =
        Ch04.restrictionResponseJObservableCubeSet (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega) := by
    filter_upwards [Observable.ae_forall_cutoffResponseJ_eq_literal M m L]
      with omega homega
    exact homega e
  have hfun : ∀ omega : CutoffSample d,
      WeakNormsMaximizer.responseDefectAverageAtScale m n
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega) =
        descendantsAverage (originCube d m) (m - n).toNat
            (fun R => Ch04.restrictionResponseJObservableCubeSet R
              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
              (coefficientCutoff M.nu L omega)) -
          Ch04.restrictionResponseJObservableCubeSet (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (coefficientCutoff M.nu L omega) := fun _ => rfl
  simp only [hfun]
  rw [integral_sub
      (integrable_descendantsAverage_restrictionResponseJ M m n L hnm hintn)
      (hintm.congr hparentAe),
    integral_descendantsAverage_restrictionResponseJ_eq M m n L hnm hintn,
    ← integral_congr_ae hparentAe]

/-- **Subadditivity of the response in expectation**.  The deterministic depth-one
subadditivity `e.subaddJ.nosymm` and the stationarity conversion give the first
line of the printed chain. -/
theorem integral_cutoffResponseJ_le_integral_cutoffResponseJ_pred (M : ABKModel d)
    (m L : ℤ) {e : Vec d}
    (hintpred : Integrable (Observable.cutoffResponseJ M (m - 1) L e)
      (cutoffSampleLaw M).toMeasure)
    (hintm : Integrable (Observable.cutoffResponseJ M m L e)
      (cutoffSampleLaw M).toMeasure) :
    ∫ omega, Observable.cutoffResponseJ M m L e omega
        ∂(cutoffSampleLaw M).toMeasure ≤
      ∫ omega, Observable.cutoffResponseJ M (m - 1) L e omega
        ∂(cutoffSampleLaw M).toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hval := integral_responseDefectAverageAtScale_eq_sub M m (m - 1) L
    (by omega) hintpred hintm
  have hnn : (0 : ℝ) ≤ ∫ omega,
      WeakNormsMaximizer.responseDefectAverageAtScale m (m - 1)
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
        (coefficientCutoff M.nu L omega) ∂(cutoffSampleLaw M).toMeasure := by
    refine integral_nonneg fun omega => ?_
    exact
      WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
        (coefficientCutoff M.nu L omega)
        (coefficientCutoff_aeLocallyUniformlyEllipticField M L omega) m (m - 1) _ _
  linarith

/-! ## The three deterministic blocks of the good-event display -/

/-- The first block of the good-event display: the weighted corridor sum of the
deterministic parent-child response defects. -/
def responseDefectBlock (M : ABKModel d) (m L : ℤ) (e : Vec d)
    (omega : CutoffSample d) : ℝ :=
  ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    WeakNormsMaximizer.responseDefectAverageAtScale m n
      (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
      (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
      (coefficientCutoff M.nu L omega)

/-- The second block of the good-event display: the weighted corridor sum of the
descendant averages of the coarse-matrix variation, the `avsum`. -/
def coarseMatrixVariationBlock (M : ABKModel d) (m L : ℤ) (e : Vec d)
    (omega : CutoffSample d) : ℝ :=
  ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq (coefficientCutoff M.nu L omega)
        (coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
        (originCube d m)
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M L) e))

/-- The third block of the good-event display: the squared coarse scale separation
at the parent cube, the constant tail. -/
def coarseScaleSeparationBlock (M : ABKModel d) (m L : ℤ) (e : Vec d)
    (omega : CutoffSample d) : ℝ :=
  vecNormSq (coarseScaleSeparation (coefficientCutoff M.nu L omega)
    (coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
    (originCube d m)
    (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
    (Observable.sqrtLoad (Annealed.sigmaBar M L) e))

/-- The defect block is pointwise nonnegative, by the response subadditivity of
each corridor summand (`e.subaddJ.nosymm`). -/
theorem responseDefectBlock_nonneg (M : ABKModel d) (m L : ℤ) (e : Vec d)
    (omega : CutoffSample d) : 0 ≤ responseDefectBlock M m L e omega := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  refine Finset.sum_nonneg fun n _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
  exact
    WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
      (coefficientCutoff M.nu L omega)
      (coefficientCutoff_aeLocallyUniformlyEllipticField M L omega) m n _ _

/-- The defect block is integrable once the response is integrable at every
corridor scale (supplied by `integrable_cutoffResponseJ_of_precedingError`). -/
theorem integrable_responseDefectBlock (M : ABKModel d) (m L : ℤ) (hLm : L ≤ m)
    {e : Vec d}
    (hJ : ∀ n : ℤ, L ≤ n → n ≤ m →
      Integrable (Observable.cutoffResponseJ M n L e) (cutoffSampleLaw M).toMeasure) :
    Integrable (responseDefectBlock M m L e) (cutoffSampleLaw M).toMeasure := by
  refine integrable_finsetSum _ fun n hn => Integrable.const_mul ?_ _
  rw [Finset.mem_Icc] at hn
  exact integrable_responseDefectAverageAtScale M m n L hn.2 (hJ n hn.1 hn.2)
    (hJ m hLm le_rfl)

/-- **The expectation of the first block.**  Stationarity turns each
deterministic defect average into the printed difference of single-cube means. -/
theorem integral_responseDefectBlock_eq (M : ABKModel d) (m L : ℤ) (hLm : L ≤ m)
    {e : Vec d}
    (hJ : ∀ n : ℤ, L ≤ n → n ≤ m →
      Integrable (Observable.cutoffResponseJ M n L e) (cutoffSampleLaw M).toMeasure) :
    ∫ omega, responseDefectBlock M m L e omega ∂(cutoffSampleLaw M).toMeasure =
      ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        ((∫ omega, Observable.cutoffResponseJ M n L e omega
            ∂(cutoffSampleLaw M).toMeasure) -
          ∫ omega, Observable.cutoffResponseJ M m L e omega
            ∂(cutoffSampleLaw M).toMeasure) := by
  have hterm : ∀ n ∈ Finset.Icc L m,
      Integrable (fun omega => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        WeakNormsMaximizer.responseDefectAverageAtScale m n
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (coefficientCutoff M.nu L omega)) (cutoffSampleLaw M).toMeasure := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact (integrable_responseDefectAverageAtScale M m n L hn.2 (hJ n hn.1 hn.2)
      (hJ m hLm le_rfl)).const_mul _
  simp only [responseDefectBlock]
  rw [integral_finsetSum _ hterm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  rw [integral_const_mul,
    integral_responseDefectAverageAtScale_eq_sub M m n L hn.2 (hJ n hn.1 hn.2)
      (hJ m hLm le_rfl)]

/-! ## The indicator split and the assembly -/

/-- **The expectation lane of Step 1 at the genuine cutoff sample law.**

The good-event display is integrated over `G = B^c`, the split `E[J(cu_{m-1})]
= E[J(cu_{m-1}) 1_G] + E[J(cu_{m-1}) 1_B]` is performed, and the first block is
converted by stationarity into the printed corridor sum of `E[J(cu_n)] -
E[J(cu_m)]`.  The reabsorbed energy term of the good-event display appears as
`1/2 E[J(cu_m)]` on the right, exactly as in the printed proof; the bad-event
contribution is left as the set integral that the proved bad-event endpoint
bounds.

The second and third blocks remain the expectations of the deterministic field
quantities over the good event: their conversion into the two variances of
`e.initial.JL.bound` is the variance split and is not performed here.  Their
integrability over `G` is a caller obligation.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_integral_cutoffResponseJ_centralChild_le_expectationDisplay (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M : ABKModel d) (m L : ℤ), L ≤ m - 1 →
        C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) ≤ 1 / 4 →
        ∀ E : {E : ℝ // 1 ≤ E},
          (∀ k : ℤ, k ≤ m - 1 →
            ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
              Probability.IsTwoTermBigOWith
                (cutoffSampleLaw M).toMeasure
                (gammaSigma 2) (gammaSigma (1 / 2))
                (Observable.cutoffHomogenizationError M k
                  ⟨s,
                    (mul_pos (by norm_num : (0 : ℝ) < 8)
                      M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
                ((s⁻¹) ^ 2 *
                  Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
          (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
          ∀ e : Vec d, Ch02.vecNorm e = 1 →
            IntegrableOn (coarseMatrixVariationBlock M m L e)
                (observationScaleBadEvent M L m)ᶜ (cutoffSampleLaw M).toMeasure →
            IntegrableOn (coarseScaleSeparationBlock M m L e)
                (observationScaleBadEvent M L m)ᶜ (cutoffSampleLaw M).toMeasure →
              ∫ omega, Observable.cutoffResponseJ M (m - 1) L e omega
                  ∂(cutoffSampleLaw M).toMeasure ≤
                1 / 2 * ∫ omega, Observable.cutoffResponseJ M m L e omega
                    ∂(cutoffSampleLaw M).toMeasure +
                  C * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                      ((∫ omega, Observable.cutoffResponseJ M n L e omega
                          ∂(cutoffSampleLaw M).toMeasure) -
                        ∫ omega, Observable.cutoffResponseJ M m L e omega
                          ∂(cutoffSampleLaw M).toMeasure)) +
                  C * ((Annealed.sigmaBar M L : ℝ) *
                    ∫ omega in (observationScaleBadEvent M L m)ᶜ,
                      coarseMatrixVariationBlock M m L e omega
                      ∂(cutoffSampleLaw M).toMeasure) +
                  C * ((Annealed.sigmaBar M L : ℝ) *
                    ∫ omega in (observationScaleBadEvent M L m)ᶜ,
                      coarseScaleSeparationBlock M m L e omega
                      ∂(cutoffSampleLaw M).toMeasure) +
                  ∫ omega in observationScaleBadEvent M L m,
                    Observable.cutoffResponseJ M (m - 1) L e omega
                    ∂(cutoffSampleLaw M).toMeasure := by
  obtain ⟨C, hC1, hgood⟩ :=
    exists_cutoffGoodEvent_cutoffResponseJ_le_preVarianceSplitDisplay d
  refine ⟨C, hC1, ?_⟩
  intro M m L hLm1 hgate E hLower hwindow e he hVarInt hSepInt
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hJ : ∀ n : ℤ, L ≤ n → n ≤ m →
      Integrable (Observable.cutoffResponseJ M n L e) (cutoffSampleLaw M).toMeasure :=
    fun n h1 h2 =>
      integrable_cutoffResponseJ_of_precedingError M m L hLm1 E hLower hwindow he n h1 h2
  have hJm := hJ m (by omega) le_rfl
  have hJm1 := hJ (m - 1) (by omega) (by omega)
  have hBmeas := measurableSet_observationScaleBadEvent M L m
  have hGmeas : MeasurableSet (observationScaleBadEvent M L m)ᶜ := hBmeas.compl
  have hDint := integrable_responseDefectBlock M m L (by omega) hJ
  have hDval := integral_responseDefectBlock_eq M m L (by omega) hJ
  have hJm1nn : 0 ≤ᵐ[(cutoffSampleLaw M).toMeasure]
      Observable.cutoffResponseJ M (m - 1) L e := by
    filter_upwards [Observable.ae_forall_cutoffResponseJ_nonneg M (m - 1) L]
      with omega homega
    exact homega e
  have hJmnn : 0 ≤ᵐ[(cutoffSampleLaw M).toMeasure]
      Observable.cutoffResponseJ M m L e := by
    filter_upwards [Observable.ae_forall_cutoffResponseJ_nonneg M m L] with omega homega
    exact homega e
  -- the good-event part
  have hhalf : Integrable (fun omega =>
      1 / 2 * Observable.cutoffResponseJ M m L e omega)
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    hJm.restrict.const_mul _
  have hdef : Integrable (fun omega => C * responseDefectBlock M m L e omega)
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    hDint.restrict.const_mul _
  have hvar : Integrable (fun omega =>
      C * ((Annealed.sigmaBar M L : ℝ) * coarseMatrixVariationBlock M m L e omega))
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    (hVarInt.const_mul _).const_mul _
  have hsep : Integrable (fun omega =>
      C * ((Annealed.sigmaBar M L : ℝ) * coarseScaleSeparationBlock M m L e omega))
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    (hSepInt.const_mul _).const_mul _
  have hAB : Integrable (fun omega =>
      1 / 2 * Observable.cutoffResponseJ M m L e omega +
        C * responseDefectBlock M m L e omega)
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    hhalf.add hdef
  have hABC : Integrable (fun omega =>
      1 / 2 * Observable.cutoffResponseJ M m L e omega +
          C * responseDefectBlock M m L e omega +
        C * ((Annealed.sigmaBar M L : ℝ) * coarseMatrixVariationBlock M m L e omega))
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    hAB.add hvar
  have hABCD : Integrable (fun omega =>
      1 / 2 * Observable.cutoffResponseJ M m L e omega +
            C * responseDefectBlock M m L e omega +
          C * ((Annealed.sigmaBar M L : ℝ) *
            coarseMatrixVariationBlock M m L e omega) +
        C * ((Annealed.sigmaBar M L : ℝ) *
          coarseScaleSeparationBlock M m L e omega))
      ((cutoffSampleLaw M).toMeasure.restrict (observationScaleBadEvent M L m)ᶜ) :=
    hABC.add hsep
  have hGle : ∫ omega in (observationScaleBadEvent M L m)ᶜ,
        Observable.cutoffResponseJ M (m - 1) L e omega
        ∂(cutoffSampleLaw M).toMeasure ≤
      ∫ omega in (observationScaleBadEvent M L m)ᶜ,
        (1 / 2 * Observable.cutoffResponseJ M m L e omega +
            C * responseDefectBlock M m L e omega +
            C * ((Annealed.sigmaBar M L : ℝ) *
              coarseMatrixVariationBlock M m L e omega) +
            C * ((Annealed.sigmaBar M L : ℝ) *
              coarseScaleSeparationBlock M m L e omega))
        ∂(cutoffSampleLaw M).toMeasure := by
    refine integral_mono_of_nonneg (ae_restrict_of_ae hJm1nn) hABCD ?_
    refine (ae_restrict_iff' hGmeas).mpr ?_
    filter_upwards [hgood M m L hLm1 hgate e] with omega homega hmem
    exact homega hmem
  have hRhs : ∫ omega in (observationScaleBadEvent M L m)ᶜ,
        (1 / 2 * Observable.cutoffResponseJ M m L e omega +
            C * responseDefectBlock M m L e omega +
            C * ((Annealed.sigmaBar M L : ℝ) *
              coarseMatrixVariationBlock M m L e omega) +
            C * ((Annealed.sigmaBar M L : ℝ) *
              coarseScaleSeparationBlock M m L e omega))
        ∂(cutoffSampleLaw M).toMeasure =
      1 / 2 * (∫ omega in (observationScaleBadEvent M L m)ᶜ,
          Observable.cutoffResponseJ M m L e omega
          ∂(cutoffSampleLaw M).toMeasure) +
        C * (∫ omega in (observationScaleBadEvent M L m)ᶜ,
            responseDefectBlock M m L e omega ∂(cutoffSampleLaw M).toMeasure) +
        C * ((Annealed.sigmaBar M L : ℝ) *
          ∫ omega in (observationScaleBadEvent M L m)ᶜ,
            coarseMatrixVariationBlock M m L e omega
            ∂(cutoffSampleLaw M).toMeasure) +
        C * ((Annealed.sigmaBar M L : ℝ) *
          ∫ omega in (observationScaleBadEvent M L m)ᶜ,
            coarseScaleSeparationBlock M m L e omega
            ∂(cutoffSampleLaw M).toMeasure) := by
    rw [integral_add hABC hsep, integral_add hAB hvar, integral_add hhalf hdef]
    simp only [integral_const_mul]
  have hJmG : ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      Observable.cutoffResponseJ M m L e omega ∂(cutoffSampleLaw M).toMeasure ≤
        ∫ omega, Observable.cutoffResponseJ M m L e omega
          ∂(cutoffSampleLaw M).toMeasure :=
    setIntegral_le_integral hJm hJmnn
  have hDG : ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      responseDefectBlock M m L e omega ∂(cutoffSampleLaw M).toMeasure ≤
        ∫ omega, responseDefectBlock M m L e omega ∂(cutoffSampleLaw M).toMeasure :=
    setIntegral_le_integral hDint
      (Filter.Eventually.of_forall (responseDefectBlock_nonneg M m L e))
  have hDG' : C * ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      responseDefectBlock M m L e omega ∂(cutoffSampleLaw M).toMeasure ≤
        C * ∫ omega, responseDefectBlock M m L e omega
          ∂(cutoffSampleLaw M).toMeasure :=
    mul_le_mul_of_nonneg_left hDG hC0
  have hsplit := integral_add_compl hBmeas hJm1
  rw [← hDval]
  linarith [hGle, hRhs, hJmG, hDG', hsplit]

/-- **The reabsorbed expectation display of Step 1.**

Subadditivity in expectation places `E[J(cu_m)]` below `E[J(cu_{m-1})]`, so the
`1/2 E[J(cu_m)]` produced by the good-event branch may be reabsorbed -- the
integrability lane is what makes the reabsorption legitimate -- and the
bad-event contribution is replaced by the proved corrected Step-4 bound.  The
result is the printed `e.initial.JL.bound` with its second and third blocks
still in pre-variance-split form.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_integral_cutoffResponseJ_le_reabsorbedExpectationDisplay (d : ℕ) :
    ∃ Chom C Cbad : ℝ, 64 ≤ Chom ∧ 1 ≤ C ∧ 1 ≤ Cbad ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∀ L : ℤ, L ≤ m - 2 →
            C * (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) ≤ 1 / 4 →
            ∀ e : Vec d, Ch02.vecNorm e = 1 →
              IntegrableOn (coarseMatrixVariationBlock M m L e)
                  (observationScaleBadEvent M L m)ᶜ (cutoffSampleLaw M).toMeasure →
              IntegrableOn (coarseScaleSeparationBlock M m L e)
                  (observationScaleBadEvent M L m)ᶜ (cutoffSampleLaw M).toMeasure →
                let delta1 : ℝ := 10 ^ 9 * (E : ℝ) ^ 2 * M.gamma
                ∫ omega, Observable.cutoffResponseJ M m L e omega
                    ∂(cutoffSampleLaw M).toMeasure ≤
                  2 * (C * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                        ((∫ omega, Observable.cutoffResponseJ M n L e omega
                            ∂(cutoffSampleLaw M).toMeasure) -
                          ∫ omega, Observable.cutoffResponseJ M m L e omega
                            ∂(cutoffSampleLaw M).toMeasure)) +
                    C * ((Annealed.sigmaBar M L : ℝ) *
                      ∫ omega in (observationScaleBadEvent M L m)ᶜ,
                        coarseMatrixVariationBlock M m L e omega
                        ∂(cutoffSampleLaw M).toMeasure) +
                    C * ((Annealed.sigmaBar M L : ℝ) *
                      ∫ omega in (observationScaleBadEvent M L m)ᶜ,
                        coarseScaleSeparationBlock M m L e omega
                        ∂(cutoffSampleLaw M).toMeasure) +
                    Cbad * delta1 ^ 2) := by
  obtain ⟨Chom, Cbad, hChom, hCbad, hbad⟩ :=
    exists_relativeCutoff_observationScale_badEvent_bound d
  obtain ⟨C, hC1, hexp⟩ :=
    exists_integral_cutoffResponseJ_centralChild_le_expectationDisplay d
  refine ⟨Chom, C, Cbad, hChom, hC1, hCbad, ?_⟩
  intro M m E hEfloor hregime hLower epsilon hepsilon hgate L hsep hgateC e he
    hVarInt hSepInt delta1
  have hEpos : (0 : ℝ) < (E : ℝ) := zero_lt_one.trans_le E.property
  have hEinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have hEinvOne : (E : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hEpos).2 E.property
    have hEinvNonneg : 0 ≤ (E : ℝ)⁻¹ := inv_nonneg.mpr hEpos.le
    nlinarith
  have hChomPos : (0 : ℝ) < Chom := by linarith
  have hChomInv : Chom⁻¹ ≤ 1 / 64 := by
    have hid : Chom⁻¹ * Chom = 1 := inv_mul_cancel₀ hChomPos.ne'
    nlinarith [mul_nonneg (inv_pos.mpr hChomPos).le
      (by linarith : (0 : ℝ) ≤ Chom - 64)]
  have hgamma128 : M.gamma ≤ 1 / 128 := by
    have hpair : Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 ≤ 1 / 64 * 1 :=
      mul_le_mul hChomInv hEinvSq (sq_nonneg _) (by norm_num)
    have hfull : Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ≤ 1 / 64 * 1 * (1 / 2) :=
      mul_le_mul hpair hepsilon.2 hepsilon.1.le (by norm_num)
    have hval : (1 / 64 * 1 : ℝ) * (1 / 2) = 1 / 128 := by norm_num
    linarith
  have hwindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 :=
    ⟨by linarith, by norm_num⟩
  have hLm1 : L ≤ m - 1 := by omega
  have hJm := integrable_cutoffResponseJ_of_precedingError M m L hLm1 E hLower hwindow
    he m (by omega) le_rfl
  have hJm1 := integrable_cutoffResponseJ_of_precedingError M m L hLm1 E hLower hwindow
    he (m - 1) (by omega) (by omega)
  have hsub := integral_cutoffResponseJ_le_integral_cutoffResponseJ_pred M m L hJm1 hJm
  have hstep := hexp M m L hLm1 hgateC E hLower hwindow e he hVarInt hSepInt
  have hbadbound :=
    (hbad M m E hEfloor hregime hLower epsilon hepsilon hgate L hsep).2 e he
  linarith

end

end Algsuperdiff.Section3.Provider.Homogenization
