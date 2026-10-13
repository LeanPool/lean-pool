/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GaussianMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TwoTermTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverDepth
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# ObservationScaleFiniteCover

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Observation-scale finite-cover transport

This module transports the lower-clause two-term homogenization-error bound
from the cutoff cube to a larger observation cube.  The transport is carried
out on the genuine measurable representative.  Translation covariance is
used only through the cutoff-sample action, and the spatial enlargement is
paid for by descendant averages, finite maxima, and the geometric depth
weights already present in the `q = 2` error.

The declarations here are internal Provider estimates.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverInternal
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The common constant for squaring the two-term observation-scale tail estimate. -/
def twoTermSquareConst : ℝ :=
  1 + 4 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹)

private theorem one_le_twoTermSquareConst : 1 ≤ twoTermSquareConst := by
  unfold twoTermSquareConst
  have hbase : 0 ≤ 3 * max 1 (Real.log 2) :=
    mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))
  have hfac : 0 ≤ (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) :=
    Real.rpow_nonneg hbase _
  linarith

private theorem isBigOWith_gammaQuarter_sq_of_twoTerm
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {X : Omega → ℝ} {A B : ℝ}
    (hXnonneg : ∀ omega, 0 ≤ X omega)
    (h : Probability.IsTwoTermBigOWith mu
      (gammaSigma 2) (gammaSigma (1 / 2)) X A B) :
    IsBigOWith mu (gammaSigma (1 / 4)) (fun omega => X omega ^ 2)
      (twoTermSquareConst * (A ^ 2 + B ^ 2)) := by
  obtain ⟨Y, Z, -, -, hA, hB, -, -, -, hdom, hYtail, hZtail⟩ := h
  let Y₀ : Omega → ℝ := fun omega => max 0 (Y omega)
  let Z₀ : Omega → ℝ := fun omega => max 0 (Z omega)
  have hY₀nonneg : ∀ omega, 0 ≤ Y₀ omega := fun omega => by
    exact le_max_left _ _
  have hZ₀nonneg : ∀ omega, 0 ≤ Z₀ omega := fun omega => by
    exact le_max_left _ _
  have hY₀tail : IsBigOWith mu (gammaSigma 2) Y₀ A := by
    simpa only [Y₀] using Tail.isBigOWith_max_zero hA hYtail
  have hZ₀tail : IsBigOWith mu (gammaSigma (1 / 2)) Z₀ B := by
    simpa only [Z₀] using Tail.isBigOWith_max_zero hB hZtail
  have hY₀sq : IsBigOWith mu (gammaSigma (1 / 4))
      (fun omega => Y₀ omega ^ 2) (A ^ 2) := by
    have hsq :=
      (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
        (μ := mu) (X := Y₀) (K := A) (σ := 2) hA.le hY₀nonneg).1 hY₀tail
    have hweak := HCPolySupport.Book.Ch04.IsBigOWith.gammaSigma_mono_exponent
      (ρ := (1 / 4 : ℝ)) (σ := (2 / 2 : ℝ)) (by norm_num) hsq
    simpa only [show (2 / 2 : ℝ) = 1 by norm_num] using hweak
  have hZ₀sq : IsBigOWith mu (gammaSigma (1 / 4))
      (fun omega => Z₀ omega ^ 2) (B ^ 2) := by
    simpa only [show ((1 / 2 : ℝ) / 2) = 1 / 4 by norm_num] using
      (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
        (μ := mu) (X := Z₀) (K := B) (σ := (1 / 2 : ℝ))
        hB.le hZ₀nonneg).1 hZ₀tail
  have hY₀two : IsBigOWith mu (gammaSigma (1 / 4))
      (fun omega => 2 * (Y₀ omega ^ 2)) (2 * A ^ 2) := by
    exact IsBigOWith.const_mul (by norm_num) hY₀sq
  have hZ₀two : IsBigOWith mu (gammaSigma (1 / 4))
      (fun omega => 2 * (Z₀ omega ^ 2)) (2 * B ^ 2) := by
    exact IsBigOWith.const_mul (by norm_num) hZ₀sq
  have hsum := Tail.isBigOWith_gammaSigma_add_of_nonneg
    (μ := mu) (σ := (1 / 4 : ℝ)) (A := 2 * A ^ 2) (B := 2 * B ^ 2)
    (by norm_num) (by positivity) (by positivity) hY₀two hZ₀two
  have hscale :
      2 * ((3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
          max (2 * A ^ 2) (2 * B ^ 2)) ≤
        twoTermSquareConst * (A ^ 2 + B ^ 2) := by
    have hfac : 0 ≤ (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) := by
      positivity
    have hmax : max (2 * A ^ 2) (2 * B ^ 2) ≤ 2 * (A ^ 2 + B ^ 2) := by
      apply max_le <;> nlinarith [sq_nonneg A, sq_nonneg B]
    unfold twoTermSquareConst
    have hsum0 : 0 ≤ A ^ 2 + B ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    calc
      2 * ((3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
          max (2 * A ^ 2) (2 * B ^ 2))
          ≤ 2 * ((3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
            (2 * (A ^ 2 + B ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax hfac)
          (by norm_num)
      _ ≤ (1 + 4 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹)) *
          (A ^ 2 + B ^ 2) := by nlinarith
  apply (hsum.mono_scale hscale).of_le
  intro omega
  have hXY : X omega ≤ Y₀ omega + Z₀ omega := by
    exact hdom omega |>.trans (add_le_add (le_max_right _ _) (le_max_right _ _))
  have hsumNonneg : 0 ≤ Y₀ omega + Z₀ omega :=
    add_nonneg (hY₀nonneg omega) (hZ₀nonneg omega)
  have hsq : X omega * X omega ≤
      (Y₀ omega + Z₀ omega) * (Y₀ omega + Z₀ omega) :=
    mul_self_le_mul_self (hXnonneg omega) hXY
  nlinarith [sq_nonneg (Y₀ omega - Z₀ omega)]

omit [NeZero d] in
/-- The measurable square of the cutoff-scale error at a translated
scale-`L` cell.  The coefficient and normalizer stay frozen at `L`. -/
def cutoffCellErrorSq (M : ABKModel d) (L : ℤ)
    {u : ℝ} (hu : 0 < u) (R : HCPolySupport.TriadicCube d) :
    Cutoff.CutoffSample d → ℝ  :=
  fun omega =>
    (Observable.cutoffHomogenizationErrorRepresentative M L L hu
      (Annealed.sigmaBar M L)
      (Cutoff.translateCutoffSample (HCPolySupport.triadicCubeShift R) omega)) ^ 2

omit [NeZero d] in
private theorem measurable_cutoffCellErrorSq (M : ABKModel d) (L : ℤ)
    {u : ℝ} (hu : 0 < u) (R : HCPolySupport.TriadicCube d) :
    Measurable (cutoffCellErrorSq M L hu R)  := by
  exact ((Observable.measurable_cutoffHomogenizationErrorRepresentative
    M L L hu (Annealed.sigmaBar M L)).comp
      (Cutoff.measurable_translateCutoffSample
        (HCPolySupport.triadicCubeShift R))).pow_const 2

omit [NeZero d] in
private theorem cutoffCellErrorSq_nonneg (M : ABKModel d) (L : ℤ)
    {u : ℝ} (hu : 0 < u) (R : HCPolySupport.TriadicCube d)
    (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffCellErrorSq M L hu R omega  :=
  sq_nonneg _

omit [NeZero d] in
private theorem cutoffCellErrorSq_isBigOWith_gammaQuarter
    (M : ABKModel d) (L : ℤ) {u : ℝ} (hu : 0 < u)
    (R : HCPolySupport.TriadicCube d) {A B : ℝ}
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L ⟨u, hu⟩) A B) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 4)) (cutoffCellErrorSq M L hu R)
      (twoTermSquareConst * (A ^ 2 + B ^ 2))  := by
  have htranslated := BadEvents.isTwoTermBigOWith_comp_translateCutoffSample
    M (HCPolySupport.triadicCubeShift R) hLower
  apply isBigOWith_gammaQuarter_sq_of_twoTerm
    (X := fun omega => Observable.cutoffHomogenizationError M L ⟨u, hu⟩
      (Cutoff.translateCutoffSample (HCPolySupport.triadicCubeShift R) omega))
  · intro omega
    exact Observable.cutoffHomogenizationError_nonneg M L ⟨u, hu⟩ _
  · simpa only [Observable.cutoffHomogenizationError,
      Observable.cutoffHomogenizationErrorAtComparatorScale,
      cutoffCellErrorSq] using htranslated

/-! ## Raw/representative finite cover -/

/-- The squared homogenization error for one cutoff cell against the isotropic comparator. -/
def cutoffCellErrorRawSq (M : ABKModel d) (L : ℤ) (u : ℝ)
    (R : HCPolySupport.TriadicCube d) : Cutoff.CutoffSample d → ℝ :=
  fun omega =>
    (Ch02.HomogenizationErrorOnCube R u .infinity (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))) ^ 2

private theorem cutoffCellErrorRawSq_ae_eq_cutoffCellErrorSq
    (M : ABKModel d) (L : ℤ) {u : ℝ} (hu : 0 < u)
    (R : HCPolySupport.TriadicCube d) (hRscale : R.scale = L) :
    cutoffCellErrorRawSq M L u R =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffCellErrorSq M L hu R := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let τ := Cutoff.translateCutoffSample (HCPolySupport.triadicCubeShift R)
  have hτ : MeasurePreserving τ μ μ := by
    refine ⟨Cutoff.measurable_translateCutoffSample
      (HCPolySupport.triadicCubeShift R), ?_⟩
    simpa only [μ, τ] using
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M
        (HCPolySupport.triadicCubeShift R)
  have horigin := Observable.cutoffHomogenizationErrorRaw_ae_eq_representative
    M L L hu (Annealed.sigmaBar M L)
  have htranslated := hτ.quasiMeasurePreserving.ae_eq_comp horigin
  filter_upwards [htranslated] with omega homega
  change (Ch02.HomogenizationErrorOnCube R u .infinity (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))) ^ 2 = _
  rw [BadEvents.homogenizationErrorOnCube_translateCutoffSample
    M L R u .infinity (.finite 2)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) omega,
    hRscale]
  have hchar := Observable.cutoffHomogenizationErrorRaw_characterization
    M L L u (Annealed.sigmaBar M L) (τ omega)
  rw [← hchar]
  exact congrArg (fun x : ℝ => x ^ 2) homega

/-- The geometrically weighted block-response error at one observation depth. -/
def observationScaleErrorLayerRaw (M : ABKModel d) (L m : ℤ)
    (t : ℝ) (ell : ℕ) (omega : Cutoff.CutoffSample d) : ℝ :=
  Ch02.geometricWeight t 2 ell *
    Ch02.maxDescendantNormalizedBlockResponseAtScale (originCube d m)
      (m - (ell : ℤ)) (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))

/-- The infinite error tail below the cutoff scale. -/
def observationScaleFineTailRaw (M : ABKModel d) (L m : ℤ)
    (t : ℝ) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑' n : ℕ, observationScaleErrorLayerRaw M L m t
    (Int.toNat (m - L) + n) omega

omit [NeZero d] in
/-- The largest parent-cube average of normalized cutoff-cell errors at one depth. -/
def observationScaleCoarseParentAverage (M : ABKModel d) (L m : ℤ) {u : ℝ} (hu : 0 < u)
    (ell : ℕ) (omega : Cutoff.CutoffSample d) : ℝ  :=
  Ch02.finsetSupReal (descendantsAtScale (originCube d m) (m - (ell : ℤ)))
    (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
      (fun R => cutoffCellErrorSq M L hu R omega))

omit [NeZero d] in
/-- The finite weighted envelope of coarse parent-cube error averages. -/
def observationScaleCoarseEnvelope (M : ABKModel d) (L m : ℤ) (t : ℝ) {u : ℝ} (hu : 0 < u)
    (omega : Cutoff.CutoffSample d) : ℝ  :=
  ∑ ell ∈ Finset.range (Int.toNat (m - L)),
    Ch02.geometricWeight t 2 ell *
      observationScaleCoarseParentAverage M L m hu ell omega

omit [NeZero d] in
/-- The maximum normalized cutoff-cell error at the cutoff scale. -/
def observationScaleCellErrorSup (M : ABKModel d) (L m : ℤ) {u : ℝ} (hu : 0 < u)
    (omega : Cutoff.CutoffSample d) : ℝ  :=
  Ch02.finsetSupReal (descendantsAtScale (originCube d m) L)
    (fun R => cutoffCellErrorSq M L hu R omega)

private theorem normalizedBlockResponseMax_le_cutoffCellErrorRawSq
    (M : ABKModel d) (L : ℤ) (R : HCPolySupport.TriadicCube d)
    {u : ℝ} (hu : 0 < u) (omega : Cutoff.CutoffSample d) :
    Ch02.normalizedBlockResponseMax R
        (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) ≤
      cutoffCellErrorRawSq M L u R omega := by
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  have hhead :=
    Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_le
      R le_rfl a a0
  have htail := maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
    R hu a a0 0
  have hpow : Real.rpow (3 : ℝ) (0 : ℝ) = 1 := Real.rpow_zero _
  simp only [Nat.cast_zero, sub_zero, mul_zero, hpow, one_mul] at htail
  exact hhead.trans (by simpa only [cutoffCellErrorRawSq, a, a0] using htail)

private theorem observationScaleErrorLayerRaw_coarse_le_parentAverage
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (ell : ℕ) (hell : ell < Int.toNat (m - L))
    (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      cutoffCellErrorRawSq M L u R omega ≤ cutoffCellErrorSq M L hu R omega) :
    observationScaleErrorLayerRaw M L m t ell omega ≤
      Ch02.geometricWeight t 2 ell *
        observationScaleCoarseParentAverage M L m hu ell omega := by
  classical
  let Q := originCube d m
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let r : ℕ := Int.toNat (m - L)
  have hr : (r : ℤ) = m - L := by
    dsimp [r]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hLm)
  have hellZ : (ell : ℤ) < m - L := by
    rw [← hr]
    exact_mod_cast hell
  have hLell : L ≤ m - (ell : ℤ) := by omega
  have hscale : m - (ell : ℤ) ≤ m :=
    sub_le_self m (by exact_mod_cast Nat.zero_le ell)
  have hweight : 0 ≤ Ch02.geometricWeight t 2 ell := by
    simpa [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg ell
        (by positivity : 0 ≤ t * (2 : ℝ))
  have hmax :
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q (m - (ell : ℤ)) a a0 ≤
        observationScaleCoarseParentAverage M L m hu ell omega := by
    unfold Ch02.maxDescendantNormalizedBlockResponseAtScale
    refine Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty Q hscale) ?_
    intro P hP
    have hPscale : P.scale = m - (ell : ℤ) :=
      descendant_scale_eq_of_mem_descendantsAtScale hP
    let j : ℕ := Int.toNat (m - (ell : ℤ) - L)
    have hj : (j : ℤ) = P.scale - L := by
      dsimp [j]
      rw [hPscale]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hLell)
    have hPavg := normalizedBlockResponseMax_le_descendantsAverage P j a a0
    have hdesc : descendantsAverage P j
        (fun R => Ch02.normalizedBlockResponseMax R a a0) ≤
        descendantsAverage P j (fun R => cutoffCellErrorSq M L hu R omega) := by
      apply descendantsAverage_le_descendantsAverage
      intro R hR
      have hRscale : R.scale = L := by
        rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hj]
        ring
      exact (normalizedBlockResponseMax_le_cutoffCellErrorRawSq
        M L R hu omega).trans (hcell R hRscale)
    have hbound : Ch02.normalizedBlockResponseMax P a a0 ≤
        descendantsAverage P j (fun R => cutoffCellErrorSq M L hu R omega) :=
      hPavg.trans hdesc
    have hsup : descendantsAverage P j
        (fun R => cutoffCellErrorSq M L hu R omega) ≤
        observationScaleCoarseParentAverage M L m hu ell omega := by
      apply le_csSup
      · exact ((Set.toFinite _).image fun S => descendantsAverage S
          (Int.toNat (m - (ell : ℤ) - L))
          (fun R => cutoffCellErrorSq M L hu R omega)).bddAbove
      · refine ⟨P, ?_, ?_⟩
        · simpa only [observationScaleCoarseParentAverage, Q] using! hP
        · rw [show j = Int.toNat (m - (ell : ℤ) - L) by rfl]
    exact hbound.trans hsup
  unfold observationScaleErrorLayerRaw
  exact mul_le_mul_of_nonneg_left hmax hweight

private theorem observationScaleErrorLayerRaw_fine_le_cellSup
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (n : ℕ) (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      cutoffCellErrorRawSq M L u R omega ≤ cutoffCellErrorSq M L hu R omega) :
    observationScaleErrorLayerRaw M L m t (Int.toNat (m - L) + n) omega ≤
      Ch02.geometricWeight t 2 (Int.toNat (m - L) + n) *
        Real.rpow 3 (2 * u * (n : ℝ)) *
          observationScaleCellErrorSup M L m hu omega := by
  classical
  let Q := originCube d m
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let r : ℕ := Int.toNat (m - L)
  let D := descendantsAtScale Q L
  let H : ℝ := Ch02.maxDescendantNormalizedBlockResponseAtScale Q
    (m - ((r + n : ℕ) : ℤ)) a a0
  have hr : (r : ℤ) = m - L := by
    dsimp [r]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hLm)
  have hscale : m - ((r + n : ℕ) : ℤ) = L - (n : ℤ) := by
    rw [show ((r + n : ℕ) : ℤ) = (r : ℤ) + (n : ℤ) by norm_num, hr]
    ring
  have hD : D.Nonempty := by
    dsimp [D, Q]
    exact descendantsAtScale_nonempty (originCube d m) hLm
  have hpoint : ∀ R ∈ D,
      Ch02.maxDescendantNormalizedBlockResponseAtScale R (L - (n : ℤ)) a a0 ≤
        Real.rpow 3 (2 * u * (n : ℝ)) * cutoffCellErrorSq M L hu R omega := by
    intro R hR
    have hRscale : R.scale = L := descendant_scale_eq_of_mem_descendantsAtScale hR
    have hraw := maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
      R hu a a0 n
    have hraw' : Ch02.maxDescendantNormalizedBlockResponseAtScale R
        (L - (n : ℤ)) a a0 ≤
        Real.rpow 3 (2 * u * (n : ℝ)) * cutoffCellErrorRawSq M L u R omega := by
      simpa only [hRscale, cutoffCellErrorRawSq, a, a0] using hraw
    exact hraw'.trans (mul_le_mul_of_nonneg_left (hcell R hRscale)
      (Real.rpow_nonneg (by norm_num) _))
  have hroot : H ≤ Real.rpow 3 (2 * u * (n : ℝ)) *
      observationScaleCellErrorSup M L m hu omega := by
    dsimp [H]
    have hscale' : m - ((r : ℤ) + (n : ℤ)) = L - (n : ℤ) := by
      simpa only [Nat.cast_add] using hscale
    rw [hscale']
    change Ch02.finsetSupReal (descendantsAtScale Q (L - (n : ℤ)))
      (fun S => Ch02.normalizedBlockResponseMax S a a0) ≤ _
    refine Ch02.finsetSupReal_le _
      (descendantsAtScale_nonempty Q
        ((sub_le_self L (by exact_mod_cast Nat.zero_le n)).trans (by simpa [Q] using! hLm))) ?_
    intro S hS
    obtain ⟨R, hR, hSR⟩ := exists_mem_descendantsAtScale_split
      (Q := Q) (k := L) (l := L - (n : ℤ)) (by simpa [Q] using! hLm)
      (sub_le_self L (by exact_mod_cast Nat.zero_le n)) hS
    have hSRle :=
      Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        a a0 hSR
    have hRle := hpoint R (by simpa [D] using hR)
    have hsup : cutoffCellErrorSq M L hu R omega ≤
        observationScaleCellErrorSup M L m hu omega := by
      apply le_csSup
      · exact ((Set.toFinite _).image fun T => cutoffCellErrorSq M L hu T omega).bddAbove
      · exact ⟨R, by simpa [observationScaleCellErrorSup, D, Q] using hR, rfl⟩
    exact hSRle.trans (hRle.trans (mul_le_mul_of_nonneg_left hsup
      (Real.rpow_nonneg (by norm_num) _)))
  have hweight : 0 ≤ Ch02.geometricWeight t 2 (r + n) := by
    simpa [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg (r + n)
        (by positivity : 0 ≤ t * (2 : ℝ))
  have hmul := mul_le_mul_of_nonneg_left hroot hweight
  simpa only [observationScaleErrorLayerRaw, r, H, Q, a, a0, mul_assoc] using hmul

private theorem collapseSummand {s t q : ℝ} (n : ℕ) :
    Ch02.geometricWeight t q n *
        ((3 : ℝ) ^ (2 * s * (n : ℝ))) ^ (q / 2) =
      Ch02.geometricDiscount t q *
        ((3 : ℝ) ^ (-((t - s) * q))) ^ n := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  unfold Ch02.geometricWeight
  simp only [Real.rpow_eq_pow]
  rw [mul_assoc, ← Real.rpow_mul h3.le,
    ← Real.rpow_natCast ((3 : ℝ) ^ (-((t - s) * q))) n,
    ← Real.rpow_mul h3.le, ← Real.rpow_add h3]
  congr 2
  ring

private theorem summable_geometricWeight_rpow {s t q : ℝ}
    (hst : s < t) (hq : 0 < q) :
    Summable (fun n : ℕ => Ch02.geometricWeight t q n *
      ((3 : ℝ) ^ (2 * s * (n : ℝ))) ^ (q / 2)) := by
  refine (Summable.congr ?_ (fun n => (collapseSummand (s := s) (t := t) (q := q) n).symm))
  exact (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_iff_pos.mpr (mul_pos (by linarith) hq)))).mul_left _

private theorem tsum_geometricWeight_rpow {s t q : ℝ}
    (hst : s < t) (hq : 0 < q) :
    (∑' n : ℕ, Ch02.geometricWeight t q n *
        ((3 : ℝ) ^ (2 * s * (n : ℝ))) ^ (q / 2)) =
      Ch02.geometricDiscount t q *
        (1 - (3 : ℝ) ^ (-((t - s) * q)))⁻¹ := by
  have hrPos : 0 < (3 : ℝ) ^ (-((t - s) * q)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrLt : (3 : ℝ) ^ (-((t - s) * q)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_iff_pos.mpr (mul_pos (by linarith) hq))
  rw [tsum_congr (fun n => collapseSummand (s := s) (t := t) (q := q) n),
    tsum_mul_left, tsum_geometric_of_lt_one hrPos.le hrLt]

private theorem observationScaleFineTailRaw_le_cellErrorSup
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {t u : ℝ} (hu : 0 < u) (hut : u < t)
    (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      cutoffCellErrorRawSq M L u R omega ≤ cutoffCellErrorSq M L hu R omega) :
    observationScaleFineTailRaw M L m t omega ≤
      Real.rpow 3 (-(2 * t * (Int.toNat (m - L) : ℝ))) *
        (Ch02.geometricDiscount t 2 *
          (1 - (3 : ℝ) ^ (-((t - u) * 2)))⁻¹) *
        observationScaleCellErrorSup M L m hu omega := by
  let Q := originCube d m
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  let r : ℕ := Int.toNat (m - L)
  let B : ℝ := observationScaleCellErrorSup M L m hu omega
  let g : ℕ → ℝ := fun n => observationScaleErrorLayerRaw M L m t (r + n) omega
  have ht : 0 < t := hu.trans hut
  have hfull := Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
    Q a a0 ht
  have hg : Summable g := by
    have htail := hfull.comp_injective (add_left_injective r)
    simpa only [g, observationScaleErrorLayerRaw, Q, a, a0, r,
      originCube, Function.comp_apply, Nat.add_comm]
      using! htail
  have hpoint : ∀ n, g n ≤ Ch02.geometricWeight t 2 (r + n) *
      Real.rpow 3 (2 * u * (n : ℝ)) * B := by
    intro n
    simpa only [g, B, r] using
      observationScaleErrorLayerRaw_fine_le_cellSup M L m hLm ht hu n omega hcell
  let A : ℝ := Real.rpow 3 (t * 2 * (r : ℝ))
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hweightShift (n : ℕ) :
      Ch02.geometricWeight t 2 (r + n) = A⁻¹ * Ch02.geometricWeight t 2 n := by
    calc
      Ch02.geometricWeight t 2 (r + n) = Ch02.geometricWeight t 2 (n + r) := by
        rw [Nat.add_comm]
      _ = 1 * Ch02.geometricWeight t 2 (n + r) := by rw [one_mul]
      _ = (A⁻¹ * A) * Ch02.geometricWeight t 2 (n + r) := by
        rw [inv_mul_cancel₀ hA.ne']
      _ = A⁻¹ * (A * Ch02.geometricWeight t 2 (n + r)) := by ring
      _ = A⁻¹ * Ch02.geometricWeight t 2 n := by
        congr 1
        simpa only [A, Ch02.geometricWeight_eq_old] using
          (HCPolySupport.geometricWeight_shift (s := t) (q := 2) r n).symm
  have hbase : Summable (fun n : ℕ => Ch02.geometricWeight t 2 n *
      Real.rpow 3 (2 * u * (n : ℝ))) := by
    simpa only [show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] using!
      (summable_geometricWeight_rpow (s := u) (t := t) (q := 2) hut (by norm_num))
  have hmajor : Summable (fun n : ℕ => Ch02.geometricWeight t 2 (r + n) *
      Real.rpow 3 (2 * u * (n : ℝ)) * B) := by
    refine ((hbase.mul_left (A⁻¹ * B)).congr fun n => ?_)
    rw [hweightShift]
    ring
  have hsum := Summable.tsum_le_tsum hpoint hg hmajor
  have hclosed : (∑' n : ℕ, Ch02.geometricWeight t 2 n *
      Real.rpow 3 (2 * u * (n : ℝ))) =
      Ch02.geometricDiscount t 2 *
        (1 - (3 : ℝ) ^ (-((t - u) * 2)))⁻¹ := by
    simpa only [show (2 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] using!
      (tsum_geometricWeight_rpow (s := u) (t := t) (q := 2) hut (by norm_num))
  have hmajorEq :
      (∑' n : ℕ, Ch02.geometricWeight t 2 (r + n) *
        Real.rpow 3 (2 * u * (n : ℝ)) * B) =
      A⁻¹ * (Ch02.geometricDiscount t 2 *
        (1 - (3 : ℝ) ^ (-((t - u) * 2)))⁻¹) * B := by
    calc
      (∑' n : ℕ, Ch02.geometricWeight t 2 (r + n) *
          Real.rpow 3 (2 * u * (n : ℝ)) * B) =
          (A⁻¹ * B) * ∑' n : ℕ, Ch02.geometricWeight t 2 n *
            Real.rpow 3 (2 * u * (n : ℝ)) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hweightShift]
        ring
      _ = A⁻¹ * (Ch02.geometricDiscount t 2 *
          (1 - (3 : ℝ) ^ (-((t - u) * 2)))⁻¹) * B := by
        rw [hclosed]
        ring
  have hAinv : A⁻¹ = Real.rpow 3 (-(2 * t * (r : ℝ))) := by
    dsimp [A]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  unfold observationScaleFineTailRaw
  change (∑' n : ℕ, g n) ≤ _
  rw [hmajorEq] at hsum
  simpa only [B, r, hAinv, mul_assoc] using hsum

private theorem cutoffHomogenizationErrorRaw_sq_le_finiteCover
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (hut : u < t)
    (omega : Cutoff.CutoffSample d)
    (hcell : ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
      cutoffCellErrorRawSq M L u R omega ≤ cutoffCellErrorSq M L hu R omega) :
    (Observable.cutoffHomogenizationErrorRaw M L m t
      (Annealed.sigmaBar M L) omega) ^ 2 ≤
      observationScaleCoarseEnvelope M L m t hu omega +
        Real.rpow 3 (-(2 * t * (Int.toNat (m - L) : ℝ))) *
          (Ch02.geometricDiscount t 2 *
            (1 - (3 : ℝ) ^ (-((t - u) * 2)))⁻¹) *
          observationScaleCellErrorSup M L m hu omega := by
  let r : ℕ := Int.toNat (m - L)
  let f : ℕ → ℝ := fun ell => observationScaleErrorLayerRaw M L m t ell omega
  let Q := originCube d m
  let a := Cutoff.coefficientCutoffTriadicCoeffFamily M L omega
  let a0 : HCPolySupport.Mat d :=
    Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)
  have hsum : Summable f := by
    simpa only [f, observationScaleErrorLayerRaw, Q, a, a0, originCube]
      using Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q a a0 ht
  have hsq :
      (Observable.cutoffHomogenizationErrorRaw M L m t
        (Annealed.sigmaBar M L) omega) ^ 2 = ∑' ell : ℕ, f ell := by
    rw [Observable.cutoffHomogenizationErrorRaw_characterization]
    simpa only [f, observationScaleErrorLayerRaw, Q, a, a0, originCube] using
      Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q ht a a0
  have hsplit :
      (Observable.cutoffHomogenizationErrorRaw M L m t
        (Annealed.sigmaBar M L) omega) ^ 2 =
        (∑ ell ∈ Finset.range r, f ell) + observationScaleFineTailRaw M L m t omega := by
    rw [hsq]
    symm
    simpa only [r, f, observationScaleFineTailRaw, Nat.add_comm] using
      hsum.sum_add_tsum_nat_add r
  have hprefix : (∑ ell ∈ Finset.range r, f ell) ≤
      observationScaleCoarseEnvelope M L m t hu omega := by
    unfold observationScaleCoarseEnvelope
    refine Finset.sum_le_sum fun ell hell => ?_
    exact observationScaleErrorLayerRaw_coarse_le_parentAverage
      M L m hLm ht hu ell (by simpa only [r] using Finset.mem_range.mp hell) omega hcell
  have hfine := observationScaleFineTailRaw_le_cellErrorSup
    M L m hLm hu hut omega hcell
  rw [hsplit]
  exact add_le_add hprefix hfine

private theorem cutoffHomogenizationErrorRepresentative_sq_ae_le_finiteCover
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (Observable.cutoffHomogenizationErrorRepresentative M L m
        (by norm_num : (0 : ℝ) < 1 / 8) (Annealed.sigmaBar M L) omega) ^ 2 ≤
        observationScaleCoarseEnvelope M L m (1 / 8) (by norm_num : (0 : ℝ) < 1 / 16)
            omega +
          Real.rpow 3 (-(2 * (1 / 8 : ℝ) * (Int.toNat (m - L) : ℝ))) *
            (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
              (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) *
            observationScaleCellErrorSup M L m (by norm_num : (0 : ℝ) < 1 / 16) omega := by
  have hall : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ R : HCPolySupport.TriadicCube d, R.scale = L →
        cutoffCellErrorRawSq M L (1 / 16) R omega =
          cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R omega := by
    rw [MeasureTheory.ae_all_iff]
    intro R
    by_cases hR : R.scale = L
    · filter_upwards [cutoffCellErrorRawSq_ae_eq_cutoffCellErrorSq
        M L (by norm_num : (0 : ℝ) < 1 / 16) R hR] with omega homega
      exact fun _ => homega
    · exact Filter.Eventually.of_forall fun _ h => (hR h).elim
  have htarget := Observable.cutoffHomogenizationErrorRaw_ae_eq_representative
    M L m (by norm_num : (0 : ℝ) < 1 / 8) (Annealed.sigmaBar M L)
  filter_upwards [hall, htarget] with omega hcell htargetOmega
  have hraw := cutoffHomogenizationErrorRaw_sq_le_finiteCover
    M L m hLm (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1 / 8)
      omega (fun R hR => (hcell R hR).le)
  simpa only [htargetOmega] using hraw

/-! ## Probabilistic aggregation over the finite cover -/

omit [NeZero d] in
private theorem descendantsAverage_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : HCPolySupport.TriadicCube d) (j : ℕ)
    (X : HCPolySupport.TriadicCube d → Omega → ℝ)
    (hX : ∀ R, Measurable (X R)) :
    Measurable (fun omega => descendantsAverage Q j (fun R => X R omega)) := by
  unfold descendantsAverage
  exact measurable_const.mul (Finset.measurable_sum _ fun R _ => hX R)

omit [NeZero d] in
private theorem observationScaleCoarseParentAverage_measurable
    (M : ABKModel d) (L m : ℤ) {u : ℝ} (hu : 0 < u) (ell : ℕ) :
    Measurable (observationScaleCoarseParentAverage M L m hu ell)  := by
  let D := descendantsAtScale (originCube d m) (m - (ell : ℤ))
  have hk : m - (ell : ℤ) ≤ (originCube d m).scale := by
    change m - (ell : ℤ) ≤ m
    exact sub_le_self m (by exact_mod_cast Nat.zero_le ell)
  have hD : D.Nonempty := descendantsAtScale_nonempty _ hk
  let X : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ := fun P omega =>
    descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
      (fun R => cutoffCellErrorSq M L hu R omega)
  have hsup : Measurable (fun omega => D.sup' hD (fun P => X P omega)) :=
    Probability.measurable_finset_sup' hD fun P _ =>
      descendantsAverage_measurable P _ _ fun R =>
        measurable_cutoffCellErrorSq M L hu R
  have heq : (fun omega => D.sup' hD (fun P => X P omega)) =
      observationScaleCoarseParentAverage M L m hu ell := by
    funext omega
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' D hD
      (fun P => X P omega)).symm
  rwa [← heq]

omit [NeZero d] in
private theorem descendantsAverage_isBigOWith_gammaQuarter
    (M : ABKModel d) (L : ℤ) (P : HCPolySupport.TriadicCube d)
    (j : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
      (fun omega => descendantsAverage P j
        (fun R => cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R omega))
      (gammaTriangleConst (1 / 4) *
        (twoTermSquareConst * (A ^ 2 + B ^ 2)))  := by
  let D := descendantsAtDepth P j
  let delta : ℝ := twoTermSquareConst * (A ^ 2 + B ^ 2)
  have hdelta : 0 < delta := by
    exact mul_pos (lt_of_lt_of_le zero_lt_one one_le_twoTermSquareConst)
      (add_pos (sq_pos_of_pos hA) (sq_pos_of_pos hB))
  have htail : ∀ R ∈ D, IsBigO (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 4))
      (cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R) delta := by
    intro R _
    rw [← Orlicz.isBigOWith_iff_isBigO_of_nonneg
      (cutoffCellErrorSq_nonneg M L (by norm_num : (0 : ℝ) < 1 / 16) R)]
    exact cutoffCellErrorSq_isBigOWith_gammaQuarter
      M L (by norm_num : (0 : ℝ) < 1 / 16) R hLower
  have haverage := Ch04.isBigO_finsetAverage_of_isBigO_gammaSigma_aemeasurable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) D
    (X := fun R => cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R)
    (a := fun _ => delta) (σ := (1 / 4 : ℝ))
    (by norm_num) (descendantsAtDepth_nonempty P j)
    (fun _ _ => hdelta) htail
    (fun R => (measurable_cutoffCellErrorSq M L
      (by norm_num : (0 : ℝ) < 1 / 16) R).aemeasurable)
  have hscale : ((D.card : ℝ)⁻¹) * ∑ _ ∈ D, delta = delta := by
    have hcard : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast (descendantsAtDepth_nonempty P j).card_ne_zero
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hnonneg : ∀ omega, 0 ≤ descendantsAverage P j
      (fun R => cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R omega) :=
    fun omega => descendantsAverage_nonneg P j _ fun R _ =>
      cutoffCellErrorSq_nonneg M L (by norm_num : (0 : ℝ) < 1 / 16) R omega
  apply (Orlicz.isBigOWith_iff_isBigO_of_nonneg hnonneg).2
  simpa only [descendantsAverage, D, hscale,
    twoTermSquareConst] using! haverage

omit [NeZero d] in
private theorem coarseParentAverage_isBigOWith_gammaQuarter (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    (ell : ℕ) (hell : ell < Int.toNat (m - L))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
      (observationScaleCoarseParentAverage M L m
        (by norm_num : (0 : ℝ) < 1 / 16) ell)
      ((3 * max 1 (Real.log (((3 ^ d) ^ ell : ℕ) : ℝ))) ^ ((1 / 4 : ℝ)⁻¹) *
        (gammaTriangleConst (1 / 4) *
          (twoTermSquareConst * (A ^ 2 + B ^ 2))))  := by
  classical
  let D := descendantsAtScale (originCube d m) (m - (ell : ℤ))
  have hD : D.Nonempty := descendantsAtScale_nonempty _
    (sub_le_self m (by exact_mod_cast Nat.zero_le ell))
  have hDcard : D.card = (3 ^ d) ^ ell := by
    dsimp only [D]
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m)
      (sub_le_self m (by exact_mod_cast Nat.zero_le ell)), descendantsAtDepth_card]
    have hdepth : (m - (m - (ell : ℤ))).toNat = ell := by
      rw [sub_sub_cancel]
      exact_mod_cast Int.toNat_of_nonneg
        (show (0 : ℤ) ≤ (ell : ℤ) by exact_mod_cast Nat.zero_le ell)
    simpa only [originCube] using congrArg (fun n => (3 ^ d) ^ n) hdepth
  have hr : ((Int.toNat (m - L) : ℕ) : ℤ) = m - L :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hLm)
  have hellZ : (ell : ℤ) < m - L := by
    rw [← hr]
    exact_mod_cast hell
  let X : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ := fun P omega =>
    descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
      (fun R => cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R omega)
  have hX : ∀ P ∈ D, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 4)) (X P)
      (gammaTriangleConst (1 / 4) *
        (twoTermSquareConst * (A ^ 2 + B ^ 2))) := by
    intro P _
    exact descendantsAverage_isBigOWith_gammaQuarter M L P
      (Int.toNat (m - (ell : ℤ) - L)) hA hB hLower
  have hscaleNonneg : 0 ≤ gammaTriangleConst (1 / 4) *
      (twoTermSquareConst * (A ^ 2 + B ^ 2)) := by
    exact mul_nonneg gammaTriangleConst_pos.le
      (mul_nonneg (zero_le_one.trans one_le_twoTermSquareConst)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hmax := Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) D hD
    (X := X) (A := gammaTriangleConst (1 / 4) *
      (twoTermSquareConst * (A ^ 2 + B ^ 2)))
    (σ := (1 / 4 : ℝ)) (by norm_num) hscaleNonneg hX
  have hfun : (fun omega => D.sup' hD (fun P => X P omega)) =
      observationScaleCoarseParentAverage M L m
        (by norm_num : (0 : ℝ) < 1 / 16) ell := by
    funext omega
    change D.sup' hD (fun P => X P omega) = Ch02.finsetSupReal D (fun P => X P omega)
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' D hD
      (fun P => X P omega)).symm
  simpa only [hfun, hDcard] using hmax

/-- The dimension- and depth-dependent stochastic scale for the observation error. -/
def observationDepthScale (d ell : ℕ) : ℝ :=
  Ch02.geometricWeight (1 / 8) 2 ell *
    (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ)))) ^ ((1 / 4 : ℝ)⁻¹) *
    gammaTriangleConst (1 / 4)

private theorem observationDepthScale_pos (d ell : ℕ) :
    0 < observationDepthScale d ell := by
  unfold observationDepthScale
  have hweight : 0 < Ch02.geometricWeight (1 / 8) 2 ell := by
    rw [Ch02.geometricWeight_eq_old]
    exact HCPolySupport.geometricWeight_pos ell (by norm_num)
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : 0 < 3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ))) := by
    positivity
  exact mul_pos (mul_pos hweight (Real.rpow_pos_of_pos hbase _))
    gammaTriangleConst_pos

private theorem summable_observationDepthScale (d : ℕ) :
    Summable (observationDepthScale d) := by
  let r : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  have hr0 : 0 ≤ r := by
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have h0 : Summable (fun ell : ℕ => r ^ ell) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr)
  have h1 : Summable (fun ell : ℕ => (ell : ℝ) * r ^ ell) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)
  have h2 : Summable (fun ell : ℕ => (ell : ℝ) ^ 2 * r ^ ell) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr)
  have h3 : Summable (fun ell : ℕ => (ell : ℝ) ^ 3 * r ^ ell) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr)
  have h4 : Summable (fun ell : ℕ => (ell : ℝ) ^ 4 * r ^ ell) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hr)
  let c : ℝ := 1 + (d : ℝ) * Real.log 3
  let K : ℝ := Ch02.geometricDiscount (1 / 8) 2 * 81 * c ^ 4 *
    gammaTriangleConst (1 / 4)
  have hpoly := (((((h0.mul_left K).add (h1.mul_left (4 * K))).add
    (h2.mul_left (6 * K))).add (h3.mul_left (4 * K))).add (h4.mul_left K))
  refine hpoly.congr ?_
  intro ell
  unfold observationDepthScale
  have hinv : ((1 / 4 : ℝ)⁻¹) = 4 := by norm_num
  have hpow4 : Real.rpow
      (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ))))
      ((1 / 4 : ℝ)⁻¹) =
      (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ)))) ^ (4 : ℕ) := by
    rw [hinv]
    exact Real.rpow_natCast _ 4
  change _ = Ch02.geometricWeight (1 / 8) 2 ell *
    Real.rpow (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ))))
      ((1 / 4 : ℝ)⁻¹) * gammaTriangleConst (1 / 4)
  rw [hpow4]
  unfold Ch02.geometricWeight
  have hrpow : Real.rpow (3 : ℝ) (-(1 / 8 : ℝ) * 2 * (ell : ℝ)) = r ^ ell := by
    rw [← Real.rpow_natCast r ell]
    dsimp only [r]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hrpow]
  change K * r ^ ell + 4 * K * ((ell : ℝ) * r ^ ell) +
      6 * K * ((ell : ℝ) ^ 2 * r ^ ell) +
      4 * K * ((ell : ℝ) ^ 3 * r ^ ell) +
      K * ((ell : ℝ) ^ 4 * r ^ ell) =
    Ch02.geometricDiscount (1 / 8) 2 * r ^ ell *
      (3 * (c * (1 + (ell : ℝ)))) ^ (4 : ℕ) * gammaTriangleConst (1 / 4)
  dsimp only [K]
  let z : ℝ := r ^ ell
  let x : ℝ := ell
  change Ch02.geometricDiscount (1 / 8) 2 * 81 * c ^ 4 *
        gammaTriangleConst (1 / 4) * z +
      4 * (Ch02.geometricDiscount (1 / 8) 2 * 81 * c ^ 4 *
        gammaTriangleConst (1 / 4)) * (x * z) +
      6 * (Ch02.geometricDiscount (1 / 8) 2 * 81 * c ^ 4 *
        gammaTriangleConst (1 / 4)) * (x ^ 2 * z) +
      4 * (Ch02.geometricDiscount (1 / 8) 2 * 81 * c ^ 4 *
        gammaTriangleConst (1 / 4)) * (x ^ 3 * z) +
      Ch02.geometricDiscount (1 / 8) 2 * 81 * c ^ 4 *
        gammaTriangleConst (1 / 4) * (x ^ 4 * z) =
    Ch02.geometricDiscount (1 / 8) 2 * z *
      (3 * (c * (1 + x))) ^ (4 : ℕ) * gammaTriangleConst (1 / 4)
  have hfactor : 3 * (c * (1 + x)) = (3 * c) * (1 + x) := by ring
  rw [hfactor, mul_pow]
  norm_num
  ring

private theorem coarseEnvelope_isBigOWith_gammaQuarter
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
      (observationScaleCoarseEnvelope M L m (1 / 8)
        (by norm_num : (0 : ℝ) < 1 / 16))
      (gammaTriangleConst (1 / 4) *
        ((∑' ell : ℕ, observationDepthScale d ell) *
          (twoTermSquareConst * (A ^ 2 + B ^ 2)))) := by
  let r : ℕ := Int.toNat (m - L)
  let X : ℕ → Cutoff.CutoffSample d → ℝ := fun ell omega =>
    if ell < r then
      Ch02.geometricWeight (1 / 8) 2 ell *
        observationScaleCoarseParentAverage M L m
          (by norm_num : (0 : ℝ) < 1 / 16) ell omega
    else 0
  let delta : ℝ := twoTermSquareConst * (A ^ 2 + B ^ 2)
  let scale : ℕ → ℝ := fun ell => observationDepthScale d ell * delta
  have hdelta : 0 < delta := mul_pos
    (lt_of_lt_of_le zero_lt_one one_le_twoTermSquareConst)
    (add_pos (sq_pos_of_pos hA) (sq_pos_of_pos hB))
  have hXnonneg : ∀ ell omega, 0 ≤ X ell omega := by
    intro ell omega
    dsimp only [X]
    split_ifs
    · have hweight : 0 ≤ Ch02.geometricWeight (1 / 8) 2 ell := by
        rw [Ch02.geometricWeight_eq_old]
        exact HCPolySupport.geometricWeight_nonneg ell (by norm_num)
      exact mul_nonneg hweight (by
        apply Ch02.finsetSupReal_nonneg
        intro P _
        exact descendantsAverage_nonneg P _ _ fun R _ =>
          cutoffCellErrorSq_nonneg M L
            (by norm_num : (0 : ℝ) < 1 / 16) R omega)
    · norm_num
  have hXmeas : ∀ ell, Measurable (X ell) := by
    intro ell
    dsimp only [X]
    split_ifs with hell
    · exact measurable_const.mul
        (observationScaleCoarseParentAverage_measurable M L m
          (by norm_num : (0 : ℝ) < 1 / 16) ell)
    · exact measurable_const
  have hscalePos : ∀ ell, 0 < scale ell := fun ell =>
    mul_pos (observationDepthScale_pos d ell) hdelta
  have hscaleSum : Summable scale :=
    (summable_observationDepthScale d).mul_right delta
  have hXtail : ∀ ell, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 4)) (X ell) (scale ell) := by
    intro ell
    dsimp only [X]
    split_ifs with hell
    · have hparent := coarseParentAverage_isBigOWith_gammaQuarter
        M L m hLm ell hell hA hB hLower
      have hweight : 0 ≤ Ch02.geometricWeight (1 / 8) 2 ell := by
        rw [Ch02.geometricWeight_eq_old]
        exact HCPolySupport.geometricWeight_nonneg ell (by norm_num)
      have hmul := hparent.const_mul hweight
      have hlog := Algsuperdiff.Probability.max_log_three_pow_le d ell
      have hbase0 : 0 ≤ 3 * max 1 (Real.log (((3 ^ d) ^ ell : ℕ) : ℝ)) :=
        mul_nonneg (by norm_num) ((zero_le_one.trans (le_max_left _ _)))
      have hbaseLe : 3 * max 1 (Real.log (((3 ^ d) ^ ell : ℕ) : ℝ)) ≤
          3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      have hpowLe := Real.rpow_le_rpow hbase0 hbaseLe
        (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 1 / 4))
      apply hmul.mono_scale
      dsimp only [scale, observationDepthScale, delta]
      have hweight0 : 0 ≤ Ch02.geometricWeight (1 / 8) 2 ell := by
        simpa [Ch02.geometricWeight_eq_old] using
          HCPolySupport.geometricWeight_nonneg ell
            (by norm_num : 0 ≤ (1 / 8 : ℝ) * 2)
      have hrest0 : 0 ≤ gammaTriangleConst (1 / 4) *
          (twoTermSquareConst * (A ^ 2 + B ^ 2)) :=
        mul_nonneg gammaTriangleConst_pos.le hdelta.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowLe hweight0) hrest0
    · have hpositive := hscalePos ell
      intro t ht
      have hthreshold : 0 < scale ell * t :=
        mul_pos hpositive (zero_lt_one.trans_le ht)
      have hempty : upperTailEvent (fun _ : Cutoff.CutoffSample d => (0 : ℝ))
          (scale ell * t) = ∅ := by
        ext omega
        simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false]
        exact not_lt.mpr hthreshold.le
      rw [hempty]
      exact measureReal_empty.trans_le
        (inv_nonneg.mpr (Real.exp_pos (t ^ (1 / 4 : ℝ))).le)
  have hsumTail := Orlicz.isBigOWith_gammaSigma_tsum
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (σ := (1 / 4 : ℝ)) (by norm_num) hXnonneg hXmeas hscalePos hscaleSum hXtail
  have hfun : (fun omega => ∑' ell, X ell omega) =
      observationScaleCoarseEnvelope M L m (1 / 8)
        (by norm_num : (0 : ℝ) < 1 / 16) := by
    funext omega
    have hfinite : (∑' ell, X ell omega) = ∑ ell ∈ Finset.range r, X ell omega := by
      exact tsum_eq_sum (s := Finset.range r) fun ell hell => by
        rw [Finset.mem_range, not_lt] at hell
        simp [X, hell]
    rw [hfinite]
    unfold observationScaleCoarseEnvelope
    apply Finset.sum_congr rfl
    intro ell hell
    simp [X, Finset.mem_range.mp hell]
  have hscaleEq : (∑' ell, scale ell) =
      (∑' ell, observationDepthScale d ell) * delta := by
    exact tsum_mul_right
  simpa only [hfun, hscaleEq, delta, mul_assoc] using hsumTail

omit [NeZero d] in
private theorem observationScaleCellErrorSup_isBigOWith_gammaQuarter
    (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {A B : ℝ}
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
      (observationScaleCellErrorSup M L m
        (by norm_num : (0 : ℝ) < 1 / 16))
      ((3 * max 1
          (Real.log (((3 ^ d) ^ Int.toNat (m - L) : ℕ) : ℝ))) ^
        ((1 / 4 : ℝ)⁻¹) *
        (twoTermSquareConst * (A ^ 2 + B ^ 2)))  := by
  classical
  let D := descendantsAtScale (originCube d m) L
  have hD : D.Nonempty := descendantsAtScale_nonempty _ hLm
  have hDcard : D.card = (3 ^ d) ^ Int.toNat (m - L) := by
    dsimp only [D]
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hLm,
      descendantsAtDepth_card]
    rfl
  have htail : ∀ R ∈ D, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 4))
      (cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R)
      (twoTermSquareConst * (A ^ 2 + B ^ 2)) := by
    intro R _
    exact cutoffCellErrorSq_isBigOWith_gammaQuarter
      M L (by norm_num : (0 : ℝ) < 1 / 16) R hLower
  have hscale : 0 ≤ twoTermSquareConst * (A ^ 2 + B ^ 2) :=
    mul_nonneg (zero_le_one.trans one_le_twoTermSquareConst)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmax := Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) D hD
    (X := fun R => cutoffCellErrorSq M L
      (by norm_num : (0 : ℝ) < 1 / 16) R)
    (A := twoTermSquareConst * (A ^ 2 + B ^ 2))
    (σ := (1 / 4 : ℝ)) (by norm_num) hscale htail
  have hfun : (fun omega => D.sup' hD (fun R =>
      cutoffCellErrorSq M L (by norm_num : (0 : ℝ) < 1 / 16) R omega)) =
      observationScaleCellErrorSup M L m
        (by norm_num : (0 : ℝ) < 1 / 16) := by
    funext omega
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' D hD
      (fun R => cutoffCellErrorSq M L
        (by norm_num : (0 : ℝ) < 1 / 16) R omega)).symm
  simpa only [hfun, hDcard] using hmax

/-- The geometric depth factor bounding the fine part of the observation error. -/
def observationScaleFineDepthFactor (d r : ℕ) : ℝ :=
  Real.rpow 3 (-(2 * (1 / 8 : ℝ) * (r : ℝ))) *
    (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
      (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) *
    (3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (r : ℝ)))) ^
      ((1 / 4 : ℝ)⁻¹)

private theorem observationScaleFineDepthFactor_pos (d r : ℕ) :
    0 < observationScaleFineDepthFactor d r := by
  unfold observationScaleFineDepthFactor
  have hdiscount : 0 < Ch02.geometricDiscount (1 / 8 : ℝ) 2 := by
    rw [Ch02.geometricDiscount_eq_old]
    exact HCPolySupport.geometricDiscount_pos (by norm_num)
  have hgap : 0 < 1 - (3 : ℝ) ^
      (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 3) (by norm_num :
        -(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2) < 0)
    linarith
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hbase : 0 < 3 *
      ((1 + (d : ℝ) * Real.log 3) * (1 + (r : ℝ))) := by
    positivity
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (mul_pos hdiscount (inv_pos.mpr hgap))) (Real.rpow_pos_of_pos hbase _)

private theorem summable_observationScaleFineDepthFactor (d : ℕ) :
    Summable (observationScaleFineDepthFactor d) := by
  let C : ℝ := (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
      (1 - (3 : ℝ) ^ (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) /
    (Ch02.geometricDiscount (1 / 8 : ℝ) 2 * gammaTriangleConst (1 / 4))
  have heq : observationScaleFineDepthFactor d =
      fun r => C * observationDepthScale d r := by
    funext r
    unfold observationScaleFineDepthFactor observationDepthScale
    rw [Ch02.geometricWeight]
    have htri : gammaTriangleConst (1 / 4) ≠ 0 := gammaTriangleConst_pos.ne'
    have hdisc : Ch02.geometricDiscount (1 / 8 : ℝ) 2 ≠ 0 := by
      rw [Ch02.geometricDiscount_eq_old]
      exact (HCPolySupport.geometricDiscount_pos (by norm_num)).ne'
    dsimp only [C]
    field_simp
  rw [heq]
  exact (summable_observationDepthScale d).mul_left C

omit [NeZero d] in
private theorem fineCoverTerm_isBigOWith_gammaQuarter (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {A B : ℝ}
    (hLower : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4))
      (fun omega =>
        Real.rpow 3 (-(2 * (1 / 8 : ℝ) * (Int.toNat (m - L) : ℝ))) *
          (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
            (1 - (3 : ℝ) ^
              (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) *
          observationScaleCellErrorSup M L m
            (by norm_num : (0 : ℝ) < 1 / 16) omega)
      (observationScaleFineDepthFactor d (Int.toNat (m - L)) *
        (twoTermSquareConst * (A ^ 2 + B ^ 2)))  := by
  have hsup := observationScaleCellErrorSup_isBigOWith_gammaQuarter
    M L m hLm hLower
  have hcoef : 0 ≤ Real.rpow 3
      (-(2 * (1 / 8 : ℝ) * (Int.toNat (m - L) : ℝ))) *
      (Ch02.geometricDiscount (1 / 8 : ℝ) 2 *
        (1 - (3 : ℝ) ^
          (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹) := by
    have hdiscount : 0 ≤ Ch02.geometricDiscount (1 / 8 : ℝ) 2 := by
      rw [Ch02.geometricDiscount_eq_old]
      exact (HCPolySupport.geometricDiscount_pos (by norm_num)).le
    have hgap : 0 ≤ (1 - (3 : ℝ) ^
        (-(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2)))⁻¹ := by
      apply inv_nonneg.mpr
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by norm_num :
          -(((1 / 8 : ℝ) - (1 / 16 : ℝ)) * 2) < 0)
      linarith
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      (mul_nonneg hdiscount hgap)
  have hscaled := hsup.const_mul hcoef
  have hlog := Algsuperdiff.Probability.max_log_three_pow_le d
    (Int.toNat (m - L))
  have hbase0 : 0 ≤ 3 * max 1
      (Real.log (((3 ^ d) ^ Int.toNat (m - L) : ℕ) : ℝ)) :=
    mul_nonneg (by norm_num) ((zero_le_one.trans (le_max_left _ _)))
  have hbaseLe : 3 * max 1
      (Real.log (((3 ^ d) ^ Int.toNat (m - L) : ℕ) : ℝ)) ≤
      3 * ((1 + (d : ℝ) * Real.log 3) *
        (1 + (Int.toNat (m - L) : ℝ))) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have hpowLe := Real.rpow_le_rpow hbase0 hbaseLe
    (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  apply hscaled.mono_scale
  unfold observationScaleFineDepthFactor
  have hdelta : 0 ≤ twoTermSquareConst * (A ^ 2 + B ^ 2) :=
    mul_nonneg (zero_le_one.trans one_le_twoTermSquareConst)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpowLe hcoef) hdelta

/-- The common constant for the observation-scale finite-cover estimate. -/
def observationScaleFiniteCoverConst (d : ℕ) : ℝ :=
  1 + 2 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
    twoTermSquareConst *
      (gammaTriangleConst (1 / 4) *
          (∑' r : ℕ, observationDepthScale d r) +
        ∑' r : ℕ, observationScaleFineDepthFactor d r)

private theorem one_le_observationScaleFiniteCoverConst (d : ℕ) :
    1 ≤ observationScaleFiniteCoverConst d := by
  unfold observationScaleFiniteCoverConst
  have hdepth : 0 ≤ ∑' r : ℕ, observationDepthScale d r :=
    tsum_nonneg fun r => (observationDepthScale_pos d r).le
  have hfine : 0 ≤ ∑' r : ℕ, observationScaleFineDepthFactor d r :=
    tsum_nonneg fun r => (observationScaleFineDepthFactor_pos d r).le
  have hsum : 0 ≤ gammaTriangleConst (1 / 4) *
      (∑' r : ℕ, observationDepthScale d r) +
      ∑' r : ℕ, observationScaleFineDepthFactor d r :=
    add_nonneg (mul_nonneg gammaTriangleConst_pos.le hdepth) hfine
  exact le_add_of_nonneg_right (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by positivity) _))
      (zero_le_one.trans one_le_twoTermSquareConst)) hsum)

/-- Dimension-only finite-cover transport of the lower homogenization-error
clause from the cutoff cube at `1/16` to the observation cube at `1/8`.

The legal-window premise only specializes the displayed lower clause; the
constant is chosen before the model, induction scale, and amplitude parameter.
This is a Provider endpoint and carries no source-node status by itself. -/
theorem observationScaleFiniteCover_sq_isBigOWith_gammaQuarter
    (d : ℕ) :
    ∃ Cobs : ℝ, 1 ≤ Cobs ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
        ∀ L : ℤ, L ≤ m - 1 →
          let hd : NeZero d :=
            ⟨Nat.ne_of_gt
              (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
          IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma (1 / 4))
            (fun omega =>
              (@Observable.cutoffHomogenizationErrorRepresentative d hd M L m
                (1 / 8) (by norm_num : (0 : ℝ) < 1 / 8)
                (Annealed.sigmaBar M L) omega) ^ 2)
            (Cobs *
              (((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma) ^ 2 +
                (((1 / 16 : ℝ)⁻¹) ^ 2 *
                  Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ^ 2)) := by
  refine ⟨observationScaleFiniteCoverConst d,
    one_le_observationScaleFiniteCoverConst d, ?_⟩
  intro M m E hLower hWindow L hL
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hLm : L ≤ m := hL.trans (by omega)
  let A : ℝ := (E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma
  let B : ℝ := ((1 / 16 : ℝ)⁻¹) ^ 2 *
    Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one E.property)
      (inv_pos.mpr (by norm_num)))
      (Real.sqrt_pos.2 M.shellPrefix.gamma_pos)
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr (by norm_num))) (Real.exp_pos _)
  have hLowerL : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B := by
    simpa only [A, B] using hLower L hL (1 / 16) hWindow
  have hcoarse := coarseEnvelope_isBigOWith_gammaQuarter
    M L m hLm hA hB hLowerL
  have hfine := fineCoverTerm_isBigOWith_gammaQuarter
    M L m hLm hLowerL
  have hmerge := Tail.isBigOWith_gammaSigma_add_of_nonneg
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (σ := (1 / 4 : ℝ))
    (by norm_num)
    (mul_nonneg gammaTriangleConst_pos.le
      (mul_nonneg (tsum_nonneg fun r => (observationDepthScale_pos d r).le)
        (mul_nonneg (zero_le_one.trans one_le_twoTermSquareConst)
          (add_nonneg (sq_nonneg _) (sq_nonneg _)))))
    (mul_nonneg (observationScaleFineDepthFactor_pos d
      (Int.toNat (m - L))).le
      (mul_nonneg (zero_le_one.trans one_le_twoTermSquareConst)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))))
    hcoarse hfine
  have hdepthLe : observationScaleFineDepthFactor d (Int.toNat (m - L)) ≤
      ∑' r : ℕ, observationScaleFineDepthFactor d r := by
    have hsum := summable_observationScaleFineDepthFactor d
    have hsingleton := hsum.sum_le_tsum
      {Int.toNat (m - L)}
      (fun r _ => (observationScaleFineDepthFactor_pos d r).le)
    simpa using hsingleton
  have hscale : 2 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
      max
        (gammaTriangleConst (1 / 4) *
          ((∑' r : ℕ, observationDepthScale d r) *
            (twoTermSquareConst * (A ^ 2 + B ^ 2))))
        (observationScaleFineDepthFactor d (Int.toNat (m - L)) *
          (twoTermSquareConst * (A ^ 2 + B ^ 2))) ≤
      observationScaleFiniteCoverConst d * (A ^ 2 + B ^ 2) := by
    have hdelta : 0 ≤ A ^ 2 + B ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have htriDepth : 0 ≤ gammaTriangleConst (1 / 4) *
        (∑' r : ℕ, observationDepthScale d r) :=
      mul_nonneg gammaTriangleConst_pos.le
        (tsum_nonneg fun r => (observationDepthScale_pos d r).le)
    have hfineTotal : 0 ≤ ∑' r : ℕ, observationScaleFineDepthFactor d r :=
      tsum_nonneg fun r => (observationScaleFineDepthFactor_pos d r).le
    have hmax : max
        (gammaTriangleConst (1 / 4) *
          ((∑' r : ℕ, observationDepthScale d r) *
            (twoTermSquareConst * (A ^ 2 + B ^ 2))))
        (observationScaleFineDepthFactor d (Int.toNat (m - L)) *
          (twoTermSquareConst * (A ^ 2 + B ^ 2))) ≤
        (gammaTriangleConst (1 / 4) *
            (∑' r : ℕ, observationDepthScale d r) +
          ∑' r : ℕ, observationScaleFineDepthFactor d r) *
          (twoTermSquareConst * (A ^ 2 + B ^ 2)) := by
      apply max_le
      · nlinarith [mul_nonneg
          (mul_nonneg hfineTotal
            (zero_le_one.trans one_le_twoTermSquareConst)) hdelta]
      · have hmono := mul_le_mul_of_nonneg_right hdepthLe
          (mul_nonneg (zero_le_one.trans one_le_twoTermSquareConst) hdelta)
        nlinarith [mul_nonneg
          (mul_nonneg htriDepth
            (zero_le_one.trans one_le_twoTermSquareConst)) hdelta]
    unfold observationScaleFiniteCoverConst
    have hfac : 0 ≤ 2 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) := by
      positivity
    calc
      _ ≤ 2 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
          ((gammaTriangleConst (1 / 4) *
              (∑' r : ℕ, observationDepthScale d r) +
            ∑' r : ℕ, observationScaleFineDepthFactor d r) *
            (twoTermSquareConst * (A ^ 2 + B ^ 2))) :=
        mul_le_mul_of_nonneg_left hmax hfac
      _ ≤ (1 + 2 * (3 * max 1 (Real.log 2)) ^ ((1 / 4 : ℝ)⁻¹) *
          twoTermSquareConst *
            (gammaTriangleConst (1 / 4) *
                (∑' r : ℕ, observationDepthScale d r) +
              ∑' r : ℕ, observationScaleFineDepthFactor d r)) *
          (A ^ 2 + B ^ 2) := by
        nlinarith [hdelta]
  have hcover := Ch04.isBigOWith_of_ae_le
    (hmerge.mono_scale (by simpa only [mul_assoc] using hscale))
    (cutoffHomogenizationErrorRepresentative_sq_ae_le_finiteCover M L m hLm)
  simpa only [A, B] using hcover

end

end Algsuperdiff.Section3.Provider.Homogenization
