/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffCoarseBlockRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationErrorRaw
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.WidetildeTheta

/-!
# CutoffHomogenizationErrorRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Measurable cutoff homogenization-error representative

This module constructs the actual measurable provider for the literal
manuscript observable
`\mathcal E_{s,\infty,2}(\square_m; a_L, \sigma\operatorname{Id})`.

The construction has three deliberately separate layers:

* `cutoffHomogenizationErrorRaw` remains the literal CoarseGraining expression;
* one measurable full coarse-block matrix is selected for each cube, and the
  compact-sphere norm functional is applied to it;
* the countable geometric sum is selected with `A.mk`, with an explicit a.e.
  equality back to the literal expression.

The coefficient cutoff scale `L` and observed cube scale `m` are independent
arguments throughout.  In particular, no `L = m` specialization is hidden in
this measurable realization.
-/

namespace Algsuperdiff.Section3.Observable

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch04
open scoped BigOperators

noncomputable section

private theorem aemeasurable_finset_sup'
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S : Finset ι} (hS : S.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ S, AEMeasurable (f i) μ) :
    AEMeasurable (S.sup' hS f) μ :=
  Finset.sup'_induction (s := S) (H := hS) (f := f)
    (p := fun g => AEMeasurable g μ)
    (fun _ hf' _ hg' => hf'.sup hg')
    (fun i hi => hf i hi)

/-- The everywhere-defined normalized response functional of the common
measurable full coarse-block representative.  Off the physical event it is
still a norm of a continuous finite-dimensional functional, not an arbitrary
replacement. -/
noncomputable def cutoffNormalizedBlockResponseRepresentative {d : ℕ}
    (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (a0 : Mat d) : Cutoff.CutoffSample d → ℝ  :=
  fun omega => normalizedBlockResponseMaxRepresentativeFunctional a0
    (cutoffCoarseFullBlockRepresentative M coefficientScale Q omega)

theorem measurable_cutoffNormalizedBlockResponseRepresentative {d : ℕ}
    (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (a0 : Mat d) :
    Measurable (cutoffNormalizedBlockResponseRepresentative M coefficientScale Q a0)  :=
  (continuous_normalizedBlockResponseMaxRepresentativeFunctional a0).measurable.comp
    (measurable_cutoffCoarseFullBlockRepresentative M coefficientScale Q)

theorem cutoffNormalizedBlockResponseRepresentative_nonneg {d : ℕ}
    (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (a0 : Mat d) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffNormalizedBlockResponseRepresentative M coefficientScale Q a0 omega  := by
  exact norm_nonneg _

/-- On the physical cutoff coefficient, the raw full coarse matrix has nonnegative
normalized quadratic response on every exact CoarseGraining unit direction. -/
private theorem cutoff_rawCoarseBlock_normalizedQuadratic_nonneg
    {d : ℕ} [NeZero d] (M : ABKModel d) (coefficientScale : ℤ)
    (Q : TriadicCube d) (a0 : Mat d) (omega : Cutoff.CutoffSample d)
    (e : FullBlockVec d) :
    0 ≤ blockJQuadraticFullBlockMat
      (cutoffCoarseFullBlockRaw M coefficientScale Q omega)
      (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e))
      (ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)) := by
  let a := Cutoff.coefficientCutoff M.nu coefficientScale omega
  let F := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a
    (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M coefficientScale omega)
  let P := ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e)
  let Qv := ofFullBlockVec (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)
  have hlocal := Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField
    M coefficientScale omega
  calc
    0 ≤ Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q) P Qv :=
      Ch02.doubledResponseJ_nonneg _ _ _ _
    _ = blockJObservableCubeSetBlockVec Q P Qv a :=
      doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
        hlocal Q P Qv
    _ = blockJQuadraticFullBlockMat
        (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P Qv :=
      blockJObservable_eq_blockJQuadraticForm_of_uniformEllipticity
        hlocal Q P Qv

/-- At every fixed cube, the canonical full-matrix representative realizes
CoarseGraining's literal normalized response maximum almost everywhere. -/
theorem ae_normalizedBlockResponseMax_cutoff_eq_representative
    {d : ℕ} [NeZero d] (M : ABKModel d) (coefficientScale : ℤ)
    (Q : TriadicCube d) (a0 : Mat d) :
    (fun omega => Ch02.normalizedBlockResponseMax Q
      (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0) =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffNormalizedBlockResponseRepresentative M coefficientScale Q a0 := by
  filter_upwards [cutoffCoarseFullBlockMatrix_ae_eq_representative
    M coefficientScale Q] with omega hmatrix
  calc
    Ch02.normalizedBlockResponseMax Q
        (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0 =
        normalizedBlockResponseMaxFromFullCoarseBlock a0
          (cutoffCoarseFullBlockRaw M coefficientScale Q omega) :=
      normalizedBlockResponseMax_cutoff_eq_fromRawCoarseBlock M coefficientScale Q a0 omega
    _ = normalizedBlockResponseMaxRepresentativeFunctional a0
          (cutoffCoarseFullBlockRaw M coefficientScale Q omega) :=
      normalizedBlockResponseMaxFromFullCoarseBlock_eq_representativeFunctional_of_nonneg
        a0 _ (fun e _ =>
          cutoff_rawCoarseBlock_normalizedQuadratic_nonneg M coefficientScale Q a0 omega e)
    _ = cutoffNormalizedBlockResponseRepresentative M coefficientScale Q a0 omega := by
      simpa [cutoffNormalizedBlockResponseRepresentative] using
        congrArg (normalizedBlockResponseMaxRepresentativeFunctional a0) hmatrix

/-- A single probability-one event identifies the literal normalized maximum
with its common-coarse-block realization on *every* triadic cube.  This
countable consolidation is what licenses the later countable scale sum. -/
theorem ae_forall_normalizedBlockResponseMax_cutoff_eq_representative
    {d : ℕ} [NeZero d] (M : ABKModel d) (coefficientScale : ℤ) (a0 : Mat d) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ Q : TriadicCube d,
        Ch02.normalizedBlockResponseMax Q
          (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0 =
        cutoffNormalizedBlockResponseRepresentative M coefficientScale Q a0 omega :=
  MeasureTheory.ae_all_iff.2 fun Q =>
    ae_normalizedBlockResponseMax_cutoff_eq_representative M coefficientScale Q a0

/-- The finite descendant maximum formed from the canonical common-block
representatives. -/
noncomputable def cutoffMaxDescendantNormalizedBlockResponseRepresentative
    {d : ℕ} (M : ABKModel d) (coefficientScale : ℤ)
    (Q : TriadicCube d) (k : ℤ) (a0 : Mat d) : Cutoff.CutoffSample d → ℝ  :=
  fun omega => Ch02.finsetSupReal (descendantsAtScale Q k)
    (fun R => cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0 omega)

theorem aemeasurable_cutoffMaxDescendantNormalizedBlockResponseRepresentative
    {d : ℕ} (M : ABKModel d) (coefficientScale : ℤ)
    (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale) (a0 : Mat d) :
    AEMeasurable
      (cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale Q k a0)
      (Cutoff.cutoffSampleLaw M).toMeasure  := by
  classical
  let S := descendantsAtScale Q k
  have hS : S.Nonempty := descendantsAtScale_nonempty Q hk
  have hsup : AEMeasurable
      (S.sup' hS (fun R =>
        cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    refine aemeasurable_finset_sup' hS ?_
    intro R _
    exact (measurable_cutoffNormalizedBlockResponseRepresentative
      M coefficientScale R a0).aemeasurable
  have hfin : AEMeasurable
      (fun omega => Ch02.finsetSupReal S
        (fun R => cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0 omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    convert hsup using 1
    ext omega
    rw [Finset.sup'_apply]
    exact Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS
      (fun R => cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0 omega)
  simpa [cutoffMaxDescendantNormalizedBlockResponseRepresentative, S] using! hfin

theorem cutoffMaxDescendantNormalizedBlockResponseRepresentative_nonneg
    {d : ℕ} (M : ABKModel d) (coefficientScale : ℤ)
    (Q : TriadicCube d) (k : ℤ) (a0 : Mat d) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffMaxDescendantNormalizedBlockResponseRepresentative
      M coefficientScale Q k a0 omega  := by
  apply Ch02.finsetSupReal_nonneg
  intro R _
  exact cutoffNormalizedBlockResponseRepresentative_nonneg M coefficientScale R a0 omega

private theorem aemeasurable_tsum_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (term : ℕ → Ω → ℝ)
    (hmeas : ∀ n, AEMeasurable (term n) μ)
    (hnonneg : ∀ n omega, 0 ≤ term n omega) :
    AEMeasurable (fun omega => ∑' n, term n omega) μ := by
  have hnn : AEMeasurable (fun omega => ∑' n, (term n omega).toNNReal) μ :=
    AEMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun n =>
      (hmeas n).real_toNNReal
  have hnn := hnn.coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  apply tsum_congr
  intro n
  rw [Real.toNNReal_of_nonneg (hnonneg n omega)]
  rfl

/-- The nonnegative everywhere-defined finite-dimensional/countable-sum
functional before selecting its measurable modification. -/
noncomputable def cutoffHomogenizationErrorFunctional {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) : Cutoff.CutoffSample d → ℝ  :=
  fun omega => √(∑' l : ℕ,
    Ch02.geometricWeight s 2 l *
      cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale
        (originCube d domainScale)
        ((originCube d domainScale).scale - (l : ℤ))
        (isotropicComparatorMatrix sigma) omega)

private theorem cutoffHomogenizationErrorFunctional_term_nonneg {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) (l : ℕ) (omega : Cutoff.CutoffSample d) :
    0 ≤ Ch02.geometricWeight s 2 l *
      cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale
        (originCube d domainScale)
        ((originCube d domainScale).scale - (l : ℤ))
        (isotropicComparatorMatrix sigma) omega  := by
  refine mul_nonneg ?_ ?_
  · simpa [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg l (by positivity : 0 ≤ s * (2 : ℝ))
  · exact cutoffMaxDescendantNormalizedBlockResponseRepresentative_nonneg
      M coefficientScale (originCube d domainScale)
        ((originCube d domainScale).scale - (l : ℤ))
        (isotropicComparatorMatrix sigma) omega

theorem cutoffHomogenizationErrorFunctional_nonneg {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationErrorFunctional M coefficientScale domainScale s sigma omega  :=
  Real.sqrt_nonneg _

theorem aemeasurable_cutoffHomogenizationErrorFunctional {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) :
    AEMeasurable (cutoffHomogenizationErrorFunctional M coefficientScale domainScale s sigma)
      (Cutoff.cutoffSampleLaw M).toMeasure  := by
  have hterm : ∀ l : ℕ, AEMeasurable
      (fun omega => Ch02.geometricWeight s 2 l *
        cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale
          (originCube d domainScale)
          ((originCube d domainScale).scale - (l : ℤ))
          (isotropicComparatorMatrix sigma) omega)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro l
    apply (aemeasurable_cutoffMaxDescendantNormalizedBlockResponseRepresentative
      M coefficientScale (originCube d domainScale)
      ((originCube d domainScale).scale - (l : ℤ))
      (sub_le_self _ (by exact_mod_cast Nat.zero_le l))
      (isotropicComparatorMatrix sigma)).const_mul
  have hsum := aemeasurable_tsum_of_nonneg _ hterm
    (cutoffHomogenizationErrorFunctional_term_nonneg M coefficientScale domainScale hs sigma)
  exact Real.continuous_sqrt.measurable.comp_aemeasurable hsum

/-- The genuine measurable, nonnegative representative of the cutoff
homogenization error.  The `max 0` is not a fallback: it makes the canonical
measurable modification nonnegative everywhere, while the following theorem
records its precise a.e. identity with the nonnegative raw functional. -/
noncomputable def cutoffHomogenizationErrorRepresentative {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) : Cutoff.CutoffSample d → ℝ  :=
  fun omega => max 0 (AEMeasurable.mk
    (cutoffHomogenizationErrorFunctional M coefficientScale domainScale s sigma)
    (aemeasurable_cutoffHomogenizationErrorFunctional M coefficientScale domainScale
      hs sigma) omega)

theorem measurable_cutoffHomogenizationErrorRepresentative {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) :
    Measurable (cutoffHomogenizationErrorRepresentative M coefficientScale domainScale hs sigma)
       := by
  exact measurable_const.max
    (aemeasurable_cutoffHomogenizationErrorFunctional M coefficientScale domainScale
      hs sigma).measurable_mk

theorem cutoffHomogenizationErrorRepresentative_nonneg {d : ℕ}
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationErrorRepresentative M coefficientScale domainScale hs sigma omega  :=
  le_max_left _ _

theorem cutoffHomogenizationErrorFunctional_ae_eq_representative
    {d : ℕ} [NeZero d] (M : ABKModel d) (coefficientScale domainScale : ℤ)
    {s : ℝ} (hs : 0 < s) (sigma : PositiveScalar) :
    cutoffHomogenizationErrorFunctional M coefficientScale domainScale s sigma =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffHomogenizationErrorRepresentative M coefficientScale domainScale hs sigma := by
  filter_upwards
    [(aemeasurable_cutoffHomogenizationErrorFunctional M coefficientScale domainScale
      hs sigma).ae_eq_mk] with omega homega
  rw [cutoffHomogenizationErrorRepresentative, ← homega]
  exact (max_eq_right (cutoffHomogenizationErrorFunctional_nonneg
    M coefficientScale domainScale s sigma omega)).symm

/-- On the countable common event for all triadic cubes, the literal homogenization
error and the pre-selection finite-dimensional functional agree exactly.  The
proof uses CoarseGraining's squared `p = infinity`, `q = 2` identity and the
fact that both sides are nonnegative. -/
private theorem cutoffHomogenizationErrorRaw_eq_functional_on_common_event
    {d : ℕ} [NeZero d] (M : ABKModel d) (coefficientScale domainScale : ℤ)
    {s : ℝ} (hs : 0 < s) (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d)
    (hall : ∀ R : TriadicCube d,
      Ch02.normalizedBlockResponseMax R
        (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
        (isotropicComparatorMatrix sigma) =
      cutoffNormalizedBlockResponseRepresentative M coefficientScale R
        (isotropicComparatorMatrix sigma) omega) :
    cutoffHomogenizationErrorRaw M coefficientScale domainScale s sigma omega =
      cutoffHomogenizationErrorFunctional M coefficientScale domainScale s sigma omega := by
  let Q := originCube d domainScale
  let a0 : Mat d := isotropicComparatorMatrix sigma
  have hmax (l : ℕ) :
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ))
          (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0 =
        cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale Q
          (Q.scale - (l : ℤ)) a0 omega := by
    exact Ch02.finsetSupReal_congr _ fun R _ => hall R
  have hsum_eq :
      (∑' l : ℕ, Ch02.geometricWeight s 2 l *
        Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ))
          (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0) =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale Q
          (Q.scale - (l : ℤ)) a0 omega := by
    apply tsum_congr
    intro l
    exact congrArg (fun x => Ch02.geometricWeight s 2 l * x) (hmax l)
  have hrawsq :
      cutoffHomogenizationErrorRaw M coefficientScale domainScale s sigma omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ))
          (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0 := by
    rw [cutoffHomogenizationErrorRaw_characterization]
    exact Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs
      (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega) a0
  have hsum_nonneg : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight s 2 l *
      cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale Q
        (Q.scale - (l : ℤ)) a0 omega := by
    refine tsum_nonneg ?_
    intro l
    simpa [Q, a0] using cutoffHomogenizationErrorFunctional_term_nonneg
      M coefficientScale domainScale hs sigma l omega
  have hfuncsq :
      cutoffHomogenizationErrorFunctional M coefficientScale domainScale s sigma omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale Q
          (Q.scale - (l : ℤ)) a0 omega := by
    change (√(∑' l : ℕ, Ch02.geometricWeight s 2 l *
      cutoffMaxDescendantNormalizedBlockResponseRepresentative M coefficientScale Q
        (Q.scale - (l : ℤ)) a0 omega)) ^ 2 = _
    exact Real.sq_sqrt hsum_nonneg
  have hraw_nonneg := cutoffHomogenizationErrorRaw_nonneg
    M coefficientScale domainScale hs sigma omega
  have hfunctional_nonneg := cutoffHomogenizationErrorFunctional_nonneg
    M coefficientScale domainScale s sigma omega
  nlinarith [hrawsq, hfuncsq, hsum_eq]

/-- The genuine measurable representative is almost everywhere exactly the
literal manuscript observable
`\mathcal E_{s,\infty,2}(\square_m; a_L, \sigma\operatorname{Id})` under the
actual cutoff law.  This is the only semantic bridge consumers may use. -/
theorem cutoffHomogenizationErrorRaw_ae_eq_representative
    {d : ℕ} [NeZero d] (M : ABKModel d) (coefficientScale domainScale : ℤ)
    {s : ℝ} (hs : 0 < s) (sigma : PositiveScalar) :
    cutoffHomogenizationErrorRaw M coefficientScale domainScale s sigma =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffHomogenizationErrorRepresentative M coefficientScale domainScale hs sigma := by
  filter_upwards
    [ae_forall_normalizedBlockResponseMax_cutoff_eq_representative M coefficientScale
      (isotropicComparatorMatrix sigma),
      cutoffHomogenizationErrorFunctional_ae_eq_representative
        M coefficientScale domainScale hs sigma] with omega hall hrepresentative
  exact (cutoffHomogenizationErrorRaw_eq_functional_on_common_event
    M coefficientScale domainScale hs sigma omega hall).trans hrepresentative

end

end Algsuperdiff.Section3.Observable
