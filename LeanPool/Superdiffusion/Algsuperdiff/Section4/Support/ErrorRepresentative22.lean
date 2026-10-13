/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationErrorRepresentative

/-!
# ErrorRepresentative22

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The measurable `(2,2)` homogenization-error representative

`Algsuperdiff.Section4.Support.ErrorAtoms` records the *literal* `(2,2)`
observable `cutoffHomogenizationErrorRaw22` and the `𝒢₂` atom
`annularErrorAtom`.  Neither is measurable by composition: CoarseGraining's
`normalizedBlockResponseMax` is an `sSup` over the uncountable set of doubled
unit directions.  Section 3 solves this once and for all at `(∞,2)` in
`Observable/CutoffHomogenizationErrorRepresentative.lean`: one measurable full
coarse-block matrix is selected per cube, the compact-sphere norm functional is
applied to it, and the countable scale sum is selected with `A.mk` with an
explicit a.e. equality back to the literal.

This module is the `(2,2)` sibling of that construction.  Three of its four
layers are *reused verbatim* from the proved `(∞,2)` chain, because they are
exponent-independent: the coarse-block representative
(`cutoffCoarseFullBlockRepresentative`), its normalized response
(`cutoffNormalizedBlockResponseRepresentative`), and the single probability-one
event on which the literal maximum equals that response at *every* triadic cube
(`ae_forall_normalizedBlockResponseMax_cutoff_eq_representative`).

Only the scale aggregation changes.  At `p = ∞` CoarseGraining's
`scaleResponseAtScale` takes the descendant *maximum* (`finsetSupReal`); at `p
= 2` it takes the descendant *average* (`finsetAverageReal`) of the same
normalized maxima, with the inner exponent `p / 2 = 1`.  Consequently the
squared identity `homogenizationErrorOnCube_two_two_sq_eq_tsum` below is the
exact `(2,2)` sibling of CoarseGraining's
`Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum`
(`Book/Ch02/Theorems/HomogenizationError/Finite.lean`), and the finite average
of finitely many *genuinely* measurable representatives is measurable with no
`Finset.sup'` induction at all.

## Main definitions

* `cutoffAvgDescendantNormalizedBlockResponseRepresentative` — the descendant
  average of the common coarse-block responses.
* `cutoffHomogenizationErrorRepresentative22` — the genuine measurable
  nonnegative `(2,2)` representative.
* `annularErrorObservable` — the `𝒢₂` observable `𝓔_{s,2,2}(□_n; a_{n−2},
  σ_{n−2} Id)`.

## Main results

* `homogenizationErrorOnCube_two_two_sq_eq_tsum` — the `(2,2)` squared identity.
* `cutoffHomogenizationErrorRaw22_ae_eq_representative22` — the semantic bridge.
* `annularErrorAtom_ae_eq_annularErrorObservable` — the same bridge at the
  `𝒢₂` atom.

## References

* ABK26, `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Support

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The `(2,2)` squared identity -/

private theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = x := by
  simpa [Real.sqrt_eq_rpow] using Real.sq_sqrt hx

/-- The `p = 2` reading of `scaleResponseAtScale`: the finite branch at `p = 2`
has inner exponent `p / 2 = 1`, so the aggregated quantity is the plain
descendant *average* of the normalized block-response maxima. -/
private theorem scaleResponseAtScale_two_eq
    (Q : TriadicCube d) (k : ℤ) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    scaleResponseAtScale Q k (.finite 2) F a0 =
      (finsetAverageReal (descendantsAtScale Q k)
        (fun R => normalizedBlockResponseMax R F a0)) ^ ((1 : ℝ) / 2) := by
  have h : scaleResponseAtScale Q k (.finite 2) F a0 =
      (finsetAverageReal (descendantsAtScale Q k)
        (fun R => (normalizedBlockResponseMax R F a0) ^ ((2 : ℝ) / 2))) ^
        ((1 : ℝ) / 2) := rfl
  rw [h]
  simp only [show ((2 : ℝ) / 2) = 1 from by norm_num, Real.rpow_one]

private theorem finsetAverageReal_normalizedBlockResponseMax_nonneg
    (Q : TriadicCube d) (k : ℤ) (F : TriadicCoeffFamily d) (a0 : Mat d) :
    0 ≤ finsetAverageReal (descendantsAtScale Q k)
      (fun R => normalizedBlockResponseMax R F a0) :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun R _ => normalizedBlockResponseMax_nonneg R F a0)

/-- The `(2,2)` sibling of CoarseGraining's
`Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum`: after squaring, the
`q = 2` root disappears and `𝓔_{s,2,2}` is exactly the geometrically weighted
sum of the descendant *averages* of the normalized block-response maxima. -/
theorem homogenizationErrorOnCube_two_two_sq_eq_tsum
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (F : TriadicCoeffFamily d)
    (a0 : Mat d) :
    (HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0) ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ)))
          (fun R => normalizedBlockResponseMax R F a0) := by
  have hOn : HomogenizationErrorOnCube Q s (.finite 2) (.finite 2) F a0 =
      (∑' l : ℕ, Ch02.geometricWeight s 2 l *
        (scaleResponseAtScale Q (Q.scale - (l : ℤ)) (.finite 2) F a0) ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2) := rfl
  have hterm :
      (fun l : ℕ => Ch02.geometricWeight s 2 l *
          (scaleResponseAtScale Q (Q.scale - (l : ℤ)) (.finite 2) F a0) ^ (2 : ℝ)) =
        fun l : ℕ => Ch02.geometricWeight s 2 l *
          finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ)))
            (fun R => normalizedBlockResponseMax R F a0) := by
    funext l
    refine congrArg (fun x => Ch02.geometricWeight s 2 l * x) ?_
    rw [scaleResponseAtScale_two_eq,
      ← Real.rpow_mul (finsetAverageReal_normalizedBlockResponseMax_nonneg Q _ F a0),
      show (1 : ℝ) / 2 * 2 = 1 from by norm_num, Real.rpow_one]
  have hnonneg : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight s 2 l *
      finsetAverageReal (descendantsAtScale Q (Q.scale - (l : ℤ)))
        (fun R => normalizedBlockResponseMax R F a0) := by
    refine tsum_nonneg fun l => mul_nonneg ?_
      (finsetAverageReal_normalizedBlockResponseMax_nonneg Q _ F a0)
    simpa only [Ch02.geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
        (by positivity : 0 ≤ s * (2 : ℝ)))
  rw [hOn, hterm]
  exact rpow_half_sq hnonneg

/-! ## The descendant average of the common coarse-block responses -/

/-- The finite descendant *average* formed from the canonical common-block
representatives.  This is the only layer where the `(2,2)` chain differs from
the proved `(∞,2)` chain, which takes `Ch02.finsetSupReal` here. -/
noncomputable def cutoffAvgDescendantNormalizedBlockResponseRepresentative
     (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (k : ℤ) (a0 : Mat d) : Cutoff.CutoffSample d → ℝ :=
  fun omega => finsetAverageReal (descendantsAtScale Q k)
    (fun R => cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0 omega)

/-- The descendant average of genuinely measurable representatives is genuinely
measurable: a finite sum needs no `Finset.sup'` induction and no a.e.
qualification. -/
theorem measurable_cutoffAvgDescendantNormalizedBlockResponseRepresentative
     (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (k : ℤ) (a0 : Mat d) :
    Measurable
      (cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale Q k a0) := by
  have hEq :
      cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale Q k a0 =
        fun omega => ((descendantsAtScale Q k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k,
            cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0 omega :=
    rfl
  rw [hEq]
  exact measurable_const.mul (Finset.measurable_sum _ fun R _ =>
    measurable_cutoffNormalizedBlockResponseRepresentative M coefficientScale R a0)

theorem cutoffAvgDescendantNormalizedBlockResponseRepresentative_nonneg
     (M : ABKModel d) (coefficientScale : ℤ) (Q : TriadicCube d)
    (k : ℤ) (a0 : Mat d) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffAvgDescendantNormalizedBlockResponseRepresentative
      M coefficientScale Q k a0 omega :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun R _ =>
      cutoffNormalizedBlockResponseRepresentative_nonneg M coefficientScale R a0 omega)

/-! ## The `(2,2)` functional and its measurable representative -/

private theorem aemeasurable_tsum_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} (term : ℕ → Ω → ℝ)
    (hmeas : ∀ n, AEMeasurable (term n) mu)
    (hnonneg : ∀ n omega, 0 ≤ term n omega) :
    AEMeasurable (fun omega => ∑' n, term n omega) mu := by
  have hnn : AEMeasurable (fun omega => ∑' n, (term n omega).toNNReal) mu :=
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

/-- The nonnegative everywhere-defined countable-sum functional of the `(2,2)`
error, before selecting its measurable modification. -/
noncomputable def cutoffHomogenizationError22Functional
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) : Cutoff.CutoffSample d → ℝ :=
  fun omega => Real.sqrt (∑' l : ℕ, Ch02.geometricWeight s 2 l *
    cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
      (originCube d domainScale)
      ((originCube d domainScale).scale - (l : ℤ))
      (isotropicComparatorMatrix sigma) omega)

private theorem cutoffHomogenizationError22Functional_term_nonneg
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) (l : ℕ) (omega : Cutoff.CutoffSample d) :
    0 ≤ Ch02.geometricWeight s 2 l *
      cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
        (originCube d domainScale)
        ((originCube d domainScale).scale - (l : ℤ))
        (isotropicComparatorMatrix sigma) omega := by
  refine mul_nonneg ?_ ?_
  · simpa only [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg l (by positivity : 0 ≤ s * (2 : ℝ))
  · exact cutoffAvgDescendantNormalizedBlockResponseRepresentative_nonneg
      M coefficientScale (originCube d domainScale)
      ((originCube d domainScale).scale - (l : ℤ))
      (isotropicComparatorMatrix sigma) omega

theorem cutoffHomogenizationError22Functional_nonneg
    (M : ABKModel d) (coefficientScale domainScale : ℤ) (s : ℝ)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma omega :=
  Real.sqrt_nonneg _

theorem aemeasurable_cutoffHomogenizationError22Functional
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) :
    AEMeasurable
      (cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hterm : ∀ l : ℕ, AEMeasurable
      (fun omega => Ch02.geometricWeight s 2 l *
        cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
          (originCube d domainScale)
          ((originCube d domainScale).scale - (l : ℤ))
          (isotropicComparatorMatrix sigma) omega)
      (Cutoff.cutoffSampleLaw M).toMeasure := fun l =>
    ((measurable_cutoffAvgDescendantNormalizedBlockResponseRepresentative
      M coefficientScale (originCube d domainScale)
      ((originCube d domainScale).scale - (l : ℤ))
      (isotropicComparatorMatrix sigma)).const_mul _).aemeasurable
  have hsum := aemeasurable_tsum_of_nonneg _ hterm
    (cutoffHomogenizationError22Functional_term_nonneg
      M coefficientScale domainScale hs sigma)
  exact Real.continuous_sqrt.measurable.comp_aemeasurable hsum

/-- The genuine measurable, nonnegative representative of the `(2,2)` cutoff
homogenization error.  The `max 0` is not a fallback: it makes the canonical
measurable modification nonnegative everywhere, while
`cutoffHomogenizationErrorRaw22_ae_eq_representative22` records its precise
a.e. identity with the literal. -/
noncomputable def cutoffHomogenizationErrorRepresentative22
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) : Cutoff.CutoffSample d → ℝ :=
  fun omega => max 0 (AEMeasurable.mk
    (cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma)
    (aemeasurable_cutoffHomogenizationError22Functional M coefficientScale domainScale
      hs sigma) omega)

theorem measurable_cutoffHomogenizationErrorRepresentative22
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) :
    Measurable
      (cutoffHomogenizationErrorRepresentative22 M coefficientScale domainScale hs sigma) :=
  measurable_const.max
    (aemeasurable_cutoffHomogenizationError22Functional M coefficientScale domainScale
      hs sigma).measurable_mk

theorem cutoffHomogenizationErrorRepresentative22_nonneg
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationErrorRepresentative22 M coefficientScale domainScale hs sigma omega :=
  le_max_left _ _

theorem cutoffHomogenizationError22Functional_ae_eq_representative22 [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) :
    cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffHomogenizationErrorRepresentative22 M coefficientScale domainScale hs sigma := by
  filter_upwards
    [(aemeasurable_cutoffHomogenizationError22Functional M coefficientScale domainScale
      hs sigma).ae_eq_mk] with omega homega
  rw [cutoffHomogenizationErrorRepresentative22, ← homega]
  exact (max_eq_right (cutoffHomogenizationError22Functional_nonneg
    M coefficientScale domainScale s sigma omega)).symm

/-- On the countable common event for all triadic cubes, the literal `(2,2)`
error and the pre-selection functional agree exactly.  Both sides are
nonnegative and have the same square, by the `(2,2)` identity above. -/
private theorem cutoffHomogenizationErrorRaw22_eq_functional_on_common_event [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) (omega : Cutoff.CutoffSample d)
    (hall : ∀ R : TriadicCube d,
      normalizedBlockResponseMax R
        (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
        (isotropicComparatorMatrix sigma) =
      cutoffNormalizedBlockResponseRepresentative M coefficientScale R
        (isotropicComparatorMatrix sigma) omega) :
    cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma omega =
      cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma omega := by
  have hsum_eq :
      (∑' l : ℕ, Ch02.geometricWeight s 2 l *
        finsetAverageReal
          (descendantsAtScale (originCube d domainScale)
            ((originCube d domainScale).scale - (l : ℤ)))
          (fun R => normalizedBlockResponseMax R
            (Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega)
            (isotropicComparatorMatrix sigma))) =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
          (originCube d domainScale)
          ((originCube d domainScale).scale - (l : ℤ))
          (isotropicComparatorMatrix sigma) omega := by
    refine tsum_congr fun l => congrArg (fun x => Ch02.geometricWeight s 2 l * x) ?_
    exact congrArg (fun f => ((descendantsAtScale (originCube d domainScale)
        ((originCube d domainScale).scale - (l : ℤ))).card : ℝ)⁻¹ * f)
      (Finset.sum_congr rfl fun R _ => hall R)
  have hsum_nonneg : 0 ≤ ∑' l : ℕ, Ch02.geometricWeight s 2 l *
      cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
        (originCube d domainScale)
        ((originCube d domainScale).scale - (l : ℤ))
        (isotropicComparatorMatrix sigma) omega :=
    tsum_nonneg fun l => cutoffHomogenizationError22Functional_term_nonneg
      M coefficientScale domainScale hs sigma l omega
  have hrawsq :
      cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
          (originCube d domainScale)
          ((originCube d domainScale).scale - (l : ℤ))
          (isotropicComparatorMatrix sigma) omega := by
    rw [cutoffHomogenizationErrorRaw22_characterization,
      homogenizationErrorOnCube_two_two_sq_eq_tsum (originCube d domainScale) hs, hsum_eq]
  have hfuncsq :
      cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma omega ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 2 l *
        cutoffAvgDescendantNormalizedBlockResponseRepresentative M coefficientScale
          (originCube d domainScale)
          ((originCube d domainScale).scale - (l : ℤ))
          (isotropicComparatorMatrix sigma) omega :=
    Real.sq_sqrt hsum_nonneg
  have hraw_nonneg :=
    cutoffHomogenizationErrorRaw22_nonneg M coefficientScale domainScale hs sigma omega
  have hfun_nonneg :=
    cutoffHomogenizationError22Functional_nonneg M coefficientScale domainScale s sigma omega
  calc
    cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma omega =
        Real.sqrt
          (cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma omega ^ 2) :=
      (Real.sqrt_sq hraw_nonneg).symm
    _ = Real.sqrt
          (cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma
            omega ^ 2) := by rw [hrawsq, hfuncsq]
    _ = cutoffHomogenizationError22Functional M coefficientScale domainScale s sigma omega :=
      Real.sqrt_sq hfun_nonneg

/-- The genuine measurable `(2,2)` representative is almost everywhere exactly
the literal manuscript observable `𝓔_{s,2,2}(□_m; a_L, σ Id)` under the actual
cutoff law.  This is the only semantic bridge consumers may use. -/
theorem cutoffHomogenizationErrorRaw22_ae_eq_representative22 [NeZero d]
    (M : ABKModel d) (coefficientScale domainScale : ℤ) {s : ℝ} (hs : 0 < s)
    (sigma : PositiveScalar) :
    cutoffHomogenizationErrorRaw22 M coefficientScale domainScale s sigma =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      cutoffHomogenizationErrorRepresentative22 M coefficientScale domainScale hs sigma := by
  filter_upwards
    [ae_forall_normalizedBlockResponseMax_cutoff_eq_representative M coefficientScale
      (isotropicComparatorMatrix sigma),
      cutoffHomogenizationError22Functional_ae_eq_representative22
        M coefficientScale domainScale hs sigma] with omega hall hrepresentative
  exact (cutoffHomogenizationErrorRaw22_eq_functional_on_common_event
    M coefficientScale domainScale hs sigma omega hall).trans hrepresentative

/-! ## The public `𝒢₂` observable -/

/-- The paper-wide assumption `2 ≤ d`, stored in the model, supplies the
nonzero-dimension instance required by CoarseGraining's doubled-response A. -/
theorem neZero_of_model_ErrorRepresentative22 (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The translated atom at `z + □_n` is `annularErrorObservable M n s ∘
Cutoff.translateCutoffSample z` (resolution A4). -/
noncomputable def annularErrorObservable (M : ABKModel d) (n : ℤ)
    (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model_ErrorRepresentative22 M
  exact cutoffHomogenizationErrorRepresentative22 M (n - 2) n s.2
    (Annealed.sigmaBar M (n - 2))

theorem measurable_annularErrorObservable (M : ABKModel d) (n : ℤ)
    (s : {s : ℝ // 0 < s}) :
    Measurable (annularErrorObservable M n s) := by
  let : NeZero d := neZero_of_model_ErrorRepresentative22 M
  change Measurable (cutoffHomogenizationErrorRepresentative22 M (n - 2) n s.2
    (Annealed.sigmaBar M (n - 2)))
  exact measurable_cutoffHomogenizationErrorRepresentative22 M (n - 2) n s.2
    (Annealed.sigmaBar M (n - 2))

theorem annularErrorObservable_nonneg (M : ABKModel d) (n : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) :
    0 ≤ annularErrorObservable M n s omega := by
  let : NeZero d := neZero_of_model_ErrorRepresentative22 M
  change 0 ≤ cutoffHomogenizationErrorRepresentative22 M (n - 2) n s.2
    (Annealed.sigmaBar M (n - 2)) omega
  exact cutoffHomogenizationErrorRepresentative22_nonneg M (n - 2) n s.2
    (Annealed.sigmaBar M (n - 2)) omega

/-- The public `𝒢₂` observable is almost everywhere the literal `𝒢₂` atom of
`ErrorAtoms`. -/
theorem annularErrorAtom_ae_eq_annularErrorObservable (M : ABKModel d) (n : ℤ)
    (s : {s : ℝ // 0 < s}) :
    @annularErrorAtom d M n (s : ℝ) =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      annularErrorObservable M n s := by
  let : NeZero d := neZero_of_model_ErrorRepresentative22 M
  change cutoffHomogenizationErrorRaw22 M (n - 2) n (s : ℝ)
      (Annealed.sigmaBar M (n - 2)) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    cutoffHomogenizationErrorRepresentative22 M (n - 2) n s.2
      (Annealed.sigmaBar M (n - 2))
  exact cutoffHomogenizationErrorRaw22_ae_eq_representative22 M (n - 2) n s.2
    (Annealed.sigmaBar M (n - 2))

end

end Algsuperdiff.Section4.Support
