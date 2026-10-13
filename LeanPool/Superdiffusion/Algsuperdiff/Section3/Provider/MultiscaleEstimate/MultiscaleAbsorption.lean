/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleAbsorptionArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.MultiscaleEstimate.MultiscaleAbsorptionCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.DeepLegSummability

/-!
# MultiscaleAbsorption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the final absorption of `p.multiscale.estimate`

The arithmetic half is the sibling
`Provider/MultiscaleEstimate/MultiscaleAbsorptionCore.lean`.

## What is delivered

`multiscale_estimate_of_mStarStar` (section 10) is the frozen root's statement
body (`Frozen/Section3/MultiscaleEstimate.lean`) **verbatim, binder
for binder and amplitude spelling for amplitude spelling**, with ONE premise
inserted:

```text
    mStarStar M < m ->
```

immediately before `inductionState M (m - 1) E`.  Everything else is unchanged:
the same `exists Cms`, the same window `cstar^{-1} eps^{-Cms} <= E`, the same
smallness `cgamma <= (E^{-1})^{10}`, the same `s in [8 cgamma, 1]`, ONE `(Y, Z)`
pair for the main conjunct AND the refinement clause, and the two amplitudes

```text
    Cms E s^{-1} sqrt(eps cgamma)   and   Cms eps (s^{-1})^2 exp(-E^{-3} cgamma^{-1}) .
```

The fit is exact in both directions: the character-for-character copy of the
frozen body with the one premise inserted is inhabited by
`multiscale_estimate_of_mStarStar d` itself, and conversely the frozen body
implies that premised copy, so no strengthening hides in the endpoint.  The two
texts differ by `mStarStar M < m ->` and the proof opener alone.  Nothing else
about the fit moved: the inserted premise occupies the same slot, and every
other binder and amplitude spelling is untouched.

## The scale gate on `m`

The premise inserted above is `mStarStar M < m`, **not** the printed
`m0 in (mstar, infty) cap Z` that the display inherits.  The endpoint's name
`multiscale_estimate_of_mStarStar` records the gate.

## The carried premise (`mStarStar M < m`) — a named seam, NOT a weakening

Every proved producer of the buckle's five-term display carries the landmark
gate `mStarStar M < m0`:

* `Provider.Localization.localization_mathcalE_estimate_ae_unconditional`
  (and its conditional twin `localization_mathcalE_estimate_ae`);
* `exists_badEventSummed_bound`, inherited from `exists_crude_bound`.

Both inherit it from `l.shom.continuity`, whose own
premise it is.  The frozen root does **not** carry it, and neither does the
manuscript's Proposition `p.multiscale.estimate` ("Assume that `m in Z` and
`E in [1, infinity)` are such that `S(m-1, E)` is valid"), nor Lemma
`l.localization.mathcalE`.  It is **not derivable** from the frozen
root's binders: `inductionState M (m-1) E` constrains `sigmaBar` and the error
at scales `<= m-1` only, and is satisfiable at every `m`, however far below
`mStarStar M`.

The complementary range is now `m <= mStarStar M`, and it is proved: the
sibling `Provider.MultiscaleEstimate.multiscale_estimate_of_le_mStarStar`
(`MultiscaleBaseBranch.lean`) proves the same frozen body on exactly that range
from the base-case surface.

Gating at `mStarStar` rather than at `mStar` removes the band
`mStarStar M < m <= mStar M`, which under an `mStar` gate is covered by neither
branch.  That band is a record of what the base-case surface reaches, not an
open gap in this chain: the plateau `Provider.Base.annealedPlateau_le_mStar`
states only the diffusivity conjunct `nu <= sigmaBar_m <= 2 nu`, and disclaims
the homogenization-error conjunct; the only proved error statement at
`m <= mStar` (`exists_baseCaseMStarErrorConst`) fails three ways as a route to
this display (deterministic shift literally `2`, against an amplitude tending
to `0` as `E -> infinity`; no `cgamma` factor in
`(sqrt cstarPlus)^{-1} sqrt(baseLoss d s)`; `s`-range `Ioo 0 1` excluding
`s = 1`); and the `sqrt cgamma` gain exists only at the `mStarStar` (`cgamma^3`)
landmark, while `mStarStar M <= mStar M`.

Nothing here is weakened: every other binder of the frozen root is consumed as
given, and every side condition of every proved producer is discharged from
those binders (sections 8--10).

## The assembly, in the order it runs

1. **`Cms`** (section 8, `exists_absorptionConstants`) —
   `ParameterWeb.exists_parameterWeb_general` at `Chom:= max
   (homogenizationStepConst d) 10^9` with BOTH free slots used: `Cwin` carries
   every `<= Cms` demand and `Cshom` every `<= 2^{Cms}` demand, each as a SUM
   of nonnegative summands.  The numeral `10^9` occurs at exactly ONE place in
   this module, inside the proof of `exists_absorbed_envelope`, where the
   enlargement is performed; no statement of either module mentions it.
2. **`h := waveCutoff (2 max(Chom, 10^9)) eps`** — `one_le_waveCutoff`
   (`1 <= h`), `le_waveCutoff` (the corridor), `waveCutoff_le_add_one` (the bad
   producer's `H`-budget), `gamma_mul_waveCutoff_le_one` (`cgamma h <= 1`) and
   `three_rpow_five_waveCutoff_le` (the `3^{5h}` head).
3. **The `eps^2` normalisation** — the whole squared display runs at `eps^2`,
   which is what makes the frozen root's refinement clause free: the second
   conjunct is discharged with its `s <= Cms eps` hypothesis unused.
4. **The localization side** — the sibling's
   `localization_mathcalE_estimate_ae_unconditional` (the five-term endpoint
   with BOTH deep `Summable` premises discharged); the bad lane at ONE `Cbad`,
   extracted once from `exists_badEventSummed_bound` and threaded at
   `Ccg := 2 Cbad`, with the carrier bridge
   `ae_sq_cutoffHomogenizationError_eq_homogenizationErrorOnCube_sq`.
5. The adjoint leg costs no constant.
6. **The buckle** — `Provider.Orlicz.isTwoTermBigOWithWitnesses_sqrt_of_sq_one_
   quarter` (`Gamma_1 x Gamma_{1/4}` on the square becomes `Gamma_2 x
   Gamma_{1/2}` on the root), preceded by `exists_witnesses_of_envelope` (the
   a.e.-to-pointwise device) and followed by
   `Provider.Orlicz.isTwoTermBigOWithWitnesses_mono_scales`.
7. **ONE `(Y, Z)` pair** — the witnesses of step 6 serve BOTH conjuncts: the
   main one after `Provider.Orlicz.isTwoTermBigOWithWitnesses_mono_scales`, the
   refinement one from the SAME `Gamma_2` component by
   `IsBigOWith.mono_scale`.  Nothing is re-chosen.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport
open _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open _root_.Algsuperdiff.Section3.Cutoff
open _root_.Algsuperdiff.Section3.Provider.Localization

noncomputable section

variable {d : ℕ}

/-! ## 1. The two deep-leg terms -/

/-- On a nonempty sphere the frame bound's constant is nonnegative. -/
private theorem nonneg_of_forall_unit_responseJ_le {U : Ch02.Domain d} (hd : 0 < d)
    (a : Ch02.CoeffOn U) (sigma : Observable.PositiveScalar) {c : ℝ}
    (h : ∀ e : Vec d, Ch02.vecNorm e = 1 →
      Ch02.responseJ U a (Observable.inverseSqrtLoad sigma e)
        (Observable.sqrtLoad sigma e) ≤ c) :
    0 ≤ c := by
  have he : Ch02.vecNorm (Pi.single ⟨0, hd⟩ 1 : Vec d) = 1 := by
    refine Ch05.Section56.vecNorm_eq_one_of_vecNormSq_eq_one ?_
    rw [vecNormSq, vecDot, Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
    · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · simp
  exact le_trans (Ch02.responseJ_nonneg U a _ _) (h _ he)

/-- The half of a frame-supremum leg is bounded by every uniform bound on the
paired unit responses of the SAME representative. -/
private theorem half_breakdownLegA_le [NeZero d] (hd : 0 < d) (R : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (sigma : Observable.PositiveScalar) {c : ℝ}
    (h : ∀ e : Vec d, Ch02.vecNorm e = 1 →
      Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R)
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ c) :
    (1 / 2 : ℝ) * breakdownLegA R a (Observable.isotropicComparatorMatrix sigma) ≤ c := by
  have hc0 : 0 ≤ c := nonneg_of_forall_unit_responseJ_le hd (a.coeffOn R) sigma h
  have hpaired : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R)
        (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤ 2 * c :=
    fun v hv => responseJ_le_two_mul_of_forall_unit (a.coeffOn R) sigma hc0 h hv
  have hleg := breakdownLegA_le_of_paired_bound R a sigma (by linarith : (0 : ℝ) ≤ 2 * c)
    hpaired
  linarith

/-- This is the `(J3)` symmetry in the shape the lane aggregation consumes: the
transposed value at the negated sample is the primal value at the sample
(`responseJ_cutoffFamily_negateCutoffSample` at the involution). -/
private theorem half_breakdownLegB_negate_le [NeZero d] (hd : 0 < d)
    (M : ABKModel d) (L : ℤ) (R : TriadicCube d) (omega : CutoffSample d)
    (sigma : Observable.PositiveScalar) {c : ℝ}
    (h : ∀ e : Vec d, Ch02.vecNorm e = 1 →
      Ch02.responseJ (Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R)
        (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) ≤ c) :
    (1 / 2 : ℝ) * breakdownLegB R
        (coefficientCutoffTriadicCoeffFamily M L (negateCutoffSample omega))
        (Observable.isotropicComparatorMatrix sigma) ≤ c := by
  have hc0 : 0 ≤ c :=
    nonneg_of_forall_unit_responseJ_le hd
      ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) sigma h
  have htrans : ∀ p q : Vec d,
      Ch02.responseJ (Ch02.cubeDomain R)
          ((coefficientCutoffTriadicCoeffFamily M L
            (negateCutoffSample omega)).coeffOn R).transpose p q =
        Ch02.responseJ (Ch02.cubeDomain R)
          ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) p q := by
    intro p q
    have hinv := responseJ_cutoffFamily_negateCutoffSample M L R p q
      (negateCutoffSample omega)
    rw [negateCutoffSample_involutive omega] at hinv
    exact hinv.symm
  have hpaired : ∀ v : Vec d, vecNormSq v ≤ 2 →
      Ch02.responseJ (Ch02.cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L
          (negateCutoffSample omega)).coeffOn R).transpose
        (Observable.inverseSqrtLoad sigma v) (Observable.sqrtLoad sigma v) ≤ 2 * c := by
    intro v hv
    rw [htrans]
    exact responseJ_le_two_mul_of_forall_unit
      ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) sigma hc0 h hv
  have hleg := breakdownLegB_le_of_paired_bound R
    (coefficientCutoffTriadicCoeffFamily M L (negateCutoffSample omega)) sigma
    (by linarith : (0 : ℝ) ≤ 2 * c) hpaired
  linarith

/-- The scaled deep-leg envelope, in the shape both legs share: an envelope for
`96 s . (grid series of the HALF leg)` normalises to the module's two lane
scales, and dominates the printed `12 c_{2s} . (grid series of the leg)`. -/
private theorem twoLaneEnvelope_of_half_series [NeZero d]
    (M : ABKModel d) {m : ℤ} (E : {E : ℝ // 1 ≤ E}) {epsilon : ℝ}
    (heps0 : 0 < epsilon) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {bleg : ℕ → TriadicCube d → CutoffSample d → ℝ}
    (hbleg0 : ∀ (j : ℕ) (R : TriadicCube d) (omega : CutoffSample d),
      0 ≤ bleg j R omega)
    {U V : CutoffSample d → ℝ} (hUm : Measurable U) (hVm : Measurable V)
    (hUt : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma 1) U
      (homLaneOrdinaryConst d * (s⁻¹) ^ 2 *
        (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)))
    (hVt : IsBigOWith (cutoffSampleLaw M).toMeasure (gammaSigma (1 / 4)) V
      (homLaneRareConst d * (s⁻¹) ^ 5 *
        (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))))
    (hdom : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      gridScaleSeries m s (fun j R => (1 / 2 : ℝ) * bleg j R omega) ≤
        U omega + V omega) :
    TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega => 12 * (Ch02.geometricDiscount s 2 *
        gridScaleSeries m s (fun j R => bleg j R omega)))
      ((96 * homLaneOrdinaryConst d) *
        ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)))
      ((96 * homLaneRareConst d) *
        ((s⁻¹) ^ 4 * (epsilon ^ 2 *
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) := by
  have hd : d ≠ 0 := NeZero.ne d
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs
  have hsinv1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs).2 hs1
  have hOrd : (0 : ℝ) < homLaneOrdinaryConst d := homLaneOrdinaryConst_pos hd
  have hRare : (0 : ℝ) < homLaneRareConst d := homLaneRareConst_pos hd
  have hA1 : (0 : ℝ) < homLaneOrdinaryConst d * (s⁻¹) ^ 2 *
      (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) := by positivity
  have hA2 : (0 : ℝ) < homLaneRareConst d * (s⁻¹) ^ 5 *
      (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) := by positivity
  -- the half series
  have hhalf : ∀ omega : CutoffSample d,
      gridScaleSeries m s (fun j R => (1 / 2 : ℝ) * bleg j R omega) =
        (1 / 2 : ℝ) * gridScaleSeries m s (fun j R => bleg j R omega) := by
    intro omega
    rw [gridScaleSeries, gridScaleSeries, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [legScaleAverage_smul (originCube d m) (m - (j : ℤ)) hs hd
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun R _ => hbleg0 j R omega)]
    ring
  -- the raw envelope for the half series, scaled by `96 s`
  have henv : TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega => gridScaleSeries m s (fun j R => (1 / 2 : ℝ) * bleg j R omega))
      (homLaneOrdinaryConst d * (s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma))
      (homLaneRareConst d * (s⁻¹) ^ 5 *
        (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) :=
    TwoLaneEnvelope.of_envelope hA1 hA2 hUm hVm hUt hVt hdom
  have hscaled := henv.const_mul (c := 96 * s) (by positivity)
  refine (TwoLaneEnvelope.of_ae_le hscaled ?_).mono_scales ?_ ?_
  · refine Filter.Eventually.of_forall fun omega => ?_
    have hG0 : (0 : ℝ) ≤ gridScaleSeries m s (fun j R => bleg j R omega) :=
      gridScaleSeries_nonneg m s (fun j R _ => hbleg0 j R omega)
    have hgd := geometricDiscount_two_mul_le_of_nonneg (s := s) (G :=
      gridScaleSeries m s (fun j R => bleg j R omega)) hs.le hG0
    rw [hhalf omega]
    linarith
  · have hsne : s ≠ 0 := ne_of_gt hs
    have hrw : (96 * s) * (homLaneOrdinaryConst d * (s⁻¹) ^ 2 *
        (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)) =
        (96 * homLaneOrdinaryConst d) *
          (s⁻¹ * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)) := by
      field_simp
    rw [hrw]
    have hstep : s⁻¹ * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) ≤
        (s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) := by
      have hbase : (0 : ℝ) ≤ epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma := by positivity
      have : s⁻¹ ≤ (s⁻¹) ^ 2 := by nlinarith [hsinv1, hsinv]
      exact mul_le_mul_of_nonneg_right this hbase
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  · have hsne : s ≠ 0 := ne_of_gt hs
    have hrw : (96 * s) * (homLaneRareConst d * (s⁻¹) ^ 5 *
        (epsilon ^ 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) =
        (96 * homLaneRareConst d) *
          ((s⁻¹) ^ 4 * (epsilon ^ 2 *
            Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) := by
      field_simp
    exact le_of_eq hrw

/-- **The primal deep-leg term** `12 c_{2s} . Sigma_j 3^{-sj} (avsum_z legA_j^{d/s})^{s/d}`
of the localization display, at the two lane scales. -/
theorem twoLaneEnvelope_deepLegA [NeZero d]
    (M : ABKModel d) {m : ℤ} (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {epsilon : ℝ} (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (h : ℕ) (hcorr : 2 * homogenizationStepConst d * |Real.log epsilon| ≤ (h : ℝ)) :
    TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega => 12 * (Ch02.geometricDiscount s 2 *
        gridScaleSeries m s (fun j R => breakdownLegA R
          (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ)))))))
      ((96 * homLaneOrdinaryConst d) *
        ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)))
      ((96 * homLaneRareConst d) *
        ((s⁻¹) ^ 4 * (epsilon ^ 2 *
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) := by
  have hdpos : 0 < d := Provider.Orlicz.dim_pos_of_model M
  obtain ⟨U, V, hUm, hVm, hUt, hVt, hdom⟩ :=
    exists_envelope_gridScaleSeries_homogenizationInput M E hE hgammaE hS hepsilon
      hgate hs hs1 h hcorr
      (leg := fun j R omega => (1 / 2 : ℝ) * breakdownLegA R
        (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
        (Observable.isotropicComparatorMatrix
          (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ)))))
      (fun j R omega => by
        have := breakdownLegA_nonneg R
          (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ))))
        linarith)
      (fun j R _hR omega c hc => half_breakdownLegA_le hdpos R _ _ hc)
  exact twoLaneEnvelope_of_half_series M E hepsilon.1 hs hs1
    (bleg := fun j R omega => breakdownLegA R
      (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ)))))
    (fun j R omega => breakdownLegA_nonneg _ _ _) hUm hVm hUt hVt hdom

/-- **The adjoint deep-leg term**, at the same two lane scales.  The `(J3)`
negation is a law isomorphism, so the adjoint leg costs no constant: its
envelope is the primal envelope read at the negated sample. -/
theorem twoLaneEnvelope_deepLegB [NeZero d]
    (M : ABKModel d) {m : ℤ} (E : {E : ℝ // 1 ≤ E})
    (hE : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hgammaE : M.gamma ≤ ((E : ℝ)⁻¹) ^ 10)
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E)
    {epsilon : ℝ} (hepsilon : epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (h : ℕ) (hcorr : 2 * homogenizationStepConst d * |Real.log epsilon| ≤ (h : ℝ)) :
    TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega => 12 * (Ch02.geometricDiscount s 2 *
        gridScaleSeries m s (fun j R => breakdownLegB R
          (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ)))))))
      ((96 * homLaneOrdinaryConst d) *
        ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)))
      ((96 * homLaneRareConst d) *
        ((s⁻¹) ^ 4 * (epsilon ^ 2 *
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) := by
  have hdpos : 0 < d := Provider.Orlicz.dim_pos_of_model M
  obtain ⟨U, V, hUm, hVm, hUt, hVt, hdom⟩ :=
    exists_envelope_gridScaleSeries_homogenizationInput M E hE hgammaE hS hepsilon
      hgate hs hs1 h hcorr
      (leg := fun j R omega => (1 / 2 : ℝ) * breakdownLegB R
        (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ))
          (negateCutoffSample omega))
        (Observable.isotropicComparatorMatrix
          (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ)))))
      (fun j R omega => by
        have := breakdownLegB_nonneg R
          (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ))
            (negateCutoffSample omega))
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ))))
        linarith)
      (fun j R _hR omega c hc =>
        half_breakdownLegB_negate_le hdpos M (m - (j : ℤ) - (h : ℤ)) R omega _ hc)
  have hdom' := ae_comp_negateCutoffSample M hdom
  have hdom'' : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      gridScaleSeries m s (fun j R => (1 / 2 : ℝ) * breakdownLegB R
        (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
        (Observable.isotropicComparatorMatrix
          (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ))))) ≤
        U (negateCutoffSample omega) + V (negateCutoffSample omega) := by
    filter_upwards [hdom'] with omega homega
    rwa [negateCutoffSample_involutive omega] at homega
  exact twoLaneEnvelope_of_half_series M E hepsilon.1 hs hs1
    (bleg := fun j R omega => breakdownLegB R
      (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (h : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (h : ℤ)))))
    (fun j R omega => breakdownLegB_nonneg _ _ _)
    (hUm.comp measurable_negateCutoffSample) (hVm.comp measurable_negateCutoffSample)
    (Provider.Stream.isBigOWith_comp_of_map_eq measurable_negateCutoffSample
      (map_negateCutoffSample_cutoffSampleLaw M) hUm hUt)
    (Provider.Stream.isBigOWith_comp_of_map_eq measurable_negateCutoffSample
      (map_negateCutoffSample_cutoffSampleLaw M) hVm hVt)
    hdom''

/-! ## 2. The wave term -/

private theorem waveSizesTotalW2_nonneg (M : ABKModel d) (m : ℤ) (h : ℕ) {s : ℝ}
    (hs : 0 ≤ s) (omega : ShellSeq d) : 0 ≤ waveSizesTotalW2 M m h s omega := by
  refine mul_nonneg hs (tsum_nonneg fun j => ?_)
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Localization.legScaleAverage_nonneg _ _ _ (fun R _ => by positivity))

private theorem measurable_waveSizesTotalW2 (M : ABKModel d) (m : ℤ) (h : ℕ) {s : ℝ}
    (hs : 0 < s) :
    Measurable (fun omega : ShellSeq d => waveSizesTotalW2 M m h s omega) := by
  have hterm : Measurable (fun omega : ShellSeq d => ∑' j : ℕ, (3 : ℝ) ^ (-s * (j : ℝ)) *
      Localization.legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => waveSizeW2 M m h R omega ^ 2)) :=
    measurable_tsum_of_nonneg'
      (fun j => (measurable_waveScaleAverageW2 M m h j hs).const_mul _)
      (fun j omega => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Localization.legScaleAverage_nonneg _ _ _ (fun R _ => by positivity)))
  exact hterm.const_mul s

/-- **The wave term** `32 Cinj cstar^{-1} cgamma . waveSizesTotalW2`, at the
`Gamma_1` scale of `e.wave.sizes` and an empty rare lane. -/
theorem twoLaneEnvelope_waveTerm (M : ABKModel d) (m : ℤ) (h : ℕ) {s : ℝ} (hs : 0 < s)
    {Cinj Awave : ℝ} (hCinj : 0 ≤ Cinj)
    (hbound : IsBigOWith M.P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => waveSizesTotalW2 M m h s omega) Awave) :
    TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega : CutoffSample d => Cinj * waveSizesTotalW2 M m h s omega.1)
      (Cinj * Awave) (Cinj * 0) := by
  have henv : TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega : CutoffSample d => waveSizesTotalW2 M m h s omega.1) Awave 0 :=
    TwoLaneEnvelope.of_isBigOWith_gammaOne
      ((measurable_waveSizesTotalW2 M m h hs).comp measurable_subtype_coe)
      (fun omega => waveSizesTotalW2_nonneg M m h hs.le _)
      (Provider.Stream.isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val
        (fun _ => rfl) hbound) le_rfl
  exact henv.const_mul hCinj

/-! ## 3. The bad-event term -/

/-- **The bad-event term** `8 . max_l 3^{-s(m-l)/2}(avsum_z 1_{not Q})^{s/d} . E^2_{s/4}`
of the localization display.

Two things happen here and nothing else.  The proved producer
`exists_badEventSummed_bound` states the display at the `Gamma_{2/7}` rare
profile of `e.local.bad.events.summed`; the squared display of the buckle runs
at `Gamma_{1/4}`, and `2/7 > 1/4`, so the index is lowered — never raised — by
`Provider.Orlicz.isTwoTermBigOWith_mono_exponent`.  And the producer's left
factor is the Section 3 observable `E_{s/4}^2` while the localization display's
is CoarseGraining's `HomogenizationErrorOnCube`; the two agree almost surely,
which is the hypothesis `hGeq` (its producer is the proved
`BadEventSummed.ae_sq_cutoffHomogenizationError_eq_homogenizationErrorOnCube_sq`). -/
theorem twoLaneEnvelope_badTerm (M : ABKModel d) (m : ℤ) {s : ℝ} (hs4 : 0 < s / 4)
    {W G : CutoffSample d → ℝ} {B1 B2 : ℝ}
    (hGeq : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      G omega = Observable.cutoffHomogenizationError M m ⟨s / 4, hs4⟩ omega ^ 2)
    (hbad : Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (gammaSigma (2 / 7))
      (fun omega =>
        Observable.cutoffHomogenizationError M m ⟨s / 4, hs4⟩ omega ^ 2 * W omega)
      B1 B2) :
    TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun omega => 8 * W omega * G omega) (8 * B1) (8 * B2) := by
  have hquarter : Probability.IsTwoTermBigOWith (cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (gammaSigma (1 / 4))
      (fun omega =>
        Observable.cutoffHomogenizationError M m ⟨s / 4, hs4⟩ omega ^ 2 * W omega)
      B1 B2 :=
    Provider.Orlicz.isTwoTermBigOWith_mono_exponent one_pos (by norm_num)
      le_rfl (by norm_num) hbad
  have henv := (TwoLaneEnvelope.of_isTwoTermBigOWith hquarter).const_mul
    (c := 8) (by norm_num)
  refine TwoLaneEnvelope.of_ae_le henv ?_
  filter_upwards [hGeq] with omega homega
  rw [homega]
  ring_nf
  exact le_rfl

/-! ## 4--6. (moved)  The three scale bridges of the non-lane terms, the bad
lane's two amplitudes, and the deterministic remainder now live in the sibling
`Provider/MultiscaleEstimate/MultiscaleAbsorptionArith.lean`, split out at the
1500-line file cap, with their section headers, statements and proof text
unchanged.  Their section numbers are kept there so that every cross-reference
in this header still points where it did; the four consumed below are
`MultiscaleAbsorptionArith.polyTerm_le_ordinaryScale`,
`.badOrdinaryAmplitude_le`, `.badRareAmplitude_le` and `.remainderTerm_le`. -/

/-! ## 7. The five-term sum in the two normal forms -/

/-- The buckle's five terms, each already normalised to the two scales
`Ki S1` and `Li S2`, add to the assembled scales.  Four applications of the
`Gamma_1` and `Gamma_{1/4}` triangle inequalities and nothing else. -/
private theorem twoLaneEnvelope_fiveSum {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X1 X2 X3 X4 X5 : Omega → ℝ}
    {S1 S2 K1 K2 K3 K4 K5 L1 L2 L3 L4 L5 : ℝ}
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK4 : 0 ≤ K4) (hK5 : 0 ≤ K5)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL3 : 0 ≤ L3) (hL4 : 0 ≤ L4) (hL5 : 0 ≤ L5)
    (h1 : TwoLaneEnvelope mu X1 (K1 * S1) (L1 * S2))
    (h2 : TwoLaneEnvelope mu X2 (K2 * S1) (L2 * S2))
    (h3 : TwoLaneEnvelope mu X3 (K3 * S1) (L3 * S2))
    (h4 : TwoLaneEnvelope mu X4 (K4 * S1) (L4 * S2))
    (h5 : TwoLaneEnvelope mu X5 (K5 * S1) (L5 * S2)) :
    TwoLaneEnvelope mu
      (fun omega => X1 omega + X2 omega + X3 omega + X4 omega + X5 omega)
      ((gammaTriangleConst 1 * (gammaTriangleConst 1 * (gammaTriangleConst 1 *
        (gammaTriangleConst 1 * (K1 + K2) + K3) + K4) + K5)) * S1)
      ((gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
        (gammaTriangleConst (1 / 4) *
          (gammaTriangleConst (1 / 4) * (L1 + L2) + L3) + L4) + L5)) * S2) := by
  have h12 := (h1.add (mul_nonneg hK1 hS1) (mul_nonneg hL1 hS2)
      (mul_nonneg hK2 hS1) (mul_nonneg hL2 hS2) h2).mono_scales
    (le_of_eq (by ring : gammaTriangleConst 1 * (K1 * S1 + K2 * S1) =
      (gammaTriangleConst 1 * (K1 + K2)) * S1))
    (le_of_eq (by ring : gammaTriangleConst (1 / 4) * (L1 * S2 + L2 * S2) =
      (gammaTriangleConst (1 / 4) * (L1 + L2)) * S2))
  have h120 : (0 : ℝ) ≤ gammaTriangleConst 1 * (K1 + K2) := by
    have := gammaTriangleConst_pos (σ := (1 : ℝ))
    positivity
  have h120' : (0 : ℝ) ≤ gammaTriangleConst (1 / 4) * (L1 + L2) := by
    have := gammaTriangleConst_pos (σ := (1 / 4 : ℝ))
    positivity
  have h123 := (h12.add (mul_nonneg h120 hS1) (mul_nonneg h120' hS2)
      (mul_nonneg hK3 hS1) (mul_nonneg hL3 hS2) h3).mono_scales
    (le_of_eq (by ring : gammaTriangleConst 1 *
        ((gammaTriangleConst 1 * (K1 + K2)) * S1 + K3 * S1) =
      (gammaTriangleConst 1 * (gammaTriangleConst 1 * (K1 + K2) + K3)) * S1))
    (le_of_eq (by ring : gammaTriangleConst (1 / 4) *
        ((gammaTriangleConst (1 / 4) * (L1 + L2)) * S2 + L3 * S2) =
      (gammaTriangleConst (1 / 4) *
        (gammaTriangleConst (1 / 4) * (L1 + L2) + L3)) * S2))
  have h1230 : (0 : ℝ) ≤ gammaTriangleConst 1 *
      (gammaTriangleConst 1 * (K1 + K2) + K3) := by
    have := gammaTriangleConst_pos (σ := (1 : ℝ))
    positivity
  have h1230' : (0 : ℝ) ≤ gammaTriangleConst (1 / 4) *
      (gammaTriangleConst (1 / 4) * (L1 + L2) + L3) := by
    have := gammaTriangleConst_pos (σ := (1 / 4 : ℝ))
    positivity
  have h1234 := (h123.add (mul_nonneg h1230 hS1) (mul_nonneg h1230' hS2)
      (mul_nonneg hK4 hS1) (mul_nonneg hL4 hS2) h4).mono_scales
    (le_of_eq (by ring : gammaTriangleConst 1 *
        ((gammaTriangleConst 1 * (gammaTriangleConst 1 * (K1 + K2) + K3)) * S1 +
          K4 * S1) =
      (gammaTriangleConst 1 *
        (gammaTriangleConst 1 * (gammaTriangleConst 1 * (K1 + K2) + K3) + K4)) * S1))
    (le_of_eq (by ring : gammaTriangleConst (1 / 4) *
        ((gammaTriangleConst (1 / 4) *
          (gammaTriangleConst (1 / 4) * (L1 + L2) + L3)) * S2 + L4 * S2) =
      (gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
        (gammaTriangleConst (1 / 4) * (L1 + L2) + L3) + L4)) * S2))
  have h12340 : (0 : ℝ) ≤ gammaTriangleConst 1 *
      (gammaTriangleConst 1 * (gammaTriangleConst 1 * (K1 + K2) + K3) + K4) := by
    have := gammaTriangleConst_pos (σ := (1 : ℝ))
    positivity
  have h12340' : (0 : ℝ) ≤ gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
      (gammaTriangleConst (1 / 4) * (L1 + L2) + L3) + L4) := by
    have := gammaTriangleConst_pos (σ := (1 / 4 : ℝ))
    positivity
  exact (h1234.add (mul_nonneg h12340 hS1) (mul_nonneg h12340' hS2)
      (mul_nonneg hK5 hS1) (mul_nonneg hL5 hS2) h5).mono_scales
    (le_of_eq (by ring)) (le_of_eq (by ring))

/-! ## 8. The parameter web at the assembled constants -/

/-- **The `Cms` of the buckle** (`Cms` is chosen after every dimensional
constant).  `ParameterWeb.exists_parameterWeb_general`'s two
free slots `Cwin` and `Cshom` are instantiated at the SUM of everything the
absorption needs — a sum rather than a maximum, because every summand is
nonnegative and the web is monotone in both slots.

`Cwin` collects the `<= Cms` demands: the corridor's own `2 Chom`, the
bad-event producer's window exponent `Cbig`, the wave bound's exponent
`2 + Cwave`, the `3^{5h}` exponent `2 + (5 (2 Chom) log 3 + 8)`, and the two
square-root floors `sqrt Ktot`, `sqrt Ltot`.  `Cshom` collects the `<= 2^{Cms}`
demands: the localization triple, the shom gate, and the four absolute gates. -/
private theorem exists_absorptionConstants (d : ℕ) (hd : d ≠ 0)
    {Chom' Cs Cg Ci Ccg0 Cshom0 Cbad cc Cbig Cwave : ℝ} (hChom'pos : 0 < Chom')
    (hCs : 0 < Cs) (hCg : 0 < Cg) (hCi : 0 < Ci) (hCcg0 : 0 < Ccg0)
    (hCshom0 : 0 < Cshom0) (hCbad : 1 ≤ Cbad) (hcc : 0 < cc) (hCbig : 1 ≤ Cbig)
    (hCwave : 0 < Cwave) (hresp : 0 ≤ Provider.BadEvents.responseSensitivityConst d) :
    ∃ Cms Ktot Ltot K4 L4 K5 : ℝ,
      0 < Cms ∧ 4 ≤ Cms ∧ 0 < Ktot ∧ 0 < Ltot ∧ 0 ≤ K4 ∧ 0 ≤ L4 ∧ 0 ≤ K5 ∧
      Real.sqrt Ktot ≤ Cms ∧ Real.sqrt Ltot ≤ Cms ∧
      Chom' ≤ Cms ∧
      2 * Chom' ≤ Cms ∧
      Cbig ≤ Cms ∧ 2 + Cwave ≤ Cms ∧
      2 + (5 * (2 * Chom') * Real.log 3 + 8) ≤ Cms ∧
      Cs ≤ (2 : ℝ) ^ Cms ∧ Cg ≤ (2 : ℝ) ^ Cms ∧ Ci ≤ (2 : ℝ) ^ Cms ∧
      Cshom0 ≤ (2 : ℝ) ^ Cms ∧
      Chom' ≤ (2 : ℝ) ^ Cms ∧
      (3 / 2 : ℝ) * Real.exp (Ccg0 / (1 / 7)) ≤ (2 : ℝ) ^ Cms ∧
      (3 / 2 : ℝ) * (32 * (324 * Provider.BadEvents.responseSensitivityConst d *
        (16 * (2 * Cbad) + 8 * (2 * Cbad) ^ 2)) * Cwave) ≤ (2 : ℝ) ^ Cms ∧
      (3 / 2 : ℝ) * (122880 * Ccg0 * gammaTriangleConst 1 * (d : ℝ) * cc⁻¹) ≤
        (2 : ℝ) ^ Cms ∧
      (3 / 2 : ℝ) * (608 * Ccg0) ≤ (2 : ℝ) ^ Cms ∧
      (3 / 2 : ℝ) * (8 * Ccg0) ≤ (2 : ℝ) ^ Cms ∧
      2 * (122880 * Ccg0 * gammaTriangleConst 1 * (d : ℝ)) * (cc⁻¹) ^ 2 *
          (3 / 2 : ℝ) ^ 8 + 2 ≤ K4 ∧
      8 * 4096 * Ccg0 ^ 2 * (3 / 2 : ℝ) ^ 16 ≤ L4 ∧
      4 * (1024 * (Cs * (48 * (2 * Cbad)))) * (3 / 2 : ℝ) ^ 10 +
          (1024 * (Cs * (48 * (2 * Cbad)))) * (3 / 2 : ℝ) ^ 10 +
          384 * (1024 * (Cs * (48 * (2 * Cbad)))) * (3 / 2 : ℝ) ^ 3 ≤ K5 ∧
      gammaTriangleConst 1 * (gammaTriangleConst 1 * (gammaTriangleConst 1 *
          (gammaTriangleConst 1 * (96 * homLaneOrdinaryConst d +
            96 * homLaneOrdinaryConst d) + 1) + K4) + K5) ≤ Ktot ∧
      gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
        (gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
          (96 * homLaneRareConst d + 96 * homLaneRareConst d) + 0) + L4) + 0) ≤ Ltot := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hGam1 : (0 : ℝ) < gammaTriangleConst 1 := gammaTriangleConst_pos
  have hGamq : (0 : ℝ) < gammaTriangleConst (1 / 4) := gammaTriangleConst_pos
  have hOrd : (0 : ℝ) < homLaneOrdinaryConst d := homLaneOrdinaryConst_pos hd
  have hRare : (0 : ℝ) < homLaneRareConst d := homLaneRareConst_pos hd
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  set Q3 : ℝ := 32 * (324 * Provider.BadEvents.responseSensitivityConst d *
    (16 * (2 * Cbad) + 8 * (2 * Cbad) ^ 2)) * Cwave with hQ3def
  have hQ30 : (0 : ℝ) ≤ Q3 := by rw [hQ3def]; positivity
  set Q4a : ℝ := 122880 * Ccg0 * gammaTriangleConst 1 * (d : ℝ) * cc⁻¹ with hQ4adef
  set Q4b : ℝ := 122880 * Ccg0 * gammaTriangleConst 1 * (d : ℝ) with hQ4bdef
  have hQ4a0 : (0 : ℝ) ≤ Q4a := by rw [hQ4adef]; positivity
  set Q5 : ℝ := 1024 * (Cs * (48 * (2 * Cbad))) with hQ5def
  have hQ50 : (0 : ℝ) ≤ Q5 := by rw [hQ5def]; positivity
  set K4 : ℝ := 2 * Q4b * (cc⁻¹) ^ 2 * (3 / 2 : ℝ) ^ 8 + 2 with hK4def
  set L4 : ℝ := 8 * 4096 * Ccg0 ^ 2 * (3 / 2 : ℝ) ^ 16 with hL4def
  set K5 : ℝ := 4 * Q5 * (3 / 2 : ℝ) ^ 10 + Q5 * (3 / 2 : ℝ) ^ 10 +
    384 * Q5 * (3 / 2 : ℝ) ^ 3 with hK5def
  have hK40 : (0 : ℝ) ≤ K4 := by rw [hK4def, hQ4bdef]; positivity
  have hL40 : (0 : ℝ) ≤ L4 := by rw [hL4def]; positivity
  have hK50 : (0 : ℝ) ≤ K5 := by rw [hK5def, hQ5def]; positivity
  set Ktot : ℝ := gammaTriangleConst 1 * (gammaTriangleConst 1 *
    (gammaTriangleConst 1 * (gammaTriangleConst 1 *
      (96 * homLaneOrdinaryConst d + 96 * homLaneOrdinaryConst d) + 1) + K4) + K5)
    with hKtotdef
  set Ltot : ℝ := gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
    (gammaTriangleConst (1 / 4) * (gammaTriangleConst (1 / 4) *
      (96 * homLaneRareConst d + 96 * homLaneRareConst d) + 0) + L4) + 0)
    with hLtotdef
  have hKtot0 : (0 : ℝ) < Ktot := by rw [hKtotdef]; positivity
  have hLtot0 : (0 : ℝ) < Ltot := by rw [hLtotdef]; positivity
  set Cwin : ℝ := 2 * Chom' + Cbig + Cwave + (10 * Chom' * Real.log 3 + 10) +
    Real.sqrt Ktot + Real.sqrt Ltot + 2 with hCwindef
  set Cshom : ℝ := (3 / 2 : ℝ) *
    (Cs + Cg + Ci + Cshom0 + Q3 + Q4a + 608 * Ccg0 + 8 * Ccg0 + 1) with hCshomdef
  obtain ⟨Cms, hCms0, hCms1, hCms4, hChomCms, hCwinCms, hCmslog, hChom2, hCcg2,
    hCshom2, h152⟩ := exists_parameterWeb_general Chom' Cwin Ccg0 Cshom
  have hsqK : (0 : ℝ) ≤ Real.sqrt Ktot := Real.sqrt_nonneg Ktot
  have hsqL : (0 : ℝ) ≤ Real.sqrt Ltot := Real.sqrt_nonneg Ltot
  have hpieces : (0 : ℝ) ≤ 10 * Chom' * Real.log 3 + 10 := by positivity
  rw [hCwindef] at hCwinCms
  rw [hCshomdef] at hCshom2
  refine ⟨Cms, Ktot, Ltot, K4, L4, K5, hCms0, hCms4, hKtot0, hLtot0, hK40, hL40, hK50,
    by linarith, by linarith, hChomCms, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith, hChom2, hCcg2,
    by linarith, by linarith, by linarith, by linarith, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl⟩

/-! ## 9. The absorbed envelope of the squared display -/

/-- **The final absorption.**  At the `Cms` of section 8, the whole five-term
localization display collapses onto the squared display's two normal forms

```text
    A1 = Ktot . (s^{-1})^2 (eps^2 E^2 cgamma) ,
    A2 = Ltot . (s^{-1})^4 (eps^2 exp(-2 E^{-3} cgamma^{-1})) .
```

The single premise beyond the frozen root's own binders is `mStarStar M < m` (
option (i)); see the module header. -/
theorem exists_absorbed_envelope (d : ℕ) [NeZero d] :
    ∃ Cms Ktot Ltot : ℝ, 0 < Cms ∧ 4 ≤ Cms ∧ 0 < Ktot ∧ 0 < Ltot ∧
      Real.sqrt Ktot ≤ Cms ∧ Real.sqrt Ltot ≤ Cms ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
              (fun omega => Observable.cutoffHomogenizationError M m
                ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8)
                  M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩ omega ^ 2)
              (Ktot * ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)))
              (Ltot * ((s⁻¹) ^ 4 * (epsilon ^ 2 *
                Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) := by
  classical
  have hd : d ≠ 0 := NeZero.ne d
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hGam1 : (0 : ℝ) < gammaTriangleConst 1 := gammaTriangleConst_pos
  have hOrd : (0 : ℝ) < homLaneOrdinaryConst d := homLaneOrdinaryConst_pos hd
  have hRare : (0 : ℝ) < homLaneRareConst d := homLaneRareConst_pos hd
  have hresp : (0 : ℝ) ≤ Provider.BadEvents.responseSensitivityConst d := by
    by_cases h2d : 2 ≤ d
    · exact (Provider.BadEvents.responseSensitivityConst_pos h2d).le
    · simp [Provider.BadEvents.responseSensitivityConst, h2d]
  set Chom' : ℝ := max (homogenizationStepConst d) (10 ^ 9 : ℝ) with hChomdef
  have hChom'pos : (0 : ℝ) < Chom' :=
    lt_of_lt_of_le (homogenizationStepConst_pos d) (le_max_left _ _)
  have hC0pos : (0 : ℝ) < 2 * Chom' := by linarith
  obtain ⟨Cs, Cg, Ci, hCs, hCg, hCi, hloc⟩ :=
    localization_mathcalE_estimate_ae_unconditional d
  obtain ⟨Ccg0, Cshom0, Cbad, cc, hCcg0, hCshom0, hCbad, hcc, hbadH⟩ :=
    exists_badEventSummed_bound d
  obtain ⟨Cbig, hCbig1, hbad⟩ := hbadH (2 * Chom') hC0pos.le
  obtain ⟨Cwave, hCwave, hwave⟩ := wave_sizes_bound d hC0pos
  obtain ⟨Cms, Ktot, Ltot, K4, L4, K5, hCms0, hCms4, hKtot0, hLtot0, hK40, hL40,
    hK50, hwinKtot, hwinLtot, hChomCms, hwinC0, hwinCbig, hwinCwave, hwinP,
    hshomCs, hshomCg, hshomCi, hshomCshom0, hChom2, hCcg2, hshomQ3, hshomQ4a,
    hshomQ4c, hshomRare, hK4le, hL4le, hK5le, hKtotle, hLtotle⟩ :=
    exists_absorptionConstants d hd hChom'pos hCs hCg hCi hCcg0 hCshom0 hCbad hcc
      hCbig1 hCwave hresp
  set Ccg : ℝ := 2 * Cbad with hCcgdef
  have hCcgpos : (0 : ℝ) < Ccg := by rw [hCcgdef]; linarith
  set Q3 : ℝ := 32 * (324 * Provider.BadEvents.responseSensitivityConst d *
    (16 * Ccg + 8 * Ccg ^ 2)) * Cwave with hQ3def
  have hQ30 : (0 : ℝ) ≤ Q3 := by rw [hQ3def]; positivity
  set Q4a : ℝ := 122880 * Ccg0 * gammaTriangleConst 1 * (d : ℝ) * cc⁻¹ with hQ4adef
  set Q4b : ℝ := 122880 * Ccg0 * gammaTriangleConst 1 * (d : ℝ) with hQ4bdef
  set Q5 : ℝ := 1024 * (Cs * (48 * Ccg)) with hQ5def
  have hQ50 : (0 : ℝ) ≤ Q5 := by rw [hQ5def]; positivity
  have hK10 : (0 : ℝ) ≤ 96 * homLaneOrdinaryConst d := by positivity
  have hL10 : (0 : ℝ) ≤ 96 * homLaneRareConst d := by positivity
  refine ⟨Cms, Ktot, Ltot, hCms0, hCms4, hKtot0, hLtot0, hwinKtot, hwinLtot, ?_⟩
  intro M m E hmStar hS epsilon hepsilon hwin hgammaE s hsWindow
  have heps0 : (0 : ℝ) < epsilon := hepsilon.1
  have heps : epsilon ≤ 1 / 2 := hepsilon.2
  have heps1 : epsilon ≤ 1 := by linarith
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs8 : 8 * M.gamma ≤ s := hsWindow.1
  have hs1 : s ≤ 1 := hsWindow.2
  have hs : (0 : ℝ) < s := (mul_pos (by norm_num : (0 : ℝ) < 8) hgam).trans_le hs8
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsinv : (0 : ℝ) < s⁻¹ := inv_pos.2 hs
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
  have hcstar : (0 : ℝ) < Disorder.cstar M := Provider.Orlicz.cstar_pos M
  have hcinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := (inv_pos.2 hcstar).le
  have hfloor : (2 / 3 : ℝ) * epsilon ^ (-Cms) ≤ (E : ℝ) :=
    two_thirds_mul_le_of_window' M heps0 hwin
  have hE10 : (10 : ℝ) ≤ (E : ℝ) := ten_le_of_window heps0 heps hCms4 hfloor
  have hgam1 : M.gamma ≤ 1 := by
    have hinv1 : (E : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ E.2
    have hp := pow_le_one₀ (inv_nonneg.2 hEpos.le) hinv1 (n := 10)
    linarith [hgammaE, hp]
  have h15 : 15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    fifteen_mul_cstar_inv_le_of_window M heps0 heps hCms4 hwin
  have hchom2 : homogenizationStepConst d ≤ (2 : ℝ) ^ Cms :=
    le_trans (le_max_left _ _) hChom2
  have hgate : M.gamma ≤ (homogenizationStepConst d)⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ^ 2 :=
    gamma_le_gate_of_pow (homogenizationStepConst_pos d) hEpos
      (chom_le_pow_mul_sq_of_window heps0 heps hCms4 hchom2 hfloor) hgammaE
  set h : ℕ := waveCutoff (2 * Chom') epsilon with hhdef
  have hgh : M.gamma * ((h : ℕ) : ℝ) ≤ 1 :=
    gamma_mul_waveCutoff_le_one heps0 heps hCms4 hChom'pos.le hChomCms hfloor hgammaE
  have hh1 : 1 ≤ h := one_le_waveCutoff hC0pos heps0 heps
  have hhH : ((h : ℕ) : ℝ) ≤ 2 * Chom' * |Real.log epsilon| + 1 :=
    waveCutoff_le_add_one hC0pos.le
  have hcorr : 2 * homogenizationStepConst d * |Real.log epsilon| ≤ ((h : ℕ) : ℝ) := by
    have h1 := le_waveCutoff (2 * Chom') epsilon
    have h2 : 2 * homogenizationStepConst d ≤ 2 * Chom' := by
      have := le_max_left (homogenizationStepConst d) ((10 : ℝ) ^ 9)
      linarith
    exact (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)).trans h1
  have hhgap2E : ((h : ℕ) : ℝ) ≤ 2 * (E : ℝ) := by
    have habs := abs_log_le_of_window heps0 heps hfloor
    have h1 : 2 * Chom' * |Real.log epsilon| ≤ Cms * |Real.log epsilon| :=
      mul_le_mul_of_nonneg_right hwinC0 (abs_nonneg _)
    linarith [hhH, habs, h1, hE10]
  have hCsE : Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    relative_gate_le_of_window heps0 heps hCms0.le hcinv hshomCs hwin
  have hCgE : Cg * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    relative_gate_le_of_window heps0 heps hCms0.le hcinv hshomCg hwin
  have hCiE : Ci * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    relative_gate_le_of_window heps0 heps hCms0.le hcinv hshomCi hwin
  have hcgE : max (Real.exp (Ccg0 / (1 / 7))) (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    coarseGrainingGate_le_of_window M heps0 heps hCms0.le hCcg2 hwin
  have hshomE : Cshom0 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
    shomGate_le_of_window M heps0 heps hCms0.le hshomCshom0 hwin
  have hE5 : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) := le_rpow_neg_fifth E.2 hgam hgammaE
  have hwinBig : (Disorder.cstar M)⁻¹ * epsilon ^ (-Cbig) ≤ (E : ℝ) :=
    window_of_le heps0 heps1 hcinv hwinCbig hwin
  have hEQ3 : Q3 ≤ (E : ℝ) :=
    absolute_gate_le_of_window heps0 heps hCms0.le hshomQ3 hfloor
  have hEQ4a : Q4a ≤ (E : ℝ) :=
    absolute_gate_le_of_window heps0 heps hCms0.le hshomQ4a hfloor
  have hEQ4c : 608 * Ccg0 ≤ (E : ℝ) :=
    absolute_gate_le_of_window heps0 heps hCms0.le hshomQ4c hfloor
  have hERare : 8 * Ccg0 ≤ (E : ℝ) :=
    absolute_gate_le_of_window heps0 heps hCms0.le hshomRare hfloor
  have hdisp := hloc M m E hmStar hS hCsE hCgE hCiE hgammaE Ccg hCcgpos m le_rfl h hgh
    s hs8 hs1
  have hF : ∀ j : ℕ,
      ((descendantsAtScale (originCube d m) (m - (j : ℤ))).image
        triadicCubeShift).Nonempty := fun j =>
    Finset.Nonempty.image (descendantsAtScale_nonempty (originCube d m)
      (show m - (j : ℤ) ≤ (originCube d m).scale by
        show m - (j : ℤ) ≤ m
        omega)) triadicCubeShift
  have hbadM := hbad M m E epsilon h hS hmStar hcgE hshomE hE5 hgammaE hepsilon hhH
    hwinBig hh1 s hs8 hs1
    (fun j => (descendantsAtScale (originCube d m) (m - (j : ℤ))).image triadicCubeShift)
    hF
  have hwaveM := hwave M m epsilon s heps0 heps1 hs hs1 hs8
  have hS10 : (0 : ℝ) ≤ (s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma) := by positivity
  have hS20 : (0 : ℝ) ≤ (s⁻¹) ^ 4 * (epsilon ^ 2 *
      Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) := by positivity
  have hT1 := twoLaneEnvelope_deepLegA M E h15 hgammaE hS hepsilon hgate hs hs1 h hcorr
  have hT2 := twoLaneEnvelope_deepLegB M E h15 hgammaE hS hepsilon hgate hs hs1 h hcorr
  -- the wave term
  have hCinj0 : (0 : ℝ) ≤ 4 * (8 * (324 *
      Provider.BadEvents.responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
      ((Disorder.cstar M)⁻¹ * M.gamma))) := by positivity
  have hwaveScale : (4 * (8 * (324 *
        Provider.BadEvents.responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
        ((Disorder.cstar M)⁻¹ * M.gamma)))) * (Cwave * epsilon ^ (-Cwave) / s ^ 2) ≤
      1 * ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)) := by
    have hpoly := MultiscaleAbsorptionArith.polyTerm_le_ordinaryScale
      (Q := Q3) (p := Cwave) (K := (1 : ℝ))
      hQ30 hcinv heps0 heps1 hwinCwave (by linarith [hEQ3]) hwin hgam.le hs
    have heq : (4 * (8 * (324 *
          Provider.BadEvents.responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
          ((Disorder.cstar M)⁻¹ * M.gamma)))) * (Cwave * epsilon ^ (-Cwave) / s ^ 2) =
        Q3 * (Disorder.cstar M)⁻¹ * epsilon ^ (-Cwave) * M.gamma * (s⁻¹) ^ 2 := by
      have hdiv : Cwave * epsilon ^ (-Cwave) / s ^ 2 =
          Cwave * epsilon ^ (-Cwave) * (s⁻¹) ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
      rw [hQ3def, hdiv]
      ring
    rw [heq]
    exact hpoly
  have hwaveScale2 : (4 * (8 * (324 *
        Provider.BadEvents.responseSensitivityConst d * (16 * Ccg + 8 * Ccg ^ 2) *
        ((Disorder.cstar M)⁻¹ * M.gamma)))) * 0 ≤
      0 * ((s⁻¹) ^ 4 * (epsilon ^ 2 *
        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) := by
    rw [mul_zero, zero_mul]
  have hT3 := (twoLaneEnvelope_waveTerm M m h hs hCinj0 hwaveM).mono_scales hwaveScale
    hwaveScale2
  -- the bad-event term
  have hGeq : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        (coefficientCutoffTriadicCoeffFamily M m omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))) ^ 2 =
      Observable.cutoffHomogenizationError M m
        ⟨s / 4, quarter_pos_of_eight_gamma_le M.shellPrefix.gamma_pos hs8⟩ omega ^ 2 := by
    filter_upwards [ae_sq_cutoffHomogenizationError_eq_homogenizationErrorOnCube_sq M m
      ⟨s / 4, quarter_pos_of_eight_gamma_le M.shellPrefix.gamma_pos hs8⟩] with omega homega
    exact homega.symm
  have hbadOrd :=
    MultiscaleAbsorptionArith.badOrdinaryAmplitude_le
      (T := (3 : ℝ) ^ (5 * ((h : ℕ) : ℝ)))
      (p := 5 * (2 * Chom') * Real.log 3 + 8) (Q4c := 608 * Ccg0)
      hCcg0 hcc hcinv hdR hgam hgam1 hs8
      (Real.rpow_pos_of_pos (by norm_num) _).le
      (three_rpow_five_waveCutoff_le hC0pos.le heps0 heps) (by positivity)
      heps0 heps1 hEpos hgammaE hwin hfloor hQ4adef hQ4bdef rfl hwinP hEQ4a hEQ4c
      hK4le
  have hbadRare :=
    MultiscaleAbsorptionArith.badRareAmplitude_le
      (Cms := Cms) hCcg0 hgam hgam1 hs hs1 heps0 heps1 hEpos hgammaE
      hERare (by linarith) hfloor hL4le hL40
  have hT4 := (twoLaneEnvelope_badTerm M m
    (quarter_pos_of_eight_gamma_le M.shellPrefix.gamma_pos hs8) hGeq hbadM).mono_scales
    hbadOrd hbadRare
  -- the deterministic remainder
  have hT5rem : (0 : ℝ) ≤ 1024 * (Cs * (48 * Ccg)) * M.gamma ^ 2 *
      (((h : ℕ) : ℝ) ^ 2 + (s ^ 2)⁻¹ + (E : ℝ) ^ 4 * |Real.log M.gamma| ^ 4) := by
    positivity
  have hT5 : TwoLaneEnvelope (cutoffSampleLaw M).toMeasure
      (fun _ : CutoffSample d => 1024 * (Cs * (48 * Ccg)) * M.gamma ^ 2 *
        (((h : ℕ) : ℝ) ^ 2 + (s ^ 2)⁻¹ + (E : ℝ) ^ 4 * |Real.log M.gamma| ^ 4))
      (K5 * ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)))
      (0 * ((s⁻¹) ^ 4 * (epsilon ^ 2 *
        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) :=
    TwoLaneEnvelope.of_le_const hT5rem
      (MultiscaleAbsorptionArith.remainderTerm_le
        (Cms := Cms) hQ50 hgam hgam1 hs hs1 heps0 heps1 E.2 hgammaE
        (Nat.cast_nonneg h) hhgap2E (by linarith) (by linarith) hfloor hK5le)
      (by simp) (Filter.Eventually.of_forall fun _ => le_rfl)
  refine TwoLaneEnvelope.of_ae_le ?_ hdisp
  exact (twoLaneEnvelope_fiveSum hS10 hS20 hK10 hK10 zero_le_one hK40 hK50 hL10 hL10
    le_rfl hL40 le_rfl hT1 hT2 hT3 hT4 hT5).mono_scales
    (mul_le_mul_of_nonneg_right hKtotle hS10)
    (mul_le_mul_of_nonneg_right hLtotle hS20)

/-! ## 10. The buckle, and `p.multiscale.estimate` on the carried premise -/

/-- **The endpoint for `p.multiscale.estimate`** — the frozen root's statement
body verbatim (`Frozen/Section3/MultiscaleEstimate.lean`), with the one carried
premise `mStarStar M < m` inserted immediately before the induction state; the
name records the gate.

That premise is not a weakening of the mathematics: it is the landmark gate of
`l.shom.continuity`, inherited verbatim by BOTH of the buckle's proved inputs
(`Provider.Localization.localization_mathcalE_estimate_ae_unconditional` and
`exists_badEventSummed_bound`), and the frozen root — like the manuscript's
Proposition `p.multiscale.estimate` — carries no such binder.  The
complementary branch is now `m <= mStarStar M`, and it is proved as
`multiscale_estimate_of_le_mStarStar` (`MultiscaleBaseBranch.lean`); nothing in
this module supplies it, and no proved producer of the display is free of the
gate.  See the module header, "The scale gate on `m`" and "The carried
premise".

Everything else is the frozen root, binder for binder and amplitude spelling
for amplitude spelling: one `(Y, Z)` pair serves both the main conjunct and the
refinement clause, and the refinement clause is discharged unconditionally --
its `s <= Cms eps` hypothesis is consumed by nothing. -/
theorem multiscale_estimate_of_mStarStar (d : ℕ) :
    ∃ Cms : ℝ, 0 < Cms ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m →
        Algsuperdiff.Frozen.Section3.inductionState M (m - 1) E →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          (Disorder.cstar M)⁻¹ * epsilon ^ (-Cms) ≤ (E : ℝ) →
          M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            ∃ Y Z : Cutoff.CutoffSample d → ℝ,
              Probability.IsTwoTermBigOWithWitnesses
                  (Cutoff.cutoffSampleLaw M).toMeasure
                  (HCPolySupport.IndependentSums.gammaSigma 2)
                  (HCPolySupport.IndependentSums.gammaSigma (1 / 2))
                  (Observable.cutoffHomogenizationError M m
                    ⟨s,
                      (mul_pos (by norm_num : (0 : ℝ) < 8)
                        M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
                  Y Z
                  (Cms * (E : ℝ) * s⁻¹ *
                    Real.sqrt (epsilon * M.gamma))
                  (Cms * epsilon * (s⁻¹) ^ 2 *
                    Real.exp
                      (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) ∧
                (s ≤ Cms * epsilon →
                  HCPolySupport.IndependentSums.IsBigOWith
                    (Cutoff.cutoffSampleLaw M).toMeasure
                    (HCPolySupport.IndependentSums.gammaSigma 2)
                    Y
                    (Cms * epsilon * (E : ℝ) * s⁻¹ *
                      Real.sqrt M.gamma)) := by
  by_cases hd : d = 0
  · refine ⟨1, one_pos, ?_⟩
    intro M
    exact absurd (Provider.Orlicz.dim_pos_of_model M) (by omega)
  · have : NeZero d := ⟨hd⟩
    obtain ⟨Cms, Ktot, Ltot, hCms0, hCms4, hKtot0, hLtot0, hsqK, hsqL, henv⟩ :=
      exists_absorbed_envelope d
    refine ⟨Cms, hCms0, ?_⟩
    intro M m E hmStar hS epsilon hepsilon hwin hgammaE s hsWindow
    have heps0 : (0 : ℝ) < epsilon := hepsilon.1
    have heps1 : epsilon ≤ 1 := by linarith [hepsilon.2]
    have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
    have hs : (0 : ℝ) < s :=
      (mul_pos (by norm_num : (0 : ℝ) < 8) hgam).trans_le hsWindow.1
    have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one E.2
    obtain ⟨U, V, hUm, hVm, _, _, hUt, hVt, hdom⟩ :=
      henv M m E hmStar hS epsilon hepsilon hwin hgammaE s hsWindow
    have hA1 : (0 : ℝ) <
        Ktot * ((s⁻¹) ^ 2 * (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma)) := by positivity
    have hA2 : (0 : ℝ) < Ltot * ((s⁻¹) ^ 4 * (epsilon ^ 2 *
        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) := by positivity
    have hXm : Measurable (fun omega => Observable.cutoffHomogenizationError M m
        ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8)
          M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩ omega ^ 2) :=
      (Observable.measurable_cutoffHomogenizationError M m _).pow_const 2
    obtain ⟨Y', Z', hw, _, _⟩ :=
      exists_witnesses_of_envelope hA1 hA2 hXm hUm hVm hUt hVt hdom
    have hbuck := Provider.Orlicz.isTwoTermBigOWithWitnesses_sqrt_of_sq_one_quarter
      (Observable.cutoffHomogenizationError_nonneg M m _) hw
    have hAmp1 : Real.sqrt (Ktot * ((s⁻¹) ^ 2 *
        (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma))) ≤
        Cms * (E : ℝ) * s⁻¹ * Real.sqrt (epsilon * M.gamma) :=
      sqrtOrdinaryLane_le_frozen hKtot0.le hs heps0.le heps1 hEpos.le hsqK
    have hAmp2 : Real.sqrt (Ltot * ((s⁻¹) ^ 4 * (epsilon ^ 2 *
        Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))))) ≤
        Cms * epsilon * (s⁻¹) ^ 2 *
          Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) := by
      have hassoc : (2 : ℝ) * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹ =
          2 * (((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹) := by ring
      rw [hassoc]
      exact sqrtRareLane_le_frozen hLtot0.le hs heps0.le hsqL
    have hAmpRef : Real.sqrt (Ktot * ((s⁻¹) ^ 2 *
        (epsilon ^ 2 * (E : ℝ) ^ 2 * M.gamma))) ≤
        Cms * epsilon * (E : ℝ) * s⁻¹ * Real.sqrt M.gamma :=
      sqrtOrdinaryLane_le_refinement hKtot0.le hs heps0.le hEpos.le hsqK
    have hYt := hbuck.2.2.2.2.2.2.2.2.1
    refine ⟨fun omega => Real.sqrt (max (Y' omega) 0),
      fun omega => Real.sqrt (max (Z' omega) 0),
      Provider.Orlicz.isTwoTermBigOWithWitnesses_mono_scales hbuck hAmp1 hAmp2,
      fun _ => hYt.mono_scale hAmpRef⟩

end

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
