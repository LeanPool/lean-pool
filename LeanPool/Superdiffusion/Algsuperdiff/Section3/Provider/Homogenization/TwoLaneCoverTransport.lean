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
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverConstant
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverDepth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# TwoLaneCoverTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Lane-separated observation-scale cover transport

This module transports the two-term homogenization-error clause from the
cutoff cube to a larger observation cube **without merging the two Orlicz
lanes**.

The grid concentration display of ABK26 is printed with two separate lanes,

`O_{Gamma_1}(E^2 gamma 3^{-d(m-n)/2}) +
  O_{Gamma_{1/4}}(exp(-E^{-3} gamma^{-1}) 3^{-d(m-n)/2})`,

and it is obtained by citing `e.new.induction.for.shom` at the *mixed* scale
pair (coefficient cutoff `L`, observed cube `n`).  Those two printed lanes are
the squares of the two lanes `(Gamma_2, Gamma_{1/2})` of the preceding-error
clause, at the squared amplitudes: the per-site producers square the mixed-scale
error once, lane by lane, through `e.powerofGammasigma`.  Consequently the
printed separation survives only if the transport from the cutoff cube to the
observation cube is itself performed lane by lane, in the
`(Gamma_2, Gamma_{1/2})` form.

The proved transport `observationScaleFiniteCover_sq_isBigOWith_gammaQuarter`
squares the error *before* transporting it and therefore delivers a single
`Gamma_{1/4}` envelope at the merged amplitude `A ^ 2 + B ^ 2`, which is what
the fourth moment of the corrected Step 4 needs but which cannot be reopened
into the two printed lanes.  This module produces the lane-separated form
instead: same mechanism, run once per lane.

## Route

The mechanism is the proved one, run **once per lane** instead of once on the
merged square.

1. *The two lanes at the cutoff scale.*  The clause is a two-term relation, so
   it comes with measurable witnesses `Y` and `Z` and a pointwise domination
   `mathcal E <= Y + Z`, with `Y` in `Gamma_2(A)` and `Z` in
   `Gamma_{1/2}(B)`.  Translation covariance of the cutoff sample law gives
   the same witnesses, with the same two amplitudes, at every translated
   scale-`L` cell of the observation cube.

2. *The deterministic finite cover.*  The squared raw error of the observation
   cube `square_m` splits, at every sample point, into the `m - L` coarse
   layers -- each dominated by a maximum over that layer's parents of the
   average over their scale-`L` descendants -- and a geometrically damped fine
   tail dominated by the maximum over all scale-`L` descendants.  Every step is
   monotone in the cell family, and the two maxima are subadditive, so the
   cover of the cell squares by `2 max(0,Y)^2 + 2 max(0,Z)^2` splits the whole
   deterministic bound into *one cover functional per lane*
   (`laneTotal`).

3. *The probabilistic aggregation, at each lane's own exponent.*  The square
   rule `e.powerofGammasigma` sends the `Gamma_2` lane to `Gamma_1` and the
   `Gamma_{1/2}` lane to `Gamma_{1/4}`, at the squared amplitudes.  The cover
   functional of a family with a common `Gamma_sigma` scale `K` is then
   `Gamma_sigma` at `C(d, sigma) K`: the descendant average is free
   (`isBigO_finsetAverage_of_isBigO_gammaSigma_aemeasurable`), each layer
   maximum costs `(3 max(1, log N))^{1/sigma}` (`l.maximums.Gamma.s`), which the
   geometric weight `3^{-ell/4}` absorbs, and the layers are summed by the
   countable triangle inequality `l.Gamma.sigma.triangle`, whose strict
   positivity premise is met by the strictly positive geometric majorant
   `laneDepthScale`.  This is run at `sigma = 1` and at `sigma = 1/4`.

4. *The square root.*  Each lane's cover functional is a square: `sqrt` of the
   `Gamma_1` lane is `Gamma_2` at `sqrt(2 C_1) A` and `sqrt` of the
   `Gamma_{1/4}` lane is `Gamma_{1/2}` at `sqrt(2 C_{1/4}) B`, by the same power
   rule read backwards.  The observation-cube error is nonnegative and its
   square is at most the sum of the two lane functionals, hence at most the sum
   of the two square roots: the two-term relation of the printed display.

No comparator change occurs anywhere: the coefficient cutoff is `a_L` and the
normalizer is `sigmabar_L` at the cell scale, at every intermediate scale, and
at the observation cube.  The only scale comparison is the half-discount one
already used by the proved transport: the clause is read at the window `s =
1/16` and the observation-cube error is produced at the discount `1/8`.

The construction is spread over three modules that are one development.  The
deterministic cover of step 2 is
`Provider/Homogenization/TwoLaneCoverDepth.lean`; the layer scales and the
dimension-only constant `laneCoverConst` used by step 3 are
`Provider/Homogenization/TwoLaneCoverConstant.lean`; this module carries steps
1, 3 and 4 and the endpoint.

## References

* ABK26, proof of `p.homogenization.step`; the printed lane separation is
  the two-line display, cited there from `e.new.induction.for.shom` and
  `p.concentration`, for `L <= n <= m - 1`.
* ABK26, `l.Gamma.sigma.triangle`; `l.maximums.Gamma.s`;
  `e.powerofGammasigma` (inside `l.o.gamma2.mult`); the Appendix tail
  conventions.
* Here that cover is run at a general exponent, where the maximum costs `(3
  max(1, log N))^{1/sigma}`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Homogenization.TwoLaneCoverInternal
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ## The cover functional of one lane, at that lane's own exponent -/

omit [NeZero d] in
private theorem descendantsAverage_isBigOWith (M : ABKModel d)
    (P : HCPolySupport.TriadicCube d) (j : ℕ) {σ K : ℝ} (hσ : 0 < σ)
    (hK : 0 < K) {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg0 : ∀ R omega, 0 ≤ g R omega) (hgm : ∀ R, Measurable (g R))
    (hgt : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma σ) (g R) K) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
      (fun omega => descendantsAverage P j (fun R => g R omega))
      (gammaTriangleConst σ * K) := by
  classical
  have htail : ∀ R ∈ descendantsAtDepth P j,
      IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ) (g R) K := by
    intro R _
    exact (Orlicz.isBigOWith_iff_isBigO_of_nonneg (fun omega => hg0 R omega)).1
      (hgt R)
  have haverage := Ch04.isBigO_finsetAverage_of_isBigO_gammaSigma_aemeasurable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (descendantsAtDepth P j)
    (X := fun R => g R) (a := fun _ => K) (σ := σ) hσ
    (descendantsAtDepth_nonempty P j) (fun _ _ => hK) htail
    (fun R => (hgm R).aemeasurable)
  have hscale : (((descendantsAtDepth P j).card : ℝ)⁻¹) *
      ∑ _ ∈ descendantsAtDepth P j, K = K := by
    have hcard : ((descendantsAtDepth P j).card : ℝ) ≠ 0 := by
      exact_mod_cast (descendantsAtDepth_nonempty P j).card_ne_zero
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hnonneg : ∀ omega, 0 ≤ descendantsAverage P j (fun R => g R omega) :=
    fun omega => descendantsAverage_nonneg P j _ fun R _ => hg0 R omega
  apply (Orlicz.isBigOWith_iff_isBigO_of_nonneg hnonneg).2
  simpa only [descendantsAverage, hscale] using haverage

omit [NeZero d] in
private theorem laneParentAverage_isBigOWith (M : ABKModel d) (L m : ℤ)
    (ell : ℕ) {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg0 : ∀ R omega, 0 ≤ g R omega) (hgm : ∀ R, Measurable (g R))
    (hgt : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma σ) (g R) K) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
      (laneParentAverage L m g ell)
      ((3 * max 1 (Real.log (((3 ^ d) ^ ell : ℕ) : ℝ))) ^ σ⁻¹ *
        (gammaTriangleConst σ * K)) := by
  classical
  have hk : m - (ell : ℤ) ≤ (originCube d m).scale :=
    sub_le_self m (by exact_mod_cast Nat.zero_le ell)
  have hD : (descendantsAtScale (originCube d m) (m - (ell : ℤ))).Nonempty :=
    descendantsAtScale_nonempty _ hk
  have hDcard : (descendantsAtScale (originCube d m) (m - (ell : ℤ))).card =
      (3 ^ d) ^ ell := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hk,
      descendantsAtDepth_card]
    have hdepth : ((originCube d m).scale - (m - (ell : ℤ))).toNat = ell := by
      change (m - (m - (ell : ℤ))).toNat = ell
      rw [sub_sub_cancel]
      exact_mod_cast Int.toNat_of_nonneg
        (show (0 : ℤ) ≤ (ell : ℤ) by exact_mod_cast Nat.zero_le ell)
    exact congrArg (fun n => (3 ^ d) ^ n) hdepth
  have hX : ∀ P ∈ descendantsAtScale (originCube d m) (m - (ell : ℤ)),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
        (fun omega => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => g R omega)) (gammaTriangleConst σ * K) := by
    intro P _
    exact descendantsAverage_isBigOWith M P (Int.toNat (m - (ell : ℤ) - L))
      hσ hK hg0 hgm hgt
  have hmax := Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (descendantsAtScale (originCube d m) (m - (ell : ℤ))) hD
    (X := fun P omega => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
      (fun R => g R omega))
    (A := gammaTriangleConst σ * K) (σ := σ) hσ
    (mul_nonneg gammaTriangleConst_pos.le hK.le) hX
  have hfun : (fun omega =>
      (descendantsAtScale (originCube d m) (m - (ell : ℤ))).sup' hD
        (fun P => descendantsAverage P (Int.toNat (m - (ell : ℤ) - L))
          (fun R => g R omega))) = laneParentAverage L m g ell := by
    funext omega
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' _ hD _).symm
  simpa only [hfun, hDcard] using hmax

omit [NeZero d] in
private theorem laneCoarse_isBigOWith (M : ABKModel d) (L m : ℤ)
    {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg0 : ∀ R omega, 0 ≤ g R omega) (hgm : ∀ R, Measurable (g R))
    (hgt : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma σ) (g R) K) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
      (laneCoarse L m g)
      (gammaTriangleConst σ *
        ((∑' ell : ℕ, laneDepthScale d σ ell) * K)) := by
  classical
  let X : ℕ → Cutoff.CutoffSample d → ℝ := fun ell omega =>
    if ell < Int.toNat (m - L) then
      Ch02.geometricWeight (1 / 8) 2 ell * laneParentAverage L m g ell omega
    else 0
  let scale : ℕ → ℝ := fun ell => laneDepthScale d σ ell * K
  have hXnonneg : ∀ ell omega, 0 ≤ X ell omega := by
    intro ell omega
    dsimp only [X]
    split_ifs
    · exact mul_nonneg (geometricWeight_eighth_two_nonneg ell)
        (laneParentAverage_nonneg L m hg0 ell omega)
    · norm_num
  have hXmeas : ∀ ell, Measurable (X ell) := by
    intro ell
    dsimp only [X]
    split_ifs
    · exact measurable_const.mul (laneParentAverage_measurable L m hgm ell)
    · exact measurable_const
  have hscalePos : ∀ ell, 0 < scale ell := fun ell =>
    mul_pos (laneDepthScale_pos d σ ell) hK
  have hscaleSum : Summable scale :=
    (summable_laneDepthScale d σ).mul_right K
  have hXtail : ∀ ell, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma σ) (X ell) (scale ell) := by
    intro ell
    dsimp only [X]
    split_ifs with hell
    · have hparent := laneParentAverage_isBigOWith M L m ell hσ hK hg0 hgm hgt
      have hmul := hparent.const_mul (geometricWeight_eighth_two_nonneg ell)
      apply hmul.mono_scale
      have hlog := Algsuperdiff.Probability.max_log_three_pow_le d ell
      have hbase0 : 0 ≤ 3 * max 1 (Real.log (((3 ^ d) ^ ell : ℕ) : ℝ)) :=
        mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
      have hbaseLe : 3 * max 1 (Real.log (((3 ^ d) ^ ell : ℕ) : ℝ)) ≤
          3 * ((1 + (d : ℝ) * Real.log 3) * (1 + (ell : ℝ))) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
      have hpowLe := Real.rpow_le_rpow hbase0 hbaseLe (inv_nonneg.mpr hσ.le)
      have hrest0 : 0 ≤ gammaTriangleConst σ * K :=
        mul_nonneg gammaTriangleConst_pos.le hK.le
      dsimp only [scale, laneDepthScale]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowLe
          (geometricWeight_eighth_two_nonneg ell)) hrest0
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
        (inv_nonneg.mpr (Real.exp_pos (t ^ σ)).le)
  have hsumTail := Orlicz.isBigOWith_gammaSigma_tsum
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (σ := σ) hσ hXnonneg hXmeas
    hscalePos hscaleSum hXtail
  have hfun : (fun omega => ∑' ell, X ell omega) = laneCoarse L m g := by
    funext omega
    have hfinite : (∑' ell, X ell omega) =
        ∑ ell ∈ Finset.range (Int.toNat (m - L)), X ell omega := by
      refine tsum_eq_sum (s := Finset.range (Int.toNat (m - L))) fun ell hell => ?_
      rw [Finset.mem_range, not_lt] at hell
      simp only [X, ite_eq_right (not_lt.mpr hell)]
    rw [hfinite]
    unfold laneCoarse
    refine Finset.sum_congr rfl fun ell hell => ?_
    simp only [X, ite_eq_left (Finset.mem_range.mp hell)]
  have hscaleEq : (∑' ell, scale ell) =
      (∑' ell, laneDepthScale d σ ell) * K := tsum_mul_right
  simpa only [hfun, hscaleEq] using hsumTail

omit [NeZero d] in
private theorem laneCellSup_isBigOWith (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hgt : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma σ) (g R) K) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
      (laneCellSup L m g)
      ((3 * max 1 (Real.log (((3 ^ d) ^ Int.toNat (m - L) : ℕ) : ℝ))) ^ σ⁻¹ *
        K) := by
  classical
  have hD : (descendantsAtScale (originCube d m) L).Nonempty :=
    descendantsAtScale_nonempty _ hLm
  have hDcard : (descendantsAtScale (originCube d m) L).card =
      (3 ^ d) ^ Int.toNat (m - L) := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hLm,
      descendantsAtDepth_card]
    rfl
  have hmax := Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (descendantsAtScale (originCube d m) L) hD
    (X := fun R => g R) (A := K) (σ := σ) hσ hK.le (fun R _ => hgt R)
  have hfun : (fun omega =>
      (descendantsAtScale (originCube d m) L).sup' hD
        (fun R => g R omega)) = laneCellSup L m g := by
    funext omega
    exact (Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' _ hD _).symm
  simpa only [hfun, hDcard] using hmax

omit [NeZero d] in
private theorem laneTotal_isBigOWith (M : ABKModel d) (L m : ℤ) (hLm : L ≤ m)
    {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K)
    {g : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ}
    (hg0 : ∀ R omega, 0 ≤ g R omega) (hgm : ∀ R, Measurable (g R))
    (hgt : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma σ) (g R) K) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
      (laneTotal L m g) (laneCoverConst d σ * K) := by
  have hcoarse := laneCoarse_isBigOWith M L m hσ hK hg0 hgm hgt
  have hsup := laneCellSup_isBigOWith M L m hLm hσ hK hgt
  have hfine : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma σ)
      (fun omega => laneFineFactor (Int.toNat (m - L)) *
        laneCellSup L m g omega)
      (laneFineDepthScale d σ (Int.toNat (m - L)) * K) := by
    have hscaled := hsup.const_mul (laneFineFactor_nonneg (Int.toNat (m - L)))
    apply hscaled.mono_scale
    have hlog := Algsuperdiff.Probability.max_log_three_pow_le d
      (Int.toNat (m - L))
    have hbase0 : 0 ≤ 3 * max 1
        (Real.log (((3 ^ d) ^ Int.toNat (m - L) : ℕ) : ℝ)) :=
      mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
    have hbaseLe : 3 * max 1
        (Real.log (((3 ^ d) ^ Int.toNat (m - L) : ℕ) : ℝ)) ≤
        3 * ((1 + (d : ℝ) * Real.log 3) *
          (1 + (Int.toNat (m - L) : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    have hpowLe := Real.rpow_le_rpow hbase0 hbaseLe (inv_nonneg.mpr hσ.le)
    unfold laneFineDepthScale
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpowLe
        (laneFineFactor_nonneg (Int.toNat (m - L)))) hK.le
  have hmerge := Tail.isBigOWith_gammaSigma_add_of_nonneg
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (σ := σ) hσ
    (mul_nonneg gammaTriangleConst_pos.le
      (mul_nonneg (tsum_nonneg fun r => (laneDepthScale_pos d σ r).le) hK.le))
    (mul_nonneg (laneFineDepthScale_pos d σ (Int.toNat (m - L))).le hK.le)
    hcoarse hfine
  refine hmerge.mono_scale ?_
  have hdepthLe : laneFineDepthScale d σ (Int.toNat (m - L)) ≤
      ∑' r : ℕ, laneFineDepthScale d σ r := by
    have hsum := summable_laneFineDepthScale d σ
    have hsingleton := hsum.sum_le_tsum {Int.toNat (m - L)}
      (fun r _ => (laneFineDepthScale_pos d σ r).le)
    simpa using hsingleton
  have hdepthTotal : 0 ≤ gammaTriangleConst σ *
      (∑' r : ℕ, laneDepthScale d σ r) :=
    mul_nonneg gammaTriangleConst_pos.le
      (tsum_nonneg fun r => (laneDepthScale_pos d σ r).le)
  have hfineTotal : 0 ≤ ∑' r : ℕ, laneFineDepthScale d σ r :=
    tsum_nonneg fun r => (laneFineDepthScale_pos d σ r).le
  have hfac : 0 ≤ 2 * (3 * max 1 (Real.log 2)) ^ σ⁻¹ := by
    have : (0 : ℝ) ≤ 3 * max 1 (Real.log 2) :=
      mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
    positivity
  have hmax : max (gammaTriangleConst σ *
        ((∑' r : ℕ, laneDepthScale d σ r) * K))
      (laneFineDepthScale d σ (Int.toNat (m - L)) * K) ≤
      (gammaTriangleConst σ * (∑' r : ℕ, laneDepthScale d σ r) +
        ∑' r : ℕ, laneFineDepthScale d σ r) * K := by
    refine max_le ?_ ?_
    · nlinarith [mul_nonneg hfineTotal hK.le]
    · nlinarith [mul_le_mul_of_nonneg_right hdepthLe hK.le,
        mul_nonneg hdepthTotal hK.le]
  unfold laneCoverConst
  calc 2 * ((3 * max 1 (Real.log 2)) ^ σ⁻¹ *
        max (gammaTriangleConst σ *
            ((∑' r : ℕ, laneDepthScale d σ r) * K))
          (laneFineDepthScale d σ (Int.toNat (m - L)) * K))
      = 2 * (3 * max 1 (Real.log 2)) ^ σ⁻¹ *
        max (gammaTriangleConst σ *
            ((∑' r : ℕ, laneDepthScale d σ r) * K))
          (laneFineDepthScale d σ (Int.toNat (m - L)) * K) := by ring
    _ ≤ 2 * (3 * max 1 (Real.log 2)) ^ σ⁻¹ *
        ((gammaTriangleConst σ * (∑' r : ℕ, laneDepthScale d σ r) +
          ∑' r : ℕ, laneFineDepthScale d σ r) * K) :=
        mul_le_mul_of_nonneg_left hmax hfac
    _ ≤ (1 + 2 * (3 * max 1 (Real.log 2)) ^ σ⁻¹ *
        (gammaTriangleConst σ * (∑' r : ℕ, laneDepthScale d σ r) +
          ∑' r : ℕ, laneFineDepthScale d σ r)) * K := by nlinarith [hK.le]

/-! ## The two lanes of a single cell -/

/-- The squared raw cell error is, almost everywhere, the square of the genuine
cutoff error observable read at the translated sample. -/
private theorem laneCellErrorRawSq_ae_eq (M : ABKModel d) (L : ℤ)
    (R : HCPolySupport.TriadicCube d) (hR : R.scale = L) :
    laneCellErrorRawSq M L R =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      fun omega =>
        (Observable.cutoffHomogenizationError M L ⟨(1 / 16 : ℝ), by norm_num⟩
          (Cutoff.translateCutoffSample
            (HCPolySupport.triadicCubeShift R) omega)) ^ 2 := by
  have hτ : MeasurePreserving
      (Cutoff.translateCutoffSample (HCPolySupport.triadicCubeShift R))
      (Cutoff.cutoffSampleLaw M).toMeasure
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    refine ⟨Cutoff.measurable_translateCutoffSample
      (HCPolySupport.triadicCubeShift R), ?_⟩
    exact Cutoff.map_translateCutoffSample_cutoffSampleLaw M
      (HCPolySupport.triadicCubeShift R)
  have horigin := Observable.cutoffHomogenizationErrorRaw_ae_eq_representative
    M L L (by norm_num : (0 : ℝ) < 1 / 16) (Annealed.sigmaBar M L)
  have htranslated := hτ.quasiMeasurePreserving.ae_eq_comp horigin
  filter_upwards [htranslated] with omega homega
  change (Ch02.HomogenizationErrorOnCube R (1 / 16) .infinity (.finite 2)
      (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L))) ^ 2 = _
  rw [BadEvents.homogenizationErrorOnCube_translateCutoffSample
    M L R (1 / 16) .infinity (.finite 2)
      (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M L)) omega, hR]
  have hchar := Observable.cutoffHomogenizationErrorRaw_characterization
    M L L (1 / 16) (Annealed.sigmaBar M L)
    (Cutoff.translateCutoffSample (HCPolySupport.triadicCubeShift R) omega)
  rw [← hchar]
  exact congrArg (fun x : ℝ => x ^ 2) homega

/-! ## The endpoint -/

private theorem twoLaneTransport_cell_ae_bound :
    ∀ (d : ℕ) (M : ABKModel d) (L : ℤ),
      NeZero d →
        ∀ (Yw Zw : TriadicCube d → Cutoff.CutoffSample d → ℝ),
          (∀ (R : TriadicCube d) (ω : Cutoff.CutoffSample d),
              (fun (omega : Cutoff.CutoffSample d) =>
                    Observable.cutoffHomogenizationError M L ⟨(1 / 16 : ℝ), by norm_num⟩
                      (Cutoff.translateCutoffSample (triadicCubeShift R) omega))
                  ω ≤
                Yw R ω + Zw R ω) →
            let Ycell : TriadicCube d → Cutoff.CutoffSample d → ℝ :=
              fun (R : TriadicCube d) (omega : Cutoff.CutoffSample d) => (2 : ℝ) * max (0 : ℝ) (Yw
                R omega) ^ (2 : ℕ);
            (Ycell = fun (R : TriadicCube d) (omega : Cutoff.CutoffSample d) =>
                (2 : ℝ) * max (0 : ℝ) (Yw R omega) ^ (2 : ℕ)) →
              let Zcell : TriadicCube d → Cutoff.CutoffSample d → ℝ :=
                fun (R : TriadicCube d) (omega : Cutoff.CutoffSample d) => (2 : ℝ) * max (0 : ℝ)
                  (Zw R omega) ^ (2 : ℕ);
              (Zcell = fun (R : TriadicCube d) (omega : Cutoff.CutoffSample d) =>
                  (2 : ℝ) * max (0 : ℝ) (Zw R omega) ^ (2 : ℕ)) →
                ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                  (Cutoff.CutoffSample d)),
                  ∀ (R : TriadicCube d), R.scale = L → laneCellErrorRawSq M L R omega ≤ Ycell R
                    omega + Zcell R omega := by
  intro _ M L _ Yw Zw hdom _ hYcell _ hZcell
  rw [MeasureTheory.ae_all_iff]
  intro R
  by_cases hR : R.scale = L
  · filter_upwards [laneCellErrorRawSq_ae_eq M L R hR] with omega homega
    intro _
    rw [homega]
    have hX0 : 0 ≤ Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩
        (Cutoff.translateCutoffSample
          (HCPolySupport.triadicCubeShift R) omega) :=
      Observable.cutoffHomogenizationError_nonneg M L _ _
    have hdomega := hdom R omega
    have hP : Yw R omega ≤ max 0 (Yw R omega) := le_max_right _ _
    have hQ : Zw R omega ≤ max 0 (Zw R omega) := le_max_right _ _
    have hP0 : (0 : ℝ) ≤ max 0 (Yw R omega) := le_max_left _ _
    have hQ0 : (0 : ℝ) ≤ max 0 (Zw R omega) := le_max_left _ _
    have hle : Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩
        (Cutoff.translateCutoffSample
          (HCPolySupport.triadicCubeShift R) omega) ≤
        max 0 (Yw R omega) + max 0 (Zw R omega) := by
      linarith
    rw [hYcell, hZcell]
    nlinarith [sq_nonneg (max 0 (Yw R omega) - max 0 (Zw R omega)),
      mul_self_le_mul_self hX0 hle]
  · exact Filter.Eventually.of_forall fun _ hcon => (hR hcon).elim

private theorem twoLaneTransport_pointwiseDomination :
    ∀ (d : ℕ) (M : ABKModel d) (_ L n : ℤ),
      ∀ (Yw Zw : (R : TriadicCube d) → Cutoff.CutoffSample d → ℝ),
        let Ycell : TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (R : TriadicCube d) (omega :
          Cutoff.CutoffSample d) =>
          (2 : ℝ) * max (0 : ℝ) (Yw R omega) ^ (2 : ℕ);
        let Zcell : TriadicCube d → Cutoff.CutoffSample d → ℝ := fun (R : TriadicCube d) (omega :
          Cutoff.CutoffSample d) =>
          (2 : ℝ) * max (0 : ℝ) (Zw R omega) ^ (2 : ℕ);
        ∀
          (_ :
            ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
              (Cutoff.CutoffSample d)),
              Observable.cutoffHomogenizationErrorRepresentative M L n
                (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega ^ (2 : ℕ) ≤
                laneTotal L n Ycell omega + laneTotal L n Zcell omega)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ laneTotal L n Ycell omega)
          (_ : ∀ (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ laneTotal L n Zcell omega),
          ∀ᵐ (omega : Cutoff.CutoffSample d) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
            (Cutoff.CutoffSample d)),
            Observable.cutoffHomogenizationErrorRepresentative M L n
              (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega ≤
              √(laneTotal L n Ycell omega) + √(laneTotal L n Zcell omega) := by
  intro _ M m L n _ _ Ycell Zcell hRepAE hUnonneg hVnonneg
  filter_upwards [hRepAE] with omega homega
  have h0 : 0 ≤ Observable.cutoffHomogenizationErrorRepresentative M L n
      (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega :=
    Observable.cutoffHomogenizationErrorRepresentative_nonneg M L n _ _ omega
  have hsum : laneTotal L n Ycell omega + laneTotal L n Zcell omega ≤
      (Real.sqrt (laneTotal L n Ycell omega) +
        Real.sqrt (laneTotal L n Zcell omega)) ^ 2 := by
    have h1 : Real.sqrt (laneTotal L n Ycell omega) ^ 2 =
        laneTotal L n Ycell omega := Real.sq_sqrt (hUnonneg omega)
    have h2 : Real.sqrt (laneTotal L n Zcell omega) ^ 2 =
        laneTotal L n Zcell omega := Real.sq_sqrt (hVnonneg omega)
    nlinarith [Real.sqrt_nonneg (laneTotal L n Ycell omega),
      Real.sqrt_nonneg (laneTotal L n Zcell omega)]
  calc Observable.cutoffHomogenizationErrorRepresentative M L n
        (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega
      = Real.sqrt ((Observable.cutoffHomogenizationErrorRepresentative M L n
          (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega) ^ 2) :=
        (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (laneTotal L n Ycell omega +
          laneTotal L n Zcell omega) := Real.sqrt_le_sqrt homega
    _ ≤ Real.sqrt ((Real.sqrt (laneTotal L n Ycell omega) +
          Real.sqrt (laneTotal L n Zcell omega)) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (laneTotal L n Ycell omega) +
          Real.sqrt (laneTotal L n Zcell omega) :=
        Real.sqrt_sq (by positivity)

/-- **Lane-separated observation-scale transport of the preceding-error
clause.**

From the preceding-error clause at the induction scale `m`, read at the
single window `1/16`, the mixed-scale homogenization error at coefficient
cutoff `L` and observation cube `n` obeys a two-term
`(Gamma_2, Gamma_{1/2})` bound with the *same two lanes* and the two
amplitudes of the clause, inflated only by one dimension-only constant.  The
constant is chosen before the model, the induction scale, the amplitude
parameter and the two scales.

This is a Provider endpoint: it carries no source-node status by itself. -/
theorem exists_twoLaneObservationScaleTransport (d : ℕ) :
    ∃ Ctwo : ℝ, 1 ≤ Ctwo ∧
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
        ∀ L n : ℤ, L ≤ m - 1 → L ≤ n →
          Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
            (gammaSigma 2) (gammaSigma (1 / 2))
            (@Observable.cutoffHomogenizationErrorRepresentative d M L n
              (1 / 8) (Annealed.sigmaBar M L))
            (Ctwo * ((E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma))
            (Ctwo *
              (((1 / 16 : ℝ)⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) := by
  classical
  refine ⟨max 1 (max (Real.sqrt (2 * laneCoverConst d 1))
      (Real.sqrt (2 * laneCoverConst d (1 / 4)))), le_max_left _ _, ?_⟩
  intro M m E hLower hWindow L n hL hLn
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  set Ctwo : ℝ := max 1 (max (Real.sqrt (2 * laneCoverConst d 1))
    (Real.sqrt (2 * laneCoverConst d (1 / 4)))) with hCtwo
  set A : ℝ := (E : ℝ) * (1 / 16 : ℝ)⁻¹ * Real.sqrt M.gamma with hA
  set B : ℝ := ((1 / 16 : ℝ)⁻¹) ^ 2 *
    Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) with hB
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one E.property)
      (inv_pos.mpr (by norm_num)))
      (Real.sqrt_pos.2 M.shellPrefix.gamma_pos)
  have hBpos : 0 < B := by
    rw [hB]
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr (by norm_num))) (Real.exp_pos _)
  have hCtwoPos : 0 < Ctwo := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLowerL : Probability.IsTwoTermBigOWith
      (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2))
      (Observable.cutoffHomogenizationError M L
        ⟨(1 / 16 : ℝ), by norm_num⟩) A B := by
    simpa only [hA, hB] using hLower L hL (1 / 16) hWindow
  -- the two lanes of every translated cell, with the two amplitudes of the clause
  have hcellTwo : ∀ R : HCPolySupport.TriadicCube d,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2))
        (fun omega =>
          Observable.cutoffHomogenizationError M L
            ⟨(1 / 16 : ℝ), by norm_num⟩
            (Cutoff.translateCutoffSample
              (HCPolySupport.triadicCubeShift R) omega)) A B := fun R =>
    BadEvents.isTwoTermBigOWith_comp_translateCutoffSample M
      (HCPolySupport.triadicCubeShift R) hLowerL
  choose Yw Zw _hYadm _hZadm _hApos' _hBpos' _hXmeas hYmeas hZmeas hdom
    hYtail hZtail using hcellTwo
  set Ycell : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ :=
    fun R omega => 2 * (max 0 (Yw R omega)) ^ 2 with hYcell
  set Zcell : HCPolySupport.TriadicCube d → Cutoff.CutoffSample d → ℝ :=
    fun R omega => 2 * (max 0 (Zw R omega)) ^ 2 with hZcell
  have hYcell0 : ∀ R omega, 0 ≤ Ycell R omega := by
    intro R omega
    rw [hYcell]
    positivity
  have hZcell0 : ∀ R omega, 0 ≤ Zcell R omega := by
    intro R omega
    rw [hZcell]
    positivity
  have hYcellMeas : ∀ R, Measurable (Ycell R) := by
    intro R
    rw [hYcell]
    exact measurable_const.mul ((measurable_const.max (hYmeas R)).pow_const 2)
  have hZcellMeas : ∀ R, Measurable (Zcell R) := by
    intro R
    rw [hZcell]
    exact measurable_const.mul ((measurable_const.max (hZmeas R)).pow_const 2)
  have hYcellTail : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 1) (Ycell R) (2 * A ^ 2) := by
    intro R
    have hmax0 := Tail.isBigOWith_max_zero hApos (hYtail R)
    have hsq := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := fun omega => max 0 (Yw R omega)) (K := A) (σ := 2)
      hApos.le (fun omega => le_max_left _ _)).1 hmax0
    rw [show (2 : ℝ) / 2 = 1 by norm_num] at hsq
    exact hsq.const_mul (by norm_num : (0 : ℝ) ≤ 2)
  have hZcellTail : ∀ R, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 4)) (Zcell R) (2 * B ^ 2) := by
    intro R
    have hmax0 := Tail.isBigOWith_max_zero hBpos (hZtail R)
    have hsq := (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := fun omega => max 0 (Zw R omega)) (K := B) (σ := (1 / 2 : ℝ))
      hBpos.le (fun omega => le_max_left _ _)).1 hmax0
    rw [show ((1 / 2 : ℝ)) / 2 = 1 / 4 by norm_num] at hsq
    exact hsq.const_mul (by norm_num : (0 : ℝ) ≤ 2)
  -- the deterministic cover, split over the two lanes
  have hcellAE := @twoLaneTransport_cell_ae_bound (d) (M) (L) (this) (Yw) (Zw) (hdom) (hYcell)
    (hZcell)
  have hRepAE : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (Observable.cutoffHomogenizationErrorRepresentative M L n
        (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega) ^ 2 ≤
        laneTotal L n Ycell omega + laneTotal L n Zcell omega := by
    have htarget := Observable.cutoffHomogenizationErrorRaw_ae_eq_representative
      M L n (by norm_num : (0 : ℝ) < 1 / 8) (Annealed.sigmaBar M L)
    filter_upwards [hcellAE, htarget] with omega hcell htargetOmega
    have hraw := cutoffHomogenizationErrorRaw_sq_le_laneTotal_add
      M L n hLn Ycell Zcell omega hcell
    simpa only [htargetOmega] using hraw
  -- the two lanes of the cover functional
  have hU := laneTotal_isBigOWith M L n hLn (σ := 1) (K := 2 * A ^ 2)
    (by norm_num) (by positivity) hYcell0 hYcellMeas hYcellTail
  have hV := laneTotal_isBigOWith M L n hLn (σ := (1 / 4 : ℝ)) (K := 2 * B ^ 2)
    (by norm_num) (by positivity) hZcell0 hZcellMeas hZcellTail
  have hUnonneg : ∀ omega, 0 ≤ laneTotal L n Ycell omega :=
    fun omega => laneTotal_nonneg L n hYcell0 omega
  have hVnonneg : ∀ omega, 0 ≤ laneTotal L n Zcell omega :=
    fun omega => laneTotal_nonneg L n hZcell0 omega
  have hCU : 0 ≤ laneCoverConst d 1 * (2 * A ^ 2) :=
    mul_nonneg (zero_le_one.trans (one_le_laneCoverConst d 1)) (by positivity)
  have hCV : 0 ≤ laneCoverConst d (1 / 4) * (2 * B ^ 2) :=
    mul_nonneg (zero_le_one.trans (one_le_laneCoverConst d (1 / 4)))
      (by positivity)
  have hsqrtU : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega => Real.sqrt (laneTotal L n Ycell omega))
      (Real.sqrt (laneCoverConst d 1 * (2 * A ^ 2))) := by
    refine (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := fun omega => Real.sqrt (laneTotal L n Ycell omega))
      (K := Real.sqrt (laneCoverConst d 1 * (2 * A ^ 2))) (σ := 2)
      (Real.sqrt_nonneg _) (fun omega => Real.sqrt_nonneg _)).2 ?_
    have hfun : (fun omega =>
        (Real.sqrt (laneTotal L n Ycell omega)) ^ 2) =
        laneTotal L n Ycell :=
      funext fun omega => Real.sq_sqrt (hUnonneg omega)
    rw [show (2 : ℝ) / 2 = 1 by norm_num, hfun, Real.sq_sqrt hCU]
    exact hU
  have hsqrtV : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma (1 / 2))
      (fun omega => Real.sqrt (laneTotal L n Zcell omega))
      (Real.sqrt (laneCoverConst d (1 / 4) * (2 * B ^ 2))) := by
    refine (Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (X := fun omega => Real.sqrt (laneTotal L n Zcell omega))
      (K := Real.sqrt (laneCoverConst d (1 / 4) * (2 * B ^ 2)))
      (σ := (1 / 2 : ℝ))
      (Real.sqrt_nonneg _) (fun omega => Real.sqrt_nonneg _)).2 ?_
    have hfun : (fun omega =>
        (Real.sqrt (laneTotal L n Zcell omega)) ^ 2) =
        laneTotal L n Zcell :=
      funext fun omega => Real.sq_sqrt (hVnonneg omega)
    rw [show ((1 / 2 : ℝ)) / 2 = 1 / 4 by norm_num, hfun, Real.sq_sqrt hCV]
    exact hV
  -- the two amplitudes, up to the dimension-only constant
  have hampU : Real.sqrt (laneCoverConst d 1 * (2 * A ^ 2)) ≤ Ctwo * A := by
    have hrewrite : Real.sqrt (laneCoverConst d 1 * (2 * A ^ 2)) =
        Real.sqrt (2 * laneCoverConst d 1) * A := by
      rw [show laneCoverConst d 1 * (2 * A ^ 2)
          = (2 * laneCoverConst d 1) * A ^ 2 by ring,
        Real.sqrt_mul (by
          have := one_le_laneCoverConst d 1
          positivity) (A ^ 2), Real.sqrt_sq hApos.le]
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hApos.le
  have hampV : Real.sqrt (laneCoverConst d (1 / 4) * (2 * B ^ 2)) ≤
      Ctwo * B := by
    have hrewrite : Real.sqrt (laneCoverConst d (1 / 4) * (2 * B ^ 2)) =
        Real.sqrt (2 * laneCoverConst d (1 / 4)) * B := by
      rw [show laneCoverConst d (1 / 4) * (2 * B ^ 2)
          = (2 * laneCoverConst d (1 / 4)) * B ^ 2 by ring,
        Real.sqrt_mul (by
          have := one_le_laneCoverConst d (1 / 4)
          positivity) (B ^ 2), Real.sqrt_sq hBpos.le]
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hBpos.le
  -- the square root of the cover, lane by lane
  have hdomAE : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Observable.cutoffHomogenizationErrorRepresentative M L n
          (1 / 8 : ℝ) (Annealed.sigmaBar M L) omega ≤
        Real.sqrt (laneTotal L n Ycell omega) +
          Real.sqrt (laneTotal L n Zcell omega)  := @twoLaneTransport_pointwiseDomination (d) (M)
            (m) (L) (n) (Yw) (Zw) (hRepAE) (hUnonneg) (hVnonneg)
  exact Tail.isTwoTermBigOWith_of_ae_le
    (Probability.isAdmissibleTail_gammaSigma (by norm_num : (0 : ℝ) < 2))
    (Probability.isAdmissibleTail_gammaSigma (by norm_num : (0 : ℝ) < 1 / 2))
    (mul_pos hCtwoPos hApos) (mul_pos hCtwoPos hBpos)
    (Observable.measurable_cutoffHomogenizationErrorRepresentative M L n
      (1 / 8 : ℝ) (Annealed.sigmaBar M L))
    ((laneTotal_measurable L n hLn hYcellMeas).sqrt)
    ((laneTotal_measurable L n hLn hZcellMeas).sqrt)
    hdomAE (hsqrtU.mono_scale hampU) (hsqrtV.mono_scale hampV)

end

end Algsuperdiff.Section3.Provider.Homogenization
