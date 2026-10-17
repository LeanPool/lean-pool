/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridWeights
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle

/-!
# ScaleSummation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The scale summation of `p.cg.ellipticity.bounds`, in the payload's shape

ABK26's proof of `p.cg.ellipticity.bounds` from `p.bfA.multiscalebound` has
exactly two moves after the block estimate:

2. "**which implies, after summing over `n`**" --- the passage from the
   per-scale display `max_z |b_m(z+cu_n)| shom^{-1} <= C + O_{Gamma_1}(A_1(n))
   + O_{Gamma_sigma'}(A_2(n))` to the display for `Lambda_{s,q}(cu_m; a_m)
   shom^{-1}` itself.

This module supplies the weighted countable step of move 2, the ingredient
behind the *three-slot shape* that
`Provider/CoarseEllipticity/UpperLeg.lean`'s payload binder consumes: a
pointwise domination `X <= Udet + U1 + Uexp` with `Udet` bounded by a constant,
`U1` and `Uexp` measurable, and each of the two carrying its own `Gamma` tail.

## What "summing over `n`" is, formally

The source's summation is: an on-grid bound of the target by a weighted series
of the per-scale grid maxima,
`X <= sum_k w_k G_k`, together with a per-scale three-way split
`G_k <= Cdet + U1_k + Uexp_k`.  Since the weights are nonnegative with total
mass at most `Wtot`, the deterministic part contributes `Cdet * Wtot` and the
two random parts contribute the *weighted countable sums*
`sum_k w_k U1_k` and `sum_k w_k Uexp_k`, each priced by the countable
`Gamma_sigma` triangle inequality `l.Gamma.sigma.triangle`
(`Provider/Orlicz/TsumTriangle.lean`) at
`gammaTriangleConst sigma * sum_k w_k a_k`.

That is the whole content of the source's one-line "after summing over `n`"; its
weighted countable step is `isBigOWith_gammaSigma_tsum_weighted`.  The
*arithmetic* of the resulting amplitudes --- turning `sum_k w_k a_k` into the
printed `C s gamma (2s - gamma)^{-3}` --- is the caller's, and is supplied by
`GridWeights.lean`'s `polyGridWeight_tsum_le`, `gridWeight_mul_rpow` and
`one_sub_rpow_neg_inv_le`.

## Main results

* `isBigOWith_gammaSigma_tsum_weighted` --- the weighted countable
  `Gamma_sigma` triangle inequality.

## What this module does NOT claim

At this repository's carrier that is the statement that
`Observable.cutoffUpperEllipticity` is dominated by a weighted series of grid
maxima of `|b|` --- the *off-grid/on-grid `LambdaSq` bridge*.  CoarseGraining
supplies the deterministic half of that bridge at `q = 1`
(`Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale`,
`Ch04.LambdaSqCoeffField_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale`);
the passage from there to the measurable representative
`Observable.cutoffUpperEllipticity` is only almost everywhere, and no theorem
here or anywhere in this repository closes that gap.

## References

* ABK26, `p.cg.ellipticity.bounds`, proof from `p.bfA.multiscalebound`, (the
  two "after summing over `n`" steps).
* ABK26, `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The weighted form of `l.Gamma.sigma.triangle`: a nonnegative family with
individual `Gamma_sigma` scales, summed against nonnegative weights, is
`Gamma_sigma` at `gammaTriangleConst sigma` times the weighted scale series. -/
theorem isBigOWith_gammaSigma_tsum_weighted [IsFiniteMeasure mu]
    {U : ℕ → Omega → ℝ} {w a : ℕ → ℝ} {sigma B : ℝ}
    (hsigma : 0 < sigma) (hw : ∀ k, 0 < w k)
    (hUnonneg : ∀ k omega, 0 ≤ U k omega)
    (hUmeas : ∀ k, Measurable (U k))
    (ha : ∀ k, 0 < a k) (hasum : Summable fun k => w k * a k)
    (hU : ∀ k, IsBigOWith mu (gammaSigma sigma) (U k) (a k))
    (hB : gammaTriangleConst sigma * ∑' k, w k * a k ≤ B) :
    IsBigOWith mu (gammaSigma sigma) (fun omega => ∑' k, w k * U k omega) B := by
  refine (Provider.Orlicz.isBigOWith_gammaSigma_tsum (μ := mu)
    (X := fun k omega => w k * U k omega) (a := fun k => w k * a k) hsigma
    (fun k omega => mul_nonneg (hw k).le (hUnonneg k omega))
    (fun k => (hUmeas k).const_mul (w k))
    (fun k => mul_pos (hw k) (ha k)) hasum
    (fun k => (hU k).const_mul (hw k).le)).mono_scale hB

/-! ## 3. The scale summation, in the payload's three-slot shape -/


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
