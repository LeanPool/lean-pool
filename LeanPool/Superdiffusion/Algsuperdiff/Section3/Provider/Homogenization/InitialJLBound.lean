/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.InitialJLBoundIntegrability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineExpectation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-!
# InitialJLBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `(e.initial.JL.bound)`, Part C: the assembly of Step 1 of the corrected combine

ABK26 (the display `e.initial.JL.bound`) and its proof.

## Content part carried by this file

This module is the **second of the two files** into which the Step-1 assembly
of the corrected combine is split.  It carries Part C: the discharge of the
five `Integrable` clauses of the proved variance split, the corridor summation,
the anchor wiring and the absorption that turn the proved pre-variance-split
display into the printed `e.initial.JL.bound`.  This is items (5)(6)(7) of the
depgraph record for node `p.combine.corrected`, the finite good-event Besov step.

Parts A and B --- the unconditional descendant envelope of the
`sigma_*^{-1}kappa` channel, the pointwise envelopes of the two deterministic
good-event blocks, their global integrability, and the discharge of the two
`IntegrableOn` binders of the proved `CombineExpectation` endpoints --- are in
`Provider/Homogenization/InitialJLBoundIntegrability.lean`, which this file
imports.  Every declaration was moved verbatim.  This half is still above the
800-line preference: about a third of it is this docstring, and the display
assembly is a single theorem with a 255-line proof, so no further cut is
available that does not split one proof.  Both halves are well under the
1500-line cap.

## Part C: the assembly into `(e.initial.JL.bound)`

The five `Integrable` clauses of
`coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le`
(`VarianceSplit.lean`) are discharged from the Part-A envelopes: the two
`sigma_*^{-1}` clauses are bounded by a *deterministic* constant (the
lower-right envelope carries no `E`), and the two `sigma_*^{-1}kappa` clauses
and the left-hand descendant average are dominated by quadratic polynomials in
`E`.

The two set integrals of the proved endpoint
`exists_integral_cutoffResponseJ_le_reabsorbedExpectationDisplay`
(`CombineExpectation.lean`) are then bounded by the global integrals
(`setIntegral_le_integral`, both blocks being pointwise nonnegative, by the
Part-A nonnegativity statements), the second block is summed over the printed
corridor, and the third block is bounded by the proved third-block split with
its deterministic residual bounded by `4 delta_1^2` through the anchor
`coefficientCutoffLaw_sq_sigmaBar_mul_annealedSigmaStarInvScalarAtScale_sub_one_le`
(`SigmaBarAnchor.lean`).

## Shape match against, with every deviation

The printed display is

`E[J(cu_m)] <= C sum_{n=L}^m 3^{-(m-n)} E[J(cu_n) - J(cu_m)]` `  + C
sigmabar_L^2 sum_{n=L}^m 3^{-(m-n)} (var[sigma_{L,*}^{-1}(cu_n)] + |mean
gap|^2)` `  + C sum_{n=L}^m 3^{-(m-n)} var[sigma_{L,*}^{-1}(cu_n)
kappa_L(cu_n)]` `  +[J(cu_{m-1}) 1_B]`.

The deviations are:

1. The factor `2` on `C_bad` is the printed reabsorption of `1/2 E[J(cu_m)]`,
   already performed by the proved endpoint.
2. The constant here is `24 C_base <= C`.
3. **Two amplitudes appear where the manuscript has one.**  `delta_1` is the
   amplitude of the printed premise `e.moment.bound.onmathcalE`, carried as a
   binder with `delta_1 in (0, 1/2]`; `10^9 E^2 gamma` is the *lane's* Step-4
   amplitude hard-coded by the proved bad-event endpoint.  Both amplitudes
   appear here only because the amplitude bridge --- which produces the
   fourth-moment premise at `s = 1/4` from the preceding-error clause --- is
   not yet proved; that bridge is the recurrence unit's item, not this file's,
   and adding `10^9 E^2 gamma <= delta_1` as a binder here would be a smuggled
   hypothesis.  The deviation is inherited from the proved Step-4 endpoint, not
   introduced here.

4. **`var[cu_m]` absorbed.**  The printed derivation produces `var[cu_m] +
   |gap|^2 + var[cu_n]`; the printed display carries only the `cu_n` variance.
   The absorption performed here is the printed one: `var[cu_m]` is the `n = m`
   term of the corridor sum (the mean gap vanishes there), and the corridor
   weight sums to at most `3/2`.
5. **Constants, and the gate's `s`.**  `C` is existential with `1 <= C`; the
   delivered `C` is `36 C_base` with `C_base` the constant of the proved
   endpoint.  The delivered statement **decouples the two**: the gate binder
   `hgateC` is hard-coded at the `s = 1/4` endpoint, i.e. at the exponent
   `3/4`, while the moment premise runs on a free `sMoment` with only `hsMoment
   : 0 < sMoment`.  For `s < 1/4` the delivered gate is therefore a *stronger*
   hypothesis than the printed one, and the printed weaker form is derived
   inside the proof; the sole consumer uses `s = 1/4`.  It makes the delivered
   statement stronger, not weaker.
6. **Regime data.**  The `Chom`, `E`, `epsilon` regime binders and the printed
   window are inherited verbatim from the proved endpoint; they are the
   corrected Step-4 regime data of `A.3`, not new premises.

## Declaration census

Eleven of the module's eighteen exported statements live here; the other seven
live in `InitialJLBoundIntegrability.lean`.  Ten `private` helpers live here.

## References

* ABK26, Section 3.5, proof of `p.combine.under.S`, Step 1.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Besov
open Algsuperdiff.Section3.Provider.Homogenization.Internal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **The pushforward integrability transfer.**  A measurable observable on
`RegCoeffField d` whose pullback along `Cutoff.coefficientCutoff M.nu L` is
dominated by an integrable sample observable is integrable at the coefficient
cutoff law.  This is the proved pattern of
`Cutoff.integrable_LambdaSqCoeffField_pow_cutoffLaw`
(`Cutoff.coefficientCutoffLaw_eq_map` + `integrable_map_measure` +
`Integrable.mono'`), factored out. -/
private theorem integrable_coefficientCutoffLaw_of_norm_le (M : ABKModel d) (L : ℤ)
    {f : RegCoeffField d → ℝ}
    (hf : AEMeasurable f (Cutoff.coefficientCutoffLaw M L))
    {g : Cutoff.CutoffSample d → ℝ}
    (hg : Integrable g (Cutoff.cutoffSampleLaw M).toMeasure)
    (hbound : ∀ omega : Cutoff.CutoffSample d,
      ‖f (Cutoff.coefficientCutoff M.nu L omega)‖ ≤ g omega) :
    Integrable f (Cutoff.coefficientCutoffLaw M L) := by
  have hmap : AEMeasurable f
      (Measure.map (Cutoff.coefficientCutoff M.nu L) (Cutoff.cutoffSampleLaw M).toMeasure) := by
    simpa only [Cutoff.coefficientCutoffLaw_eq_map] using hf
  have hcomp : AEMeasurable (fun omega => f (Cutoff.coefficientCutoff M.nu L omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [Function.comp_def] using
      hmap.comp_measurable (Cutoff.measurable_coefficientCutoff M.nu L)
  have hint : Integrable (fun omega => f (Cutoff.coefficientCutoff M.nu L omega))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    Integrable.mono' hg hcomp.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [Cutoff.coefficientCutoffLaw_eq_map M L]
  refine (integrable_map_measure hmap.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable).mpr ?_
  simpa only [Function.comp_def] using hint

/-- **The `hQlr`/`hRlr` clauses of
`coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le`,
discharged unconditionally.**  The `sigma_*^{-1}` fluctuation is bounded by a
deterministic constant at every cube, because the lower-right envelope is `4 d
nu⁻¹` with no event. -/
theorem integrable_starInverseCenteredFluctuationSq (M : ABKModel d) (L n : ℤ)
    (R : TriadicCube d) :
    Integrable (starInverseCenteredFluctuationSq M L n R)
      (Cutoff.coefficientCutoffLaw M L) := by
  refine integrable_coefficientCutoffLaw_of_norm_le M L
    (aestronglyMeasurable_starInverseCenteredFluctuationSq M L n R).aemeasurable
    (integrable_const ((4 * (d : ℝ) * M.nu⁻¹ +
      Ch02.matrixOperatorNorm
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerRight) ^ 2))
    (fun omega => ?_)
  have hlr := matrixOperatorNorm_coarseBlockMatrix_lowerRight_le_of_mem_descendantsAtScale
    M L omega R 0 (self_mem_descendantsAtScale R)
  have htri := matrixOperatorNorm_sub_le_add'
    (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerRight
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerRight
  rw [Real.norm_eq_abs, starInverseCenteredFluctuationSq,
    abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (Ch02.matrixOperatorNorm_nonneg _) (by linarith) 2

/-- **The `hQll`/`hRll` clauses of
`coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le`,
discharged unconditionally.**  The `sigma_*^{-1}kappa` fluctuation is bounded by
`(4 d nu⁻¹ E(R) + c)^2`, a quadratic polynomial in the integrable envelope. -/
theorem integrable_starInverseKappaCenteredFluctuationSq (M : ABKModel d) (L n : ℤ)
    (R : TriadicCube d) :
    Integrable (starInverseKappaCenteredFluctuationSq M L n R)
      (Cutoff.coefficientCutoffLaw M L) := by
  set c : ℝ := Ch02.matrixOperatorNorm
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerLeft with hc
  have hE1 : Integrable
      (fun omega => Cutoff.coefficientCutoffCubeEllipticityUpper M L omega R)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa using Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L R 1
  have hE2 := Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L R 2
  have hg : Integrable
      (fun omega => (4 * (d : ℝ) * M.nu⁻¹ *
        Cutoff.coefficientCutoffCubeEllipticityUpper M L omega R + c) ^ 2)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hexp : (fun omega => (4 * (d : ℝ) * M.nu⁻¹ *
          Cutoff.coefficientCutoffCubeEllipticityUpper M L omega R + c) ^ 2) =
        fun omega => (4 * (d : ℝ) * M.nu⁻¹) ^ 2 *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega R ^ 2 +
          (2 * (4 * (d : ℝ) * M.nu⁻¹) * c) *
            Cutoff.coefficientCutoffCubeEllipticityUpper M L omega R + c ^ 2 := by
      funext omega; ring
    rw [hexp]
    exact ((hE2.const_mul _).add (hE1.const_mul _)).add (integrable_const _)
  refine integrable_coefficientCutoffLaw_of_norm_le M L
    (aestronglyMeasurable_starInverseKappaCenteredFluctuationSq M L n R).aemeasurable hg
    (fun omega => ?_)
  have hll := matrixOperatorNorm_coarseBlockMatrix_lowerLeft_le_cutoffEnvelope
    M L omega R 0 (self_mem_descendantsAtScale R)
  have htri := matrixOperatorNorm_sub_le_add'
    (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu L omega).toFun).lowerLeft
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n).lowerLeft
  rw [Real.norm_eq_abs, starInverseKappaCenteredFluctuationSq,
    abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (Ch02.matrixOperatorNorm_nonneg _) (by rw [hc]; linarith) 2

/-- Integrability of one descendant summand of the coarse-matrix variation at
the coefficient cutoff law. -/
theorem integrable_coarseBlockMatrixVariationSq (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) (p q : Vec d) {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q j) :
    Integrable (fun a => coarseBlockMatrixVariationSq Q p q a R)
      (Cutoff.coefficientCutoffLaw M L) := by
  have hE2 := Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L Q 2
  refine integrable_coefficientCutoffLaw_of_norm_le M L
    (aemeasurable_coarseBlockMatrixVariationSq (Cutoff.coefficientCutoffLaw_lawCarrier M L)
      Q R p q)
    ((integrable_const (2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 * vecNormSq q)).add
      (hE2.const_mul (2 * (2 * (4 * (d : ℝ) * M.nu⁻¹)) ^ 2 * vecNormSq p)))
    (fun omega => ?_)
  rw [Real.norm_eq_abs, coarseBlockMatrixVariationSq, abs_of_nonneg (vecNormSq_nonneg _)]
  simpa only [Pi.add_apply] using!
    coarseBlockMatrixVariationSq_le_cutoffEnvelope M L omega Q p q hR

/-- **The `hLHS` clause of
`coefficientCutoffLaw_integral_descendantsAverage_coarseBlockMatrixVariationSq_le`,
discharged unconditionally.** -/
theorem integrable_descendantsAverage_coarseBlockMatrixVariationSq (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) (p q : Vec d) (j : ℕ) :
    Integrable (fun a => descendantsAverage Q j (coarseBlockMatrixVariationSq Q p q a))
      (Cutoff.coefficientCutoffLaw M L) :=
  Ch04.integrable_descendantsAverage
    (fun _R hR => integrable_coarseBlockMatrixVariationSq M L Q p q hR)

omit [NeZero d] in
/-- A.e. measurability of a finite sum, read pointwise. -/
private theorem aemeasurable_finsetSum_apply' {P : Measure (RegCoeffField d)} {iota : Type*}
    (s : Finset iota) (G : iota → RegCoeffField d → ℝ)
    (hG : ∀ i ∈ s, AEMeasurable (G i) P) :
    AEMeasurable (fun a => ∑ i ∈ s, G i a) P := by
  classical
  have h : AEMeasurable (∑ i ∈ s, G i) P := Finset.aemeasurable_sum _ hG
  convert h using 1
  ext a
  simp

omit [NeZero d] in
/-- A.e. measurability of the squared length of a measurable vector field. -/
private theorem aemeasurable_vecNormSq_comp {P : Measure (RegCoeffField d)}
    {v : RegCoeffField d → Vec d} (hv : AEMeasurable v P) :
    AEMeasurable (fun a => vecNormSq (v a)) P := by
  have hentry : ∀ a : RegCoeffField d, vecNormSq (v a) = ∑ i, v a i * v a i := fun _ => rfl
  simp only [hentry]
  exact aemeasurable_finsetSum_apply' _ (fun i a => v a i * v a i) fun i _hi =>
    (aemeasurable_pi_iff.mp hv i).mul (aemeasurable_pi_iff.mp hv i)

omit [NeZero d] in
/-- Integrability at the coefficient cutoff law pulls back to the sample law. -/
private theorem integrable_comp_coefficientCutoff (M : ABKModel d) (L : ℤ)
    {f : RegCoeffField d → ℝ} (hf : Integrable f (Cutoff.coefficientCutoffLaw M L)) :
    Integrable (fun omega => f (Cutoff.coefficientCutoff M.nu L omega))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [Cutoff.coefficientCutoffLaw_eq_map M L] at hf
  have hres := (integrable_map_measure hf.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable).mp hf
  simpa only [Function.comp_def] using hres

omit [NeZero d] in
/-- The change-of-variables identity for the coefficient cutoff pushforward. -/
private theorem integral_comp_coefficientCutoff (M : ABKModel d) (L : ℤ)
    {f : RegCoeffField d → ℝ} (hf : AEMeasurable f (Cutoff.coefficientCutoffLaw M L)) :
    ∫ omega, f (Cutoff.coefficientCutoff M.nu L omega)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ a, f a ∂(Cutoff.coefficientCutoffLaw M L) := by
  have hmap : AEMeasurable f
      (Measure.map (Cutoff.coefficientCutoff M.nu L) (Cutoff.cutoffSampleLaw M).toMeasure) := by
    simpa only [Cutoff.coefficientCutoffLaw_eq_map] using hf
  rw [Cutoff.coefficientCutoffLaw_eq_map M L]
  exact (integral_map (Cutoff.measurable_coefficientCutoff M.nu L).aemeasurable
    hmap.aestronglyMeasurable).symm

/-- Global integrability of the squared comparison vector at the coefficient
cutoff law. -/
theorem integrable_vecNormSq_coarseBlockScaleSeparation (M : ABKModel d) (L : ℤ)
    (Q : TriadicCube d) (p q : Vec d) :
    Integrable (fun a => vecNormSq (coarseBlockScaleSeparation Q p q a))
      (Cutoff.coefficientCutoffLaw M L) := by
  have hE2 := Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow M L Q 2
  refine integrable_coefficientCutoffLaw_of_norm_le M L
    (aemeasurable_vecNormSq_comp
      (aemeasurable_coarseBlockScaleSeparation (Cutoff.coefficientCutoffLaw_lawCarrier M L)
        Q p q))
    ((integrable_const (4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 * vecNormSq q + 2 * vecNormSq p)).add
      (hE2.const_mul (4 * (4 * (d : ℝ) * M.nu⁻¹) ^ 2 * vecNormSq p)))
    (fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
  simpa only [Pi.add_apply] using
    vecNormSq_coarseBlockScaleSeparation_le_cutoffEnvelope M L omega Q p q

/-- **The second block of `e.initial.JL.bound` at one corridor scale, with every
integrability clause discharged.**  This is
`coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le`
(`VarianceSplit.lean`) with its five `Integrable` binders supplied from the
unconditional envelopes above, and with the operator-norm mean gap rewritten as
the printed scalar gap `|sigmabar_{L,*}^{-1}(cu_m) - sigmabar_{L,*}^{-1}(cu_n)|^2`
through `coefficientCutoffLaw_annealedLowerRightGap_eq` (`VarianceSplit.lean`). -/
theorem coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le_of_vecNormSq_eq_one
    (M : ABKModel d) (L : ℤ) {n m : ℤ} (hnm : n ≤ m) {e : Vec d} (he : vecNormSq e = 1) :
    (Annealed.sigmaBar M L : ℝ) *
        ∫ a, descendantsAverage (originCube d m) (Int.toNat (m - n))
          (coarseBlockMatrixVariationSq (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a)
          ∂(Cutoff.coefficientCutoffLaw M L) ≤
      6 * (Annealed.sigmaBar M L : ℝ) ^ 2 *
          (starInverseVarianceAtScale M L m +
            (annealedSigmaStarInvScalarAtScale M L m -
              annealedSigmaStarInvScalarAtScale M L n) ^ 2 +
            starInverseVarianceAtScale M L n) +
        6 * (starInverseKappaVarianceAtScale M L m +
          starInverseKappaVarianceAtScale M L n) := by
  have h := coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le M L hnm he
    (integrable_descendantsAverage_coarseBlockMatrixVariationSq M L (originCube d m)
      (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
      (Observable.sqrtLoad (Annealed.sigmaBar M L) e) (Int.toNat (m - n)))
    (integrable_starInverseCenteredFluctuationSq M L m (originCube d m))
    (integrable_starInverseKappaCenteredFluctuationSq M L m (originCube d m))
    (fun R _ => integrable_starInverseCenteredFluctuationSq M L n R)
    (fun R _ => integrable_starInverseKappaCenteredFluctuationSq M L n R)
  rwa [coefficientCutoffLaw_annealedLowerRightGap_eq] at h

/-- **The third block of `e.initial.JL.bound` at the genuine cutoff sample law,
with its integrability discharged.**  The pointwise third-block split
`coefficientCutoffLaw_sigmaBar_mul_vecNormSq_coarseBlockScaleSeparation_le`
(`VarianceSplit.lean`) is integrated against the genuine cutoff law; the
deterministic residual `(sigmabar_L sigmabar_{L,*}^{-1}(cu_m) - 1)^2` is
displayed, not bounded, here.  It is bounded by `4 delta_1^2` in the final
assembly through the proved anchor
`coefficientCutoffLaw_sq_sigmaBar_mul_annealedSigmaStarInvScalarAtScale_sub_one_le`.
-/
theorem sigmaBar_mul_integral_coarseScaleSeparationBlock_le (M : ABKModel d) (m L : ℤ)
    {e : Vec d} (he : vecNormSq e = 1) :
    (Annealed.sigmaBar M L : ℝ) *
        ∫ omega, coarseScaleSeparationBlock M m L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      3 * ((Annealed.sigmaBar M L : ℝ) ^ 2 * starInverseVarianceAtScale M L m +
          ((Annealed.sigmaBar M L : ℝ) * annealedSigmaStarInvScalarAtScale M L m - 1) ^ 2 +
        starInverseKappaVarianceAtScale M L m) := by
  have hfun : (fun omega => coarseScaleSeparationBlock M m L e omega)
      = fun omega => vecNormSq (coarseBlockScaleSeparation (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
          (Cutoff.coefficientCutoff M.nu L omega)) := by
    funext omega
    rw [coarseScaleSeparationBlock, coarseScaleSeparation_eq_coarseBlockScaleSeparation]
  have hmeas := aemeasurable_vecNormSq_comp
    (aemeasurable_coarseBlockScaleSeparation (Cutoff.coefficientCutoffLaw_lawCarrier M L)
      (originCube d m) (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
      (Observable.sqrtLoad (Annealed.sigmaBar M L) e))
  rw [hfun, integral_comp_coefficientCutoff M L hmeas, ← integral_const_mul]
  have hlhs : Integrable (fun a => (Annealed.sigmaBar M L : ℝ) *
      vecNormSq (coarseBlockScaleSeparation (originCube d m)
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a))
      (Cutoff.coefficientCutoffLaw M L) :=
    (integrable_vecNormSq_coarseBlockScaleSeparation M L (originCube d m) _ _).const_mul _
  have hQlr := integrable_starInverseCenteredFluctuationSq M L m (originCube d m)
  have hQll := integrable_starInverseKappaCenteredFluctuationSq M L m (originCube d m)
  have hrhs : Integrable (fun a => 3 * ((Annealed.sigmaBar M L : ℝ) ^ 2 *
        starInverseCenteredFluctuationSq M L m (originCube d m) a +
        ((Annealed.sigmaBar M L : ℝ) * annealedSigmaStarInvScalarAtScale M L m - 1) ^ 2 +
        starInverseKappaCenteredFluctuationSq M L m (originCube d m) a))
      (Cutoff.coefficientCutoffLaw M L) :=
    (((hQlr.const_mul _).add (integrable_const _)).add hQll).const_mul _
  have hA : Integrable (fun a => (Annealed.sigmaBar M L : ℝ) ^ 2 *
      starInverseCenteredFluctuationSq M L m (originCube d m) a)
      (Cutoff.coefficientCutoffLaw M L) := hQlr.const_mul _
  have hAc : Integrable (fun a => (Annealed.sigmaBar M L : ℝ) ^ 2 *
        starInverseCenteredFluctuationSq M L m (originCube d m) a +
      ((Annealed.sigmaBar M L : ℝ) * annealedSigmaStarInvScalarAtScale M L m - 1) ^ 2)
      (Cutoff.coefficientCutoffLaw M L) := hA.add (integrable_const _)
  refine (integral_mono hlhs hrhs (fun a =>
    coefficientCutoffLaw_sigmaBar_mul_vecNormSq_coarseBlockScaleSeparation_le M L m he a)).trans
    (le_of_eq ?_)
  rw [integral_const_mul, integral_add hAc hQll, integral_add hA (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul]
  rfl

/-- **The second block of `e.initial.JL.bound` at the genuine cutoff sample
law**, summed over the printed corridor, with every integrability clause
discharged.  The corridor integral is transferred to the coefficient cutoff law
by the pushforward identity and bounded scale by scale. -/
theorem sigmaBar_mul_integral_coarseMatrixVariationBlock_le (M : ABKModel d) (m L : ℤ)
    {e : Vec d} (he : vecNormSq e = 1) :
    (Annealed.sigmaBar M L : ℝ) *
        ∫ omega, coarseMatrixVariationBlock M m L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        (6 * (Annealed.sigmaBar M L : ℝ) ^ 2 *
            (starInverseVarianceAtScale M L m +
              (annealedSigmaStarInvScalarAtScale M L m -
                annealedSigmaStarInvScalarAtScale M L n) ^ 2 +
              starInverseVarianceAtScale M L n) +
          6 * (starInverseKappaVarianceAtScale M L m +
            starInverseKappaVarianceAtScale M L n)) := by
  have hfun : (fun omega => coarseMatrixVariationBlock M m L e omega)
      = fun omega => ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          descendantsAverage (originCube d m) (Int.toNat (m - n))
            (coarseBlockMatrixVariationSq (originCube d m)
              (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
              (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
              (Cutoff.coefficientCutoff M.nu L omega)) := by
    funext omega
    refine Finset.sum_congr rfl fun n _hn => ?_
    exact congrArg (fun F => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        descendantsAverage (originCube d m) (Int.toNat (m - n)) F)
      (funext fun R => coarseMatrixVariationSq_eq_coarseBlockMatrixVariationSq
        (Cutoff.coefficientCutoff M.nu L omega)
        (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega)
        (originCube d m) _ _ R)
  have hterm : ∀ n ∈ Finset.Icc L m,
      Integrable (fun omega => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (coarseBlockMatrixVariationSq (originCube d m)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (Cutoff.coefficientCutoff M.nu L omega)))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro n _hn
    exact (integrable_comp_coefficientCutoff M L
      (integrable_descendantsAverage_coarseBlockMatrixVariationSq M L (originCube d m)
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M L) e) (Int.toNat (m - n)))).const_mul _
  rw [hfun, integral_finsetSum _ hterm, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _hn => ?_
  rw [integral_const_mul,
    integral_comp_coefficientCutoff M L
      (Ch04.integrable_descendantsAverage
        (fun _R hR => integrable_coarseBlockMatrixVariationSq M L (originCube d m)
          (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
          (Observable.sqrtLoad (Annealed.sigmaBar M L) e) hR)).aemeasurable]
  by_cases hnm : n ≤ m
  · have hbase :=
      coefficientCutoffLaw_sigmaBar_mul_integral_descendantsAverage_le_of_vecNormSq_eq_one
        M L hnm he
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    calc (Annealed.sigmaBar M L : ℝ) * ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ∫ a, descendantsAverage (originCube d m) (Int.toNat (m - n))
              (coarseBlockMatrixVariationSq (originCube d m)
                (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a)
              ∂(Cutoff.coefficientCutoffLaw M L))
        = (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) * ((Annealed.sigmaBar M L : ℝ) *
            ∫ a, descendantsAverage (originCube d m) (Int.toNat (m - n))
              (coarseBlockMatrixVariationSq (originCube d m)
                (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
                (Observable.sqrtLoad (Annealed.sigmaBar M L) e) a)
              ∂(Cutoff.coefficientCutoffLaw M L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase hw0
  · exact absurd (Finset.mem_Icc.mp _hn).2 hnm

/-- A truncated geometric series with ratio in `[0,1)` is below the full
series. -/
private theorem geom_sum_le_inv_one_sub' {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, r ^ j ≤ (1 - r)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hmul := geom_sum_mul r K
  have hpow : (0 : ℝ) ≤ r ^ K := pow_nonneg hr0 K
  have hval : (∑ j ∈ Finset.range K, r ^ j) * (1 - r) = 1 - r ^ K := by
    linear_combination -hmul
  rw [← one_div, le_div_iff₀ hpos, hval]
  linarith

/-- The nonnegative integer cast of a nonnegative integer difference. -/
private theorem toNat_sub_cast' {m n : ℤ} (h : n ≤ m) :
    (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
  have h0 : (0 : ℤ) ≤ m - n := by omega
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)

/-- A geometrically weighted power of `3` on the corridor is the corresponding
power of the one-step ratio. -/
private theorem rpow_three_mul_eq_pow' (c : ℝ) {m n : ℤ} (h : n ≤ m) :
    (3 : ℝ) ^ (c * ((m - n : ℤ) : ℝ)) = ((3 : ℝ) ^ c) ^ (m - n).toNat := by
  rw [← toNat_sub_cast' h, ← Real.rpow_natCast ((3 : ℝ) ^ c) ((m - n).toNat),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- A geometric weight on the finite corridor `[L,m]` sums below the value of the
full geometric series. -/
private theorem sum_Icc_le_of_geometric' {L m : ℤ} (hLm : L ≤ m) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (w : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Icc L m, w n = r ^ (m - n).toNat) :
    ∑ n ∈ Finset.Icc L m, w n ≤ (1 - r)⁻¹ := by
  have hreindex :
      ∑ j ∈ Finset.range ((m - L).toNat + 1), r ^ j = ∑ n ∈ Finset.Icc L m, w n := by
    refine Finset.sum_nbij' (fun j : ℕ => m - (j : ℤ)) (fun n : ℤ => (m - n).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Icc]
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      show (m - (m - (j : ℤ))).toNat = j
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      show m - (((m - n).toNat : ℕ) : ℤ) = n
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hmem : m - (j : ℤ) ∈ Finset.Icc L m := by
        simp only [Finset.mem_Icc]
        omega
      rw [hw _ hmem]
      congr 1
      omega
  rw [← hreindex]
  exact geom_sum_le_inv_one_sub' hr0 hr1 _

/-- The printed corridor weight `3^{-(m-n)}` sums to at most `3/2`. -/
private theorem sum_Icc_three_neg_le' {L m : ℤ} (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ 3 / 2 := by
  have hrv : (3 : ℝ) ^ (-1 : ℝ) = 3⁻¹ := by
    rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hbound :
      ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) ≤ (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹ := by
    refine sum_Icc_le_of_geometric' hLm (Real.rpow_nonneg (by norm_num) _) ?_ _ ?_
    · rw [hrv]; norm_num
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      rw [show -((m - n : ℤ) : ℝ) = (-1 : ℝ) * ((m - n : ℤ) : ℝ) by ring]
      exact rpow_three_mul_eq_pow' (-1 : ℝ) hn.2
  have hval : ((1 : ℝ) - (3 : ℝ) ^ (-1 : ℝ))⁻¹ = 3 / 2 := by
    rw [hrv]; norm_num
  rw [hval] at hbound
  exact hbound

omit [NeZero d] in
/-- The manuscript variance `var[sigma_{L,*}^{-1}(cu_n)]` is nonnegative. -/
theorem starInverseVarianceAtScale_nonneg (M : ABKModel d) (L n : ℤ) :
    0 ≤ starInverseVarianceAtScale M L n := by
  refine integral_nonneg fun a => ?_
  rw [starInverseCenteredFluctuationSq]
  positivity

omit [NeZero d] in
/-- The manuscript variance `var[sigma_{L,*}^{-1}(cu_n) kappa_L(cu_n)]` is
nonnegative. -/
theorem starInverseKappaVarianceAtScale_nonneg (M : ABKModel d) (L n : ℤ) :
    0 ≤ starInverseKappaVarianceAtScale M L n := by
  refine integral_nonneg fun a => ?_
  rw [starInverseKappaCenteredFluctuationSq]
  positivity

/-- **`(e.initial.JL.bound)` at the genuine cutoff sample law**.

The delivered display is

`E[J(cu_m)] <= C sum_{n=L}^m 3^{-(m-n)} (E[J(cu_n)] - E[J(cu_m)])`
`  + C sigmabar_L^2 sum_{n=L}^m 3^{-(m-n)}`
`      (var[sigma_{L,*}^{-1}(cu_n)] + |sigmabar_{L,*}^{-1}(cu_m) - sigmabar_{L,*}^{-1}(cu_n)|^2)`
`  + C sum_{n=L}^m 3^{-(m-n)} var[sigma_{L,*}^{-1}(cu_n) kappa_L(cu_n)]`
`  + C delta_1^2 + C_bad (10^9 E^2 gamma)^2`,

which is the printed display with its fourth block `C E[J(cu_{m-1}) 1_B]` already
replaced by the proved corrected Step-4 bad-event bound, and with the `+ C
delta_1^2` mandated.  Every deviation is listed in the module docstring.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_integral_cutoffResponseJ_le_initialJLBoundDisplay (d : ℕ) [NeZero d] :
    ∃ Chom C Cbad : ℝ, 64 ≤ Chom ∧ 1 ≤ C ∧ 1 ≤ Cbad ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (Cutoff.cutoffSampleLaw M).toMeasure
              (IndependentSums.gammaSigma 2) (IndependentSums.gammaSigma (1 / 2))
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
              ∀ sMoment : ℝ, ∀ hsMoment : 0 < sMoment, ∀ delta1 : ℝ,
                delta1 ∈ Set.Ioc (0 : ℝ) (1 / 2) →
                ∫⁻ omega, ENNReal.ofReal
                    (Observable.cutoffHomogenizationErrorRepresentative M L L hsMoment
                      (Annealed.sigmaBar M L) omega ^ 4)
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (delta1 ^ 2) →
                ∫ omega, Observable.cutoffResponseJ M m L e omega
                    ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
                  C * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                      ((∫ omega, Observable.cutoffResponseJ M n L e omega
                          ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
                        ∫ omega, Observable.cutoffResponseJ M m L e omega
                          ∂(Cutoff.cutoffSampleLaw M).toMeasure)) +
                    C * ((Annealed.sigmaBar M L : ℝ) ^ 2 *
                      ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                        (starInverseVarianceAtScale M L n +
                          (annealedSigmaStarInvScalarAtScale M L m -
                            annealedSigmaStarInvScalarAtScale M L n) ^ 2)) +
                    C * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                      starInverseKappaVarianceAtScale M L n) +
                    C * delta1 ^ 2 +
                    Cbad * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2 := by
  obtain ⟨Chom, Cbase, Cbad, hChom, hCbase, hCbad, hendpoint⟩ :=
    exists_integral_cutoffResponseJ_le_reabsorbedExpectationDisplay d
  refine ⟨Chom, 36 * Cbase, 2 * Cbad, hChom, by linarith only [hCbase],
    by linarith only [hCbad], ?_⟩
  intro M m E hEfloor hregime hLower epsilon hepsilon hgate L hsep hgateC e he
    sMoment hsMoment delta1 hdelta1 hmoment
  have hLm : L ≤ m := by omega
  have hLm1 : L ≤ m - 1 := by omega
  have hCbasePos : (0 : ℝ) < Cbase := by linarith only [hCbase]
  have hrpow : (0 : ℝ) < (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgateBase : Cbase * (3 : ℝ) ^ (-(3 / 4 : ℝ) * ((m - L : ℤ) : ℝ)) ≤ 1 / 4 := by
    nlinarith only [hgateC, hrpow, hCbasePos]
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hevs : vecNormSq e = 1 := by
    rw [← Ch02.vecNorm_sq_eq_vecNormSq, he]; norm_num
  have hstep : ∫ omega, Observable.cutoffResponseJ M m L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      2 * (Cbase * (∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            ((∫ omega, Observable.cutoffResponseJ M n L e omega
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
              ∫ omega, Observable.cutoffResponseJ M m L e omega
                ∂(Cutoff.cutoffSampleLaw M).toMeasure)) +
          Cbase * ((Annealed.sigmaBar M L : ℝ) *
            ∫ omega in (observationScaleBadEvent M L m)ᶜ,
              coarseMatrixVariationBlock M m L e omega
              ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
          Cbase * ((Annealed.sigmaBar M L : ℝ) *
            ∫ omega in (observationScaleBadEvent M L m)ᶜ,
              coarseScaleSeparationBlock M m L e omega
              ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
          Cbad * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) ^ 2) :=
    hendpoint M m E hEfloor hregime hLower epsilon hepsilon hgate L hsep
      hgateBase e he
      (integrableOn_coarseMatrixVariationBlock_compl_observationScaleBadEvent M m L e)
      (integrableOn_coarseScaleSeparationBlock_compl_observationScaleBadEvent M m L e)
  -- pass from the set integrals over the good event to the global integrals
  have hvarset : ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      coarseMatrixVariationBlock M m L e omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ∫ omega, coarseMatrixVariationBlock M m L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    setIntegral_le_integral (integrable_coarseMatrixVariationBlock M m L e)
      (Filter.Eventually.of_forall (coarseMatrixVariationBlock_nonneg M m L e))
  have hsepset : ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      coarseScaleSeparationBlock M m L e omega ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ∫ omega, coarseScaleSeparationBlock M m L e omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    setIntegral_le_integral (integrable_coarseScaleSeparationBlock M m L e)
      (Filter.Eventually.of_forall (coarseScaleSeparationBlock_nonneg M m L e))
  -- the two corridor sums of the printed display
  set S : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    (starInverseVarianceAtScale M L n +
      (annealedSigmaStarInvScalarAtScale M L m -
        annealedSigmaStarInvScalarAtScale M L n) ^ 2) with hS
  set K : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    starInverseKappaVarianceAtScale M L n with hK
  have hAnn : ∀ n : ℤ, (0 : ℝ) ≤ (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) := fun n =>
    Real.rpow_nonneg (by norm_num) _
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (hAnn n)
      (add_nonneg (starInverseVarianceAtScale_nonneg M L n) (sq_nonneg _))
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (hAnn n)
      (starInverseKappaVarianceAtScale_nonneg M L n)
  have hmem : m ∈ Finset.Icc L m := Finset.mem_Icc.mpr ⟨hLm, le_rfl⟩
  have hvarm : starInverseVarianceAtScale M L m ≤ S := by
    rw [hS]
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun n => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        (starInverseVarianceAtScale M L n +
          (annealedSigmaStarInvScalarAtScale M L m -
            annealedSigmaStarInvScalarAtScale M L n) ^ 2))
        (fun n _ => mul_nonneg (hAnn n)
          (add_nonneg (starInverseVarianceAtScale_nonneg M L n) (sq_nonneg _))) hmem)
    simp
  have hkvarm : starInverseKappaVarianceAtScale M L m ≤ K := by
    rw [hK]
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (f := fun n => (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        starInverseKappaVarianceAtScale M L n)
        (fun n _ => mul_nonneg (hAnn n) (starInverseKappaVarianceAtScale_nonneg M L n)) hmem)
    simp
  -- second block
  have hW := sum_Icc_three_neg_le' (L := L) (m := m) hLm
  have hvarblock :
      (Annealed.sigmaBar M L : ℝ) *
        ∫ omega, coarseMatrixVariationBlock M m L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        15 * (Annealed.sigmaBar M L : ℝ) ^ 2 * S + 15 * K := by
    refine (sigmaBar_mul_integral_coarseMatrixVariationBlock_le M m L hevs).trans ?_
    have htermwise : ∀ n ∈ Finset.Icc L m,
        (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            (6 * (Annealed.sigmaBar M L : ℝ) ^ 2 *
                (starInverseVarianceAtScale M L m +
                  (annealedSigmaStarInvScalarAtScale M L m -
                    annealedSigmaStarInvScalarAtScale M L n) ^ 2 +
                  starInverseVarianceAtScale M L n) +
              6 * (starInverseKappaVarianceAtScale M L m +
                starInverseKappaVarianceAtScale M L n)) ≤
          (6 * (Annealed.sigmaBar M L : ℝ) ^ 2 * S) * (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) +
            (6 * (Annealed.sigmaBar M L : ℝ) ^ 2) *
              ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                (starInverseVarianceAtScale M L n +
                  (annealedSigmaStarInvScalarAtScale M L m -
                    annealedSigmaStarInvScalarAtScale M L n) ^ 2)) +
            (6 * K) * (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) +
            6 * ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
              starInverseKappaVarianceAtScale M L n) := by
      intro n _hn
      have hA := hAnn n
      nlinarith only [hA, mul_nonneg (mul_nonneg hA (sq_nonneg (Annealed.sigmaBar M L : ℝ)))
          (sub_nonneg.mpr hvarm),
        mul_nonneg hA (sub_nonneg.mpr hkvarm)]
    refine (Finset.sum_le_sum htermwise).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hS, ← hK]
    nlinarith only [hW, hSnn, hKnn, sq_nonneg (Annealed.sigmaBar M L : ℝ),
      mul_nonneg (sq_nonneg (Annealed.sigmaBar M L : ℝ)) hSnn]
  -- third block, with the anchor residual
  have hpq : Observable.sqrtLoad (Annealed.sigmaBar M L) e =
      (Annealed.sigmaBar M L : ℝ) •
        Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e := by
    rw [Observable.sqrtLoad, Observable.inverseSqrtLoad, smul_smul]
    congr 1
    field_simp
    exact Real.sq_sqrt hsigpos.le
  have hqnorm : vecNormSq (Observable.sqrtLoad (Annealed.sigmaBar M L) e) =
      (Annealed.sigmaBar M L : ℝ) := by
    rw [Observable.sqrtLoad, vecNormSq_smul, Real.sq_sqrt hsigpos.le, hevs, mul_one]
  have hres :=
    coefficientCutoffLaw_sq_sigmaBar_mul_annealedSigmaStarInvScalarAtScale_sub_one_le
      M hLm hsMoment hdelta1 hmoment hpq hqnorm
  have hsepblock :
      (Annealed.sigmaBar M L : ℝ) *
        ∫ omega, coarseScaleSeparationBlock M m L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        3 * (Annealed.sigmaBar M L : ℝ) ^ 2 * S + 12 * delta1 ^ 2 + 3 * K := by
    refine (sigmaBar_mul_integral_coarseScaleSeparationBlock_le M m L hevs).trans ?_
    nlinarith only [hres, hvarm, hkvarm, sq_nonneg (Annealed.sigmaBar M L : ℝ),
      mul_nonneg (sq_nonneg (Annealed.sigmaBar M L : ℝ)) (sub_nonneg.mpr hvarm)]
  -- the defect sum is nonnegative
  have hEpos : (0 : ℝ) < (E : ℝ) := zero_lt_one.trans_le E.property
  have hEinvSq : ((E : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have hEinvOne : (E : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hEpos).2 E.property
    have hEinvNonneg : 0 ≤ (E : ℝ)⁻¹ := inv_nonneg.mpr hEpos.le
    nlinarith only [hEinvOne, hEinvNonneg]
  have hChomPos : (0 : ℝ) < Chom := by linarith only [hChom]
  have hChomInv : Chom⁻¹ ≤ 1 / 64 := by
    have hid : Chom⁻¹ * Chom = 1 := inv_mul_cancel₀ hChomPos.ne'
    nlinarith only [hid, hChom, mul_nonneg (inv_pos.mpr hChomPos).le
      (by linarith only [hChom] : (0 : ℝ) ≤ Chom - 64)]
  have hgamma128 : M.gamma ≤ 1 / 128 := by
    have hpair : Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 ≤ 1 / 64 * 1 :=
      mul_le_mul hChomInv hEinvSq (sq_nonneg _) (by norm_num)
    have hfull : Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon ≤ 1 / 64 * 1 * (1 / 2) :=
      mul_le_mul hpair hepsilon.2 hepsilon.1.le (by norm_num)
    have hval : (1 / 64 * 1 : ℝ) * (1 / 2) = 1 / 128 := by norm_num
    linarith only [hfull, hval, hgate]
  have hwindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 :=
    ⟨by linarith only [hgamma128], by norm_num⟩
  have hJ : ∀ n : ℤ, L ≤ n → n ≤ m →
      Integrable (Observable.cutoffResponseJ M n L e)
        (Cutoff.cutoffSampleLaw M).toMeasure := fun n hn1 hn2 =>
    integrable_cutoffResponseJ_of_precedingError M m L hLm1 E hLower hwindow he n hn1 hn2
  have hdefect : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      ((∫ omega, Observable.cutoffResponseJ M n L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
        ∫ omega, Observable.cutoffResponseJ M m L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    rw [← integral_responseDefectBlock_eq M m L hLm hJ]
    exact integral_nonneg fun omega => responseDefectBlock_nonneg M m L e omega
  set D : ℝ := ∑ n ∈ Finset.Icc L m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
      ((∫ omega, Observable.cutoffResponseJ M n L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) -
        ∫ omega, Observable.cutoffResponseJ M m L e omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) with hDdef
  set X : ℝ := ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      coarseMatrixVariationBlock M m L e omega ∂(Cutoff.cutoffSampleLaw M).toMeasure with hXdef
  set Y : ℝ := ∫ omega in (observationScaleBadEvent M L m)ᶜ,
      coarseScaleSeparationBlock M m L e omega ∂(Cutoff.cutoffSampleLaw M).toMeasure with hYdef
  set JM : ℝ := ∫ omega, Observable.cutoffResponseJ M m L e omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure with hJMdef
  have hvar' : Cbase * ((Annealed.sigmaBar M L : ℝ) * X) ≤
      Cbase * (15 * (Annealed.sigmaBar M L : ℝ) ^ 2 * S + 15 * K) :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hvarset hsigpos.le).trans hvarblock) hCbasePos.le
  have hsep' : Cbase * ((Annealed.sigmaBar M L : ℝ) * Y) ≤
      Cbase * (3 * (Annealed.sigmaBar M L : ℝ) ^ 2 * S + 12 * delta1 ^ 2 + 3 * K) :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hsepset hsigpos.le).trans hsepblock) hCbasePos.le
  have hCbD : (0 : ℝ) ≤ Cbase * D := mul_nonneg hCbasePos.le hdefect
  have hCbd1 : (0 : ℝ) ≤ Cbase * delta1 ^ 2 := mul_nonneg hCbasePos.le (sq_nonneg _)
  linarith only [hstep, hvar', hsep', hCbD, hCbd1]

end

end Algsuperdiff.Section3.Provider.Homogenization
