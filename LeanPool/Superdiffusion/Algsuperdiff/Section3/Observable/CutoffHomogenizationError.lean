/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Definition
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationErrorRepresentative

/-!
# CutoffHomogenizationError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The cutoff homogenization error

This file exposes the measurable Section 3 observable
`\mathcal E_{s,\infty,2}(\square_m; a_m, \bar\sigma_r\operatorname{Id})` on its
source domain `0 < s`.  The auxiliary comparator scale `r` remains explicit;
the paper's state variable is the specialization `r = m`.

The public definitions use the genuine coefficient cutoff, genuine running
diffusivity, and the verified measurable representative.  Their
almost-everywhere characterizations retain the separate coefficient, domain,
and comparator scale roles and identify the observable with CoarseGraining's
literal homogenization error.

## Main definitions

* `cutoffHomogenizationErrorAtComparatorScale`: coefficient and cube scale `m`,
  with running-diffusivity comparator taken at a separately specified scale.
* `cutoffHomogenizationError`: the manuscript specialization whose three scales
  are all `m`.

## References

* ABK26, definition `d.mathcal.E`, (2.28).
* ABK26, definition `d.mathcalS.def`, Section 3.1.
-/

namespace Algsuperdiff.Section3.Observable

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book

noncomputable section

/-- The paper-wide assumption `2 ≤ d`, stored in the model, supplies the
nonzero-dimension instance required by CoarseGraining's doubled-response A. -/
theorem neZero_of_model_CutoffHomogenizationError {d : ℕ} (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The measurable cutoff homogenization error with coefficient and cube scale
`m` and running-diffusivity comparator taken at `comparatorScale`:
`\mathcal E_{s,\infty,2}(\square_m; a_m,
  \bar\sigma_{\mathit{comparatorScale}}\operatorname{Id})`. -/
noncomputable def cutoffHomogenizationErrorAtComparatorScale {d : ℕ}
    (M : ABKModel d) (m comparatorScale : ℤ) (s : {s : ℝ // 0 < s}) :
    Cutoff.CutoffSample d → ℝ := by
  letI : NeZero d := neZero_of_model_CutoffHomogenizationError M
  exact cutoffHomogenizationErrorRepresentative M m m (s : ℝ)
    (Annealed.sigmaBar M comparatorScale)

/-- The actual Section 3 homogenization error
`\mathcal E_{s,\infty,2}(\square_m; a_m, \bar\sigma_m\operatorname{Id})`. -/
noncomputable def cutoffHomogenizationError {d : ℕ} (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) : Cutoff.CutoffSample d → ℝ :=
  cutoffHomogenizationErrorAtComparatorScale M m m s

/-- The cutoff homogenization error with a separate comparator scale is
measurable under the genuine cutoff-sample law. -/
theorem measurable_cutoffHomogenizationErrorAtComparatorScale {d : ℕ}
    (M : ABKModel d) (m comparatorScale : ℤ) (s : {s : ℝ // 0 < s}) :
    Measurable (cutoffHomogenizationErrorAtComparatorScale M m comparatorScale s) := by
  let : NeZero d := neZero_of_model_CutoffHomogenizationError M
  change Measurable (cutoffHomogenizationErrorRepresentative M m m (s : ℝ)
    (Annealed.sigmaBar M comparatorScale))
  exact measurable_cutoffHomogenizationErrorRepresentative M m m (s : ℝ)
    (Annealed.sigmaBar M comparatorScale)

/-- The actual Section 3 cutoff homogenization error is measurable. -/
theorem measurable_cutoffHomogenizationError {d : ℕ} (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) :
    Measurable (cutoffHomogenizationError M m s) :=
  measurable_cutoffHomogenizationErrorAtComparatorScale M m m s

/-- The cutoff homogenization error with a separate comparator scale is
pointwise nonnegative. -/
theorem cutoffHomogenizationErrorAtComparatorScale_nonneg {d : ℕ}
    (M : ABKModel d) (m comparatorScale : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationErrorAtComparatorScale M m comparatorScale s omega := by
  let : NeZero d := neZero_of_model_CutoffHomogenizationError M
  change 0 ≤ cutoffHomogenizationErrorRepresentative M m m (s : ℝ)
    (Annealed.sigmaBar M comparatorScale) omega
  exact cutoffHomogenizationErrorRepresentative_nonneg M m m (s : ℝ)
    (Annealed.sigmaBar M comparatorScale) omega

/-- The actual Section 3 cutoff homogenization error is pointwise
nonnegative. -/
theorem cutoffHomogenizationError_nonneg {d : ℕ} (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) :
    0 ≤ cutoffHomogenizationError M m s omega :=
  cutoffHomogenizationErrorAtComparatorScale_nonneg M m m s omega

/-- The public observable with a separate comparator scale is almost everywhere the
verified raw manuscript expression. -/
theorem cutoffHomogenizationErrorAtComparatorScale_ae_eq_raw {d : ℕ}
    (M : ABKModel d) (m comparatorScale : ℤ) (s : {s : ℝ // 0 < s}) :
    cutoffHomogenizationErrorAtComparatorScale M m comparatorScale s =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      @cutoffHomogenizationErrorRaw d M m m (s : ℝ)
        (Annealed.sigmaBar M comparatorScale) := by
  let : NeZero d := neZero_of_model_CutoffHomogenizationError M
  change cutoffHomogenizationErrorRepresentative M m m (s : ℝ)
      (Annealed.sigmaBar M comparatorScale) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    cutoffHomogenizationErrorRaw M m m (s : ℝ)
      (Annealed.sigmaBar M comparatorScale)
  exact (cutoffHomogenizationErrorRaw_ae_eq_representative M m m s.2
    (Annealed.sigmaBar M comparatorScale)).symm

/-- The public observable with a separate comparator scale is almost everywhere
CoarseGraining's literal `p = ∞`, `q = 2` homogenization error for `a_m` on
`\square_m`, normalized by `\bar\sigma_{\mathit{comparatorScale}}`. -/
theorem cutoffHomogenizationErrorAtComparatorScale_ae_eq_homogenizationErrorOnCube
    {d : ℕ} (M : ABKModel d) (m comparatorScale : ℤ)
    (s : {s : ℝ // 0 < s}) :
    cutoffHomogenizationErrorAtComparatorScale M m comparatorScale s =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      fun omega => @HCPolySupport.Book.Ch02.HomogenizationErrorOnCube d
        (originCube d m) (s : ℝ) .infinity (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M comparatorScale)) := by
  let : NeZero d := neZero_of_model_CutoffHomogenizationError M
  exact (cutoffHomogenizationErrorAtComparatorScale_ae_eq_raw M m comparatorScale s).trans
    (Filter.Eventually.of_forall fun omega =>
      cutoffHomogenizationErrorRaw_characterization M m m (s : ℝ)
        (Annealed.sigmaBar M comparatorScale) omega)

/-- The actual Section 3 observable is almost everywhere its raw manuscript
expression with coefficient, cube, and comparator scales all equal to `m`. -/
theorem cutoffHomogenizationError_ae_eq_raw {d : ℕ} (M : ABKModel d) (m : ℤ)
    (s : {s : ℝ // 0 < s}) :
    cutoffHomogenizationError M m s =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      @cutoffHomogenizationErrorRaw d M m m (s : ℝ)
        (Annealed.sigmaBar M m) := by
  simpa only [cutoffHomogenizationError] using
    cutoffHomogenizationErrorAtComparatorScale_ae_eq_raw M m m s

/-- The actual Section 3 observable is almost everywhere exactly `\mathcal
E_{s,\infty,2}(\square_m; a_m, \bar\sigma_m\operatorname{Id})` in
CoarseGraining's literal source semantics. -/
theorem cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube {d : ℕ}
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s}) :
    cutoffHomogenizationError M m s =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      fun omega => @HCPolySupport.Book.Ch02.HomogenizationErrorOnCube d
        (originCube d m) (s : ℝ) .infinity (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
        (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  simpa only [cutoffHomogenizationError] using
    cutoffHomogenizationErrorAtComparatorScale_ae_eq_homogenizationErrorOnCube M m m s

end

end Algsuperdiff.Section3.Observable
