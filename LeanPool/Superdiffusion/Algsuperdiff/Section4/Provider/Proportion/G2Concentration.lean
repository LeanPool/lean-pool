/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2RowConversion
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2Locality

/-!
# G2Concentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` lane: `r`-dependence of the atoms `X_j`

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E`: the Appendix-D
independence hypothesis of the lane's atoms.

## `r`-dependence

`columnsIndep_Xcal` is the `𝒢₂` twin of `Concentration.columnsIndep_Ycal`, and
it runs on **exactly** the same geometry: the atom `X_j` reads only truncation
levels `≤ j − 2` and only on `annulusRegion d j`
(`G2Locality.measurable_Xcal_annulusRegion_local`, a statement with **no**
hypotheses), so the varying-level producer
`Probability.iIndepFun_of_local_cutoffSample` applies at the separation
supplied by `Probability.separatedBy_annulusRegion_of_gap` at the truncation
offset `c = 2`.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory ProbabilityTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `r`-dependence of the `𝒢₂` atoms -/

/-- **The Appendix-D independence hypothesis `e.independent.columns.twosided` for
the `𝒢₂` lane.**

The atoms `X_j` are `r`-dependent for every `r ≥ 1` with
`3 + 2·3^{1−2}√d ≤ 3^r`, i.e. `3 + (2/3)√d ≤ 3^r`.  The statement is at the
**general `r`**, so no dimension restriction enters this file.

Unlike the `𝒢₀` lane, the locality input needs no premise at all: the `𝒢₂`
locality endpoint `measurable_Xcal_annulusRegion_local` is unconditional. -/
theorem columnsIndep_Xcal (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ)) :
    ColumnsIndep (Cutoff.cutoffSampleLaw M).toMeasure (xcalArray M s D) r := by
  refine columnsIndep_colArray _ r fun b => ?_
  refine iIndepFun_of_local_cutoffSample M (fun j : ℤ => j * (r : ℤ) + b - 2)
    (U := fun j : ℤ => annulusRegion d (j * (r : ℤ) + b))
    (fun j => measurableSet_annulusRegion d _) ?_ ?_
  · intro j j' hjj'
    have hgap : (r : ℤ) ≤ |j * (r : ℤ) + b - (j' * (r : ℤ) + b)| := by
      have hrw : j * (r : ℤ) + b - (j' * (r : ℤ) + b) = (j - j') * (r : ℤ) := by ring
      rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (r : ℤ))]
      exact le_mul_of_one_le_left (by positivity)
        (Int.one_le_abs (sub_ne_zero_of_ne hjj'))
    exact separatedBy_annulusRegion_of_gap (c := 2) (r := r) hr1 hr hgap
  · intro j
    exact (measurable_Xcal_annulusRegion_local M s (j * (r : ℤ) + b)).const_mul D⁻¹

end

end Algsuperdiff.Section4.Provider.Proportion
