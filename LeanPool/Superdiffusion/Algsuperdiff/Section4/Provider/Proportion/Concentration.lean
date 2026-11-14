/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.Ycal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorArray
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorDensityTails
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.AnnulusSeparation

/-!
# Concentration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₀` lane: unit moments and `r`-dependence

ABK26, §4.1, `l.good.scales.ratio.lambda`, the moment and `p` choice,
the two-dependence step and the display `e.no.bad.scales.applied.for.lambdas`.

## What is assembled

1. **`lintegral_rpow_le_one_Ycal`** — the Appendix-D moment hypothesis
   `E[(D^{-1}𝒴_n)^p] ≤ 1` from the `𝒴`-tail, via the proved `IndicatorArray`
   discharger.  This is's "by taking `p := exp(K^{-1}c⋆²γ^{-1})` with `K(d)`
   large enough, we obtain `E[𝒴_n^p] ≤ 1`"; the numerical step of that sentence
   is the hypothesis `hnorm` (`gammaMomentConst σ · p^{1/σ} · K ≤ D`), which is
   exactly the manuscript's own "for `K(d)` large enough".

2. **`columnsIndep_Ycal`** — the `2`-dependence assertion, at the honest
   `r(d)`.  The theorem below is stated at the **general `r`**, so no dimension
   restriction enters this file; `d ≤ 81` gives `r = 2`,
   and larger `d` is covered by
   `separatedBy_annulusRegion_of_gap` at the larger `r(d)`.  The cost of `r >
   2` is absorbed in the rate.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.good.scales.ratio.lambda`.
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

/-- **The Appendix-D array of the `𝒢₀` lane**, `X_{k,n} = D^{-1}𝒴_n`.  The
normalizer `D` carries the manuscript's `γ^{-4}`. -/
def ycalArray (M : ABKModel d) (Ccg sprime D : ℝ) :
    ℤ → ℤ → Cutoff.CutoffSample d → ℝ :=
  colArray fun n omega => D⁻¹ * Ycal M Ccg sprime n omega

@[simp] theorem ycalArray_apply (M : ABKModel d) (Ccg sprime D : ℝ) (k j : ℤ)
    (omega : Cutoff.CutoffSample d) :
    ycalArray M Ccg sprime D k j omega = D⁻¹ * Ycal M Ccg sprime j omega := rfl

/-! ## 1. The Appendix-D unit moments -/

/-- **`E[(D^{-1}𝒴_n)^p] ≤ 1`.**  The Appendix-D moment hypothesis
`e.Xk.p.moment.twosided`, in its honest `∫⁻` reading, for the column array of
the `𝒴`-atoms.

`hnorm` is the manuscript's own numerical step: at `σ = 1/3` the moment growth
is `gammaMomentConst σ · p³ · K` makes it `≤ 1` "by taking `p:=
exp(K^{-1}c⋆²γ^{-1})` with `K(d)` large enough" — i.e. by the smallness of the
tail scale `K` against `p³`. -/
theorem lintegral_rpow_le_one_Ycal (M : ABKModel d) (Ccg : ℝ) {sigma sprime p D K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) (hp : 1 ≤ p) (hD : 0 < D)
    (htail : ∀ n : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma sigma)
      (Ycal M Ccg sprime n) K)
    (hnorm : gammaMomentConst sigma * p ^ sigma⁻¹ * K ≤ D) :
    ∀ k j : ℤ, ∫⁻ omega,
        ENNReal.ofReal ((ycalArray M Ccg sprime D k j omega) ^ p)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ 1 :=
  colArray_lintegral_rpow_le_one hsigma hK hp hD
    (fun j omega => Ycal_nonneg M Ccg sprime j omega)
    (fun j => (measurable_Ycal M Ccg sprime j).aemeasurable) htail hnorm

/-! ## 3. `r`-dependence of the `𝒴_n` -/

/-- **The Appendix-D independence hypothesis `e.independent.columns.twosided` for
the `𝒢₀` lane.**

The atoms `𝒴_n` are `r`-dependent for every `r ≥ 1` with
`3 + 2·3^{1−2}√d ≤ 3^r`, i.e. `3 + (2/3)√d ≤ 3^r`: the annuli at index gap `≥ r`
are separated at the shared-shell threshold `√d·3^{min(n−2, n'−2)}`, which is
exactly what the varying-level producer consumes.  No dimension restriction is
imposed here — `r` is a parameter, and `d ≤ 81` gives the manuscript's `r = 2`. -/
theorem columnsIndep_Ycal (M : ABKModel d) (Ccg sprime D : ℝ) {r : ℕ}
    (hr1 : 1 ≤ r)
    (hr : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    (hloc : ∀ n : ℤ,
      Measurable[Cutoff.cutoffSampleLocalSigma M (n - 2) (annulusRegion d n)]
        (Ycal M Ccg sprime n)) :
    ColumnsIndep (Cutoff.cutoffSampleLaw M).toMeasure (ycalArray M Ccg sprime D) r := by
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
    exact (hloc (j * (r : ℤ) + b)).const_mul D⁻¹

end

end Algsuperdiff.Section4.Provider.Proportion
