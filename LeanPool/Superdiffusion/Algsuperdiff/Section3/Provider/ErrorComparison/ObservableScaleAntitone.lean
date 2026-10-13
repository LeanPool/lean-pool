/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.Monotonicity

/-!
# ObservableScaleAntitone

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: antitonicity of the Section 3 error observable in the scale

ABK26's display `e.mathcalE.monotone.ordered` asserts, among other things, that
for `t < s`

```
𝓔_{s,p,q}(□_m; a, a₀) ≤ 𝓔_{t,p,q}(□_m; a, a₀) ,
```

i.e. the multiscale homogenization error is **antitone** in the smoothness
exponent.  At `p = ∞` this is already proved on CoarseGraining's carrier by
`ErrorComparison.homogenizationErrorOnCube_infinity_finite_le_of_lt`
(`ErrorComparison.Monotonicity`); the mechanism is that the `p = ∞` scale
response is monotone in the depth (`scaleResponse_depth_monotone`), so that
CoarseGraining's `Homogenization.tsum_geometricWeight_le_of_monotone` applies
and the geometric reweighting costs nothing.

This file transports that inequality, at `q = 2`, from CoarseGraining's carrier
onto the Section 3 observable `Observable.cutoffHomogenizationError`, and
composes it with CoarseGraining's a.e. weak-Orlicz monotonicity so that a tail
estimate proved at one scale is available verbatim at every larger scale.

It is `Algsuperdiff.Section3.baseLoss`, not the error observable, that is
restricted to the open interval.

**No new constant, and no summability side condition**: both are already
discharged inside the `Monotonicity` lemma, whose tsum bookkeeping uses the
root cube's uniform deterministic response bound.

## Main results

* `cutoffHomogenizationError_ae_antitone`: a.e. antitonicity of the observable
  in the smoothness exponent.
* `isBigOWith_cutoffHomogenizationError_of_lt`: a weak-Orlicz upper-tail
  estimate for the observable at a scale `t` holds verbatim at every larger
  scale `s`.

## References

* ABK26, `e.mathcalE.monotone.ordered`; `d.mathcal.E` (2.28).
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3

noncomputable section

/-- The paper-wide assumption `2 ≤ d`, stored in the model, supplies the
nonzero-dimension instance required by CoarseGraining's doubled-response A. -/
private theorem neZero_of_model {d : ℕ} (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- **`e.mathcalE.monotone.ordered` on the Section 3 observable, at `q = 2`.**

For `0 < t < s`, almost surely under the cutoff-sample law,

```
𝓔_{s,∞,2}(□_m; a_m, σ_m) ≤ 𝓔_{t,∞,2}(□_m; a_m, σ_m) .
```

Taking `s = 1` gives the endpoint instance of any estimate proved on the open
interval `0 < t < 1`. -/
theorem cutoffHomogenizationError_ae_antitone {d : ℕ} (M : ABKModel d) (m : ℤ)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    Observable.cutoffHomogenizationError M m ⟨s, ht.trans hts⟩ ≤ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      Observable.cutoffHomogenizationError M m ⟨t, ht⟩ := by
  let : NeZero d := neZero_of_model M
  filter_upwards
    [Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube M m
        ⟨s, ht.trans hts⟩,
      Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube M m
        ⟨t, ht⟩] with omega hs ht'
  rw [hs, ht']
  exact homogenizationErrorOnCube_infinity_finite_le_of_lt (originCube d m)
    (Cutoff.coefficientCutoffTriadicCoeffFamily M m omega)
    (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ht hts
    (by norm_num)

/-- **Endpoint transport of a weak-Orlicz upper-tail estimate along the scale.**

If the Section 3 error observable at a scale `t` satisfies `𝓔_t ≤ O_Ψ(A)`, then
so does the observable at every larger scale `s`, with the *same* `Ψ` and the
*same* amplitude `A`.

This is the composition of `cutoffHomogenizationError_ae_antitone` with
CoarseGraining's `Homogenization.Book.Ch04.isBigOWith_of_ae_le`; neither piece
alone delivers the endpoint instance the Section 3.2 base case needs. -/
theorem isBigOWith_cutoffHomogenizationError_of_lt {d : ℕ} (M : ABKModel d)
    (m : ℤ) {Psi : ℝ → ℝ} {t s A : ℝ} (ht : 0 < t) (hts : t < s)
    (h : IndependentSums.IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure Psi
      (Observable.cutoffHomogenizationError M m ⟨t, ht⟩) A) :
    IndependentSums.IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure Psi
      (Observable.cutoffHomogenizationError M m ⟨s, ht.trans hts⟩) A :=
  Ch04.isBigOWith_of_ae_le h (cutoffHomogenizationError_ae_antitone M m ht hts)

end

end Algsuperdiff.Section3.Provider.ErrorComparison
