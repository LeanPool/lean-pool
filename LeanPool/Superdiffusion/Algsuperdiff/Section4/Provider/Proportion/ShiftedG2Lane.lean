/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.G2RatioTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShiftedConcentration

/-!
# ShiftedG2Lane

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₂` proportion lane re-based at an arbitrary scale `m₀`

ABK26, §4.1, `l.ratio.of.good.scales.for.mathcal.E`, composed into
`e.no.bad.scales.applied.for.lambdas` and read on the window `{m₀,…,m₀+n}`
rather than on `{0,…,n}`.

The proved `𝒢₂` lane is stated at base `0`: its window is the `Finset.Icc (0:ℤ)
(n:ℤ)` inside `IndicatorDensity.scaleProp`.  The manuscript's own reduction of
the general window to that one is "translate the array", carried out once and
generically in `ShiftedConcentration`.  This module runs the `𝒢₂` lane through
that translation.

## Contents

* `ratioTail_Xcal_shift` — the `𝒢₂` lemma-level tail on `{m₀,…,m₀+n}`.  Its
  hypothesis list is the base-`0` lane's, with the base `m₀` added and the
  deterministic reduction asked at **every** scale `m : ℤ` instead of only at
  `m ≥ 0`.
* `hreduce_eventG2_all` — the `𝒢₂` row reduction of `G2RowConversion` with its
  unused sign binder dropped, so that it can be instantiated at a negative
  scale.

## Scope

Provider material: proved local helpers.

## References

* ABK26, `l.ratio.of.good.scales.for.mathcal.E`; `p.concentration.for.scales`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The `𝒢₂` lemma-level tail on the window `{m₀,…,m₀+n}` -/

/-- **The `𝒢₂`-lane proportion tail at an arbitrary base scale `m₀`.**

For every window `{m₀,…,m₀+n}` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach (closed by the proved
`ratioTail_of_concentration` with no extra hypothesis) —

```
ℙ[ θ < (proportion of scales m₀+k, k ≤ n, at which Ev fails) ] ≤ exp(−c₁ n) / Q .
```

This is the base-`0` `𝒢₂` lemma-level tail with the base added: the same
hypothesis list, except that the deterministic reduction is asked at every scale
`m : ℤ` rather than only at `m ≥ 0`, which is what the lane in fact proves.  The
translation of the Appendix-D array is `ratioTail_of_concentration_shift`. -/
theorem ratioTail_Xcal_shift (M : ABKModel d) (s : {s : ℝ // 0 < s}) (D : ℝ)
    {A1 A2 p theta c1 Q : ℝ} {r : ℕ} (Ev : ℤ → Set (Cutoff.CutoffSample d)) (m0 : ℤ)
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hD : 0 < D) (hp : 1 ≤ p)
    (hs1 : (s : ℝ) ≤ 1) (hsp : 1 ≤ (s : ℝ) / 4 * p)
    (hr1 : 1 ≤ r) (hQ : 1 ≤ Q) (htheta0 : 0 < theta)
    (hthetar : theta * ((r : ℝ) + 1) < 1) (hc1 : 0 ≤ c1)
    (hrate : Real.log (Q * (r : ℝ)) + c1 * (r : ℝ)
      ≤ (s : ℝ) / 4 * p * theta / (16 * (r : ℝ)))
    (hcube : ∀ n : ℤ,
      Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
        (gammaSigma 2) (gammaSigma (1 / 2)) (Support.annularErrorObservable M n s)
        A1 A2)
    (hnorm : gammaMomentConst 1 * p * xcalScaleOne d (s : ℝ) A1 +
      gammaMomentConst (1 / 4) * p ^ (4 : ℝ) * xcalScaleQuarter d (s : ℝ) A2 ≤ D)
    (hrgap : 3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (r : ℕ))
    (hreduce : ∀ m : ℤ, ∀ omega ∈ (Ev m)ᶜ,
      9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p) <
        Yk (xcalArray M s D) ((s : ℝ) / 4) m omega)
    (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | theta < scaleProp (fun k => (Ev (m0 + k))ᶜ) n omega}
      ≤ ENNReal.ofReal (Real.exp (-c1 * (n : ℝ)) / Q) := by
  classical
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs40 : (0 : ℝ) < (s : ℝ) / 4 := by linarith only [hs0]
  have hs41 : (s : ℝ) / 4 ≤ 1 := by linarith only [hs1, hs0]
  have hmomL := lintegral_rpow_le_one_Xcal M s hA1 hA2 hp hD hcube hnorm
  have hindep := columnsIndep_Xcal M s D hr1 hrgap
  exact ratioTail_of_concentration_shift (Cutoff.cutoffSampleLaw M).toMeasure
    (xcalArray M s D) Ev m0 hp hs40 hs41 hsp hr1
    (fun k j => measurable_xcalArray M s D k j)
    (fun k j omega => xcalArray_nonneg M s hD k j omega)
    hmomL hindep hQ htheta0 hthetar hc1 hrate hreduce n

/-! ## 2. The reduction at every scale -/

/-- **The `hreduce` slot of the `𝒢₂` concentration assembly, for the enlarged
family, at every scale.**

This is the `𝒢₂` row reduction with its **unused** sign binder `0 ≤ m`
dropped, so that it can be instantiated at a negative scale.  The proof runs on
the public, sign-condition-free
`G2RowConversion.lt_Yk_of_notMem_eventG2`.

`hthr` is the lane's threshold identification: the Appendix-D level
`9 s'^{-1}C_⋆^{1/p}θ^{-1/p}` at `s' = ¼s` must sit below `D^{-1}ε²s^{-1}`. -/
theorem hreduce_eventG2_all (M : ABKModel d) (s : {s : ℝ // 0 < s}) {ep p theta D : ℝ}
    (hD : 0 < D)
    (hthr : 9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      ≤ D⁻¹ * (ep ^ 2 / (s : ℝ)))
    (m : ℤ) (omega : Cutoff.CutoffSample d)
    (homega : omega ∈ (Support.eventG2 M m s ep ∪ (goodRowSetG2 M s)ᶜ)ᶜ) :
    9 * ((s : ℝ) / 4)⁻¹ * Cstar ^ (1 / p) * theta ^ (-1 / p)
      < Yk (xcalArray M s D) ((s : ℝ) / 4) m omega := by
  have h1 : omega ∉ Support.eventG2 M m s ep := fun hc => homega (Or.inl hc)
  have h2 : omega ∈ goodRowSetG2 M s := by
    by_contra hc
    exact homega (Or.inr hc)
  exact lt_of_le_of_lt hthr (lt_Yk_of_notMem_eventG2 M s hD m h2 h1)

end

end Algsuperdiff.Section4.Provider.Proportion
