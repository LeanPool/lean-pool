/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexTransportMeasure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.StrongConvexQuantileTransport
public import Mathlib.Probability.CDF

/-!
# Strong convex transport measure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `cdfQuantileTransport_map`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
namespace GinibrePoincare
noncomputable section

/-- Quantile transport pushes the actual source probability measure to the
actual target probability measure; its equality is proved on half-lines. -/
theorem cdfQuantileTransport_map (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hFm : StrictMono (cdf μ)) (hFr : cdf μ '' univ = Ioo 0 1)
    (hm : StrictMonoOn (cdf ν) (Ioi 0)) (hr : cdf ν '' Ioi 0 = Ioo 0 1)
    (hzero : ∀ y, y ≤ 0 → cdf ν y = 0)
    (hT : Measurable (cdfQuantileTransport (cdf μ) (cdf ν) hm hr)) :
    μ.map (cdfQuantileTransport (cdf μ) (cdf ν) hm hr) = ν := by
  let T := cdfQuantileTransport (cdf μ) (cdf ν) hm hr
  let : IsProbabilityMeasure (μ.map T) := by infer_instance
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply hT measurableSet_Iic]
  by_cases hy : 0 < y
  · have hyF : cdf ν y ∈ Ioo (0 : ℝ) 1 := hr ▸ mem_image_of_mem (cdf ν) hy
    let b := increasingCDFQuantileOn (cdf μ) univ (hFm.strictMonoOn univ) hFr (cdf ν y)
    have hb : cdf μ b = cdf ν y := increasingCDFQuantileOn_right_inverse
      (cdf μ) univ (hFm.strictMonoOn univ) hFr (cdf ν y) hyF
    have hpre : T ⁻¹' Iic y = Iic b := by
      ext x
      have hx : cdf μ x ∈ Ioo (0 : ℝ) 1 := hFr ▸ mem_image_of_mem (cdf μ) (mem_univ x)
      have hTx : 0 < T x := increasingCDFQuantileOn_mem (cdf ν) (Ioi 0) hm hr (cdf μ x) hx
      have hGT : cdf ν (T x) = cdf μ x :=
        increasingCDFQuantileOn_right_inverse (cdf ν) (Ioi 0) hm hr (cdf μ x) hx
      change T x ≤ y ↔ x ≤ b
      constructor
      · intro h
        have hFx : cdf μ x ≤ cdf μ b := by
          rw [hb, ← hGT]
          exact hm.monotoneOn hTx hy h
        exact hFm.le_iff_le.mp hFx
      · intro h
        have hFx : cdf μ x ≤ cdf ν y := by rw [← hb]; exact hFm.monotone h
        by_contra hn
        have hh := hm hy hTx (lt_of_not_ge hn)
        rw [hGT] at hh
        exact (not_lt_of_ge hFx) hh
    rw [hpre, ← ofReal_cdf μ b, hb, ofReal_cdf ν y]
  · have hpre : T ⁻¹' Iic y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxF : cdf μ x ∈ Ioo (0 : ℝ) 1 := hFr ▸ mem_image_of_mem (cdf μ) (mem_univ x)
      have hTx : 0 < T x := increasingCDFQuantileOn_mem (cdf ν) (Ioi 0) hm hr (cdf μ x) hxF
      exact (not_le_of_gt (lt_of_le_of_lt (le_of_not_gt hy) hTx)) hx
    rw [hpre, measure_empty, ← ofReal_cdf ν y, hzero y (le_of_not_gt hy)]
    simp

end
end GinibrePoincare
