/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEPermutationMeasure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUEPaperH1
/-!
# Correspondence GUE permutation measure

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueFullMeasure_permutation_preserving`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem gueFullMeasure_permutation_integral (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x, f (guePermute n σ x) ∂gueFullMeasure n)=(∫x, f x ∂gueFullMeasure n) := by
  rw [gueFullMeasure_integral, gueFullMeasure_integral]
  congr 1
  have h := (guePermute_volume_preserving n σ).integral_comp
    (guePermuteIsometry n σ).toMeasurableEquiv.measurableEmbedding
    (fun x => gueRawDensity n x*f x)
  have he x : gueRawDensity n (guePermute n σ x)=gueRawDensity n x := gueRawDensity_symmetric n σ x
  simpa only [he] using h

theorem gueFullMeasure_permutation_preserving {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (guePermute n σ) (gueFullMeasure n) (gueFullMeasure n) := by
  let := gueFullMeasure_probability hn
  have hm : Measurable (guePermute n σ) := (guePermuteIsometry n σ).continuous.measurable
  refine ⟨hm, Measure.ext (fun s hs => ?_)⟩
  have hi := gueFullMeasure_permutation_integral n σ (s.indicator (fun _ => 1))
  rw [← integral_map hm.aemeasurable (by exact (measurable_const.indicator
                                           hs).aestronglyMeasurable)] at hi
  change (∫x, s.indicator (1 : EuclideanSpace ℝ (Fin n)→ℝ) x ∂(gueFullMeasure n).map (guePermute n
      σ))=
    (∫x, s.indicator (1 : EuclideanSpace ℝ (Fin n)→ℝ) x ∂gueFullMeasure n) at hi
  rw [integral_indicator_one hs, integral_indicator_one hs] at hi
  calc
    (gueFullMeasure n).map (guePermute n σ) s=
        ENNReal.ofReal (((gueFullMeasure n).map (guePermute n σ) s).toReal) :=
      (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
    _ = ENNReal.ofReal ((gueFullMeasure n s).toReal) := congrArg ENNReal.ofReal hi
    _ = gueFullMeasure n s := ENNReal.ofReal_toReal (measure_lt_top _ _).ne

end
end GinibrePoincare
