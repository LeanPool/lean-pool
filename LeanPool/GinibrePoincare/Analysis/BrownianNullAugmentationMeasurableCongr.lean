/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianNullAugmentationMeasurableCongr.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianNullAugmentationIndependence

/-! Null augmentation makes every almost-everywhere modification measurable in the same past. -/

@[expose] public section
open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

theorem ginibreNullAugmentation_measurable_congr {Ω E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (m : MeasurableSpace Ω) (X Y : Ω → E)
    (hY : @Measurable Ω E (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ Y)
    (hXY : X =ᵐ[P] Y) :
    @Measurable Ω E (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ X := by
  intro s hs
  have hU : P ((X ⁻¹' s) \ (Y ⁻¹' s)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hXY] with ω hω
    simp only [Set.mem_sdiff, Set.mem_preimage, hω]
    tauto
  have hV : P ((Y ⁻¹' s) \ (X ⁻¹' s)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hXY] with ω hω
    simp only [Set.mem_sdiff, Set.mem_preimage, hω]
    tauto
  have hu := ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m _ hU
  have hv := ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m _ hV
  have he : X ⁻¹' s = ((Y ⁻¹' s) \ ((Y ⁻¹' s) \ (X ⁻¹' s))) ∪ ((X ⁻¹' s) \ (Y ⁻¹' s)) := by
    ext ω
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  rw [he]
  exact ((hY hs).diff hv).union hu

end
end GinibrePoincare
