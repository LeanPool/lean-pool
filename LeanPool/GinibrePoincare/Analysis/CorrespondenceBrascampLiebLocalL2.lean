/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebLocalL2.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebGibbs
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
/-!
# Correspondence Brascamp Lieb local L 2

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.
-/

@[expose] public section
open MeasureTheory Measure
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- `f` is locally square integrable: it lies in `L²(volume.restrict K)` for every compact `K`. -/
def CorrespondenceBrascampLiebLocallyL2 (f : E → ℝ) : Prop :=
  ∀ K : Set E, IsCompact K → MemLp f 2 (volume.restrict K)

theorem correspondenceBrascampLieb_localL2_locallyIntegrable
    (f : E → ℝ) (hf : CorrespondenceBrascampLiebLocallyL2 f) : LocallyIntegrable f volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact memLp_one_iff_integrable.mp ((hf K hK).mono_exponent (by norm_num))

theorem correspondenceBrascampLieb_localL2_compact_multiplier
    (f η : E → ℝ) (hf : CorrespondenceBrascampLiebLocallyL2 f)
    (hη : Continuous η) (hc : HasCompactSupport η) :
    MemLp (fun x => η x*f x) 2 (volume : Measure E) := by
  have ht : MemLp η ⊤ ((volume : Measure E).restrict (tsupport η)) :=
    hη.memLp_top_of_hasCompactSupport hc _
  have hm := ht.fun_mul (r := 2) (hf (tsupport η) hc)
  have hi := (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr hm
  apply hi.ae_eq
  exact ae_of_all volume fun x => by
    by_cases hx : x ∈ tsupport η
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]

end
end GinibrePoincare
