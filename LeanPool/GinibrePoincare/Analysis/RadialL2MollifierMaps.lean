/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialL2MollifierMaps.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialL2Convolution
public import LeanPool.GinibrePoincare.Analysis.LebesgueL2MollificationMaps

/-! # Linear compatibility of ordinary L² mollification

Continuous linear maps of the values commute with translation and normalized
bump averaging. This permits simultaneous mollification of gradient coordinates.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology Convolution
namespace GinibrePoincare
noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Applying a continuous linear map to the values commutes with bump averaging. -/
theorem radialL2MollifierAverage_map (n : ℕ) (m : ℕ)
    (L : V →L[ℝ] W) (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (radialL2MollifierAverage n m u) =
      radialL2MollifierAverage n m (L.compLpL 2 volume u) := by
  unfold radialL2MollifierAverage
  rw [← (L.compLpL 2 volume).integral_comp_comm
    (integrable_radialL2MollifierIntegrand n m u)]
  simp only [map_smul, lebesgueL2Translate_map]

/-- Every scalar projection of the vector L² average is represented by the
actual convolution of that projection of a compact representative. -/
theorem radialL2MollifierAverage_projection_convolution_ae (n : ℕ)
    (m : ℕ) (L : V →L[ℝ] ℝ)
    (f : Configuration n → V) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (L.compLpL 2 volume (radialL2MollifierAverage n m (hf.toLp f)) :
      Configuration n → ℝ) =ᵐ[volume]
      (radialMollifierKernel n m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (L ∘ f)) := by
  have hm : MemLp (L ∘ f) 2 volume := L.comp_memLp' hf
  have he : L.compLpL 2 volume (hf.toLp f) = hm.toLp (L ∘ f) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      hm.coeFn_toLp] with x hx hy hz
    simp only [Function.comp_apply] at hz
    rw [hx, hy, hz]
  rw [radialL2MollifierAverage_map, he]
  exact radialL2MollifierAverage_convolution_ae n m (L ∘ f) hm
    (hc.comp_left L.map_zero)

end
end GinibrePoincare
