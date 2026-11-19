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

/-! # Linear compatibility of radial L² mollification

Continuous linear maps of the values commute with translation and radial kernel
averaging. This permits simultaneous mollification of gradient coordinates. These are
the general kernel statements of `LebesgueL2MollificationMaps` specialized to
`radialMollifierKernel`.
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
      radialL2MollifierAverage n m (L.compLpL 2 volume u) :=
  lebesgueL2KernelAverage_map n (continuous_radialMollifierKernel n m)
    (hasCompactSupport_radialMollifierKernel n m) L u

/-- Every scalar projection of the vector L² average is represented by the
actual convolution of that projection of a compact representative. -/
theorem radialL2MollifierAverage_projection_convolution_ae (n : ℕ)
    (m : ℕ) (L : V →L[ℝ] ℝ)
    (f : Configuration n → V) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (L.compLpL 2 volume (radialL2MollifierAverage n m (hf.toLp f)) :
      Configuration n → ℝ) =ᵐ[volume]
      (radialMollifierKernel n m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (L ∘ f)) :=
  lebesgueL2KernelAverage_projection_convolution_ae n (radialMollifierKernel_properties n m).1
    (hasCompactSupport_radialMollifierKernel n m) L f hf hc

end
end GinibrePoincare
