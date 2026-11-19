/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/LebesgueL2MollificationMaps.lean.
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

public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Convolution

/-! # Linear compatibility of ordinary L² mollification

Continuous linear maps of the values commute with translation and with kernel averaging.
This permits simultaneous mollification of gradient coordinates. Normalized smooth bumps
are the special case `K = φ.normed volume`.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology Convolution ContDiff
namespace GinibrePoincare
noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- Applying a continuous linear map to the values commutes with translation. -/
theorem lebesgueL2Translate_map (n : ℕ) (y : Configuration n) (L : V →L[ℝ] W)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (lebesgueL2Translate n y u) =
      lebesgueL2Translate n y (L.compLpL 2 volume u) := by
  apply Lp.ext
  have he := (eventually_add_right_iff (volume : Measure (Configuration n)) (-y)).mpr
    (L.coeFn_compLpL u)
  filter_upwards [L.coeFn_compLpL (lebesgueL2Translate n y u),
    lebesgueL2Translate_ae n y u,
    lebesgueL2Translate_ae n y (L.compLpL 2 volume u), he] with x hx ht hs he
  simpa only [sub_eq_add_neg] using hx.trans ((congrArg L ht).trans (he.symm.trans hs.symm))

/-- Applying a continuous linear map to the values commutes with kernel averaging. -/
theorem lebesgueL2KernelAverage_map (n : ℕ) {K : Configuration n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (L : V →L[ℝ] W) (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (lebesgueL2KernelAverage n K u) =
      lebesgueL2KernelAverage n K (L.compLpL 2 volume u) := by
  unfold lebesgueL2KernelAverage
  rw [← (L.compLpL 2 volume).integral_comp_comm
    (integrable_lebesgueL2KernelIntegrand n hK hKc u)]
  simp only [map_smul, lebesgueL2Translate_map]

/-- Every scalar projection of the vector L² kernel average is represented by the actual
convolution of that projection of a compact representative. -/
theorem lebesgueL2KernelAverage_projection_convolution_ae (n : ℕ) {K : Configuration n → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) (L : V →L[ℝ] ℝ)
    (f : Configuration n → V) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (L.compLpL 2 volume (lebesgueL2KernelAverage n K (hf.toLp f)) :
      Configuration n → ℝ) =ᵐ[volume]
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (L ∘ f)) := by
  have hm : MemLp (L ∘ f) 2 volume := L.comp_memLp' hf
  have he : L.compLpL 2 volume (hf.toLp f) = hm.toLp (L ∘ f) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      hm.coeFn_toLp] with x hx hy hz
    simp only [Function.comp_apply] at hz
    rw [hx, hy, hz]
  rw [lebesgueL2KernelAverage_map n hK.continuous hKc, he]
  exact lebesgueL2KernelAverage_convolution_ae n hK hKc (L ∘ f) hm (hc.comp_left L.map_zero)

/-- Applying a continuous linear map to the values commutes with bump averaging. -/
theorem lebesgueL2BumpAverage_map (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (L : V →L[ℝ] W) (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (lebesgueL2BumpAverage n φ u) =
      lebesgueL2BumpAverage n φ (L.compLpL 2 volume u) :=
  lebesgueL2KernelAverage_map n φ.continuous_normed φ.hasCompactSupport_normed L u

/-- Every scalar projection of the vector L² average is represented by the
actual convolution of that projection of a compact representative. -/
theorem lebesgueL2BumpAverage_projection_convolution_ae (n : ℕ)
    (φ : ContDiffBump (0 : Configuration n)) (L : V →L[ℝ] ℝ)
    (f : Configuration n → V) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (L.compLpL 2 volume (lebesgueL2BumpAverage n φ (hf.toLp f)) :
      Configuration n → ℝ) =ᵐ[volume]
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (L ∘ f)) :=
  lebesgueL2KernelAverage_projection_convolution_ae n (φ.contDiff_normed (n := ⊤))
    φ.hasCompactSupport_normed L f hf hc

end
end GinibrePoincare
