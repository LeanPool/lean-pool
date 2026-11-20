/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungMollifier.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMultiplierComposition
public import LeanPool.GinibrePoincare.Analysis.LebesgueL2MollificationMaps
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBumpAverage
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Correspondence Dolbeault Young mollifier

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization. The complex representation of the bump
average is read off from the shared real projection lemma
`lebesgueL2KernelAverage_projection_convolution_ae`, applied to the real
and imaginary parts.

Main results: `dolbeaultPiBump_convolution_tendsto`.
-/

@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

theorem dolbeaultPiBump_contDiff (n : ℕ) (φ : ContDiffBump (0 : ℂ)) :
    ContDiff ℝ ∞ (piPlanarBump n φ) := by
  unfold piPlanarBump
  apply contDiff_prod
  intro i hi
  exact (φ.contDiff_normed (n := ⊤)).comp (contDiff_apply ℝ (fun _ => ℂ) i)

theorem dolbeaultPiBump_convolution_smooth (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) :=
  (piPlanarBump_compact n φ).contDiff_convolution_left (lsmul ℝ ℝ)
    (dolbeaultPiBump_contDiff n φ) (hf.locallyIntegrable (by norm_num))

theorem dolbeaultPiBump_convolution_memLp (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) 2 volume :=
  (dolbeaultPiBump_convolution_smooth n φ f hf).continuous.memLp_of_hasCompactSupport
    ((piPlanarBump_compact n φ).convolution (lsmul ℝ ℝ) hc)

/-- Ordinary strong L² smoothing is represented by actual smooth convolution,
for arbitrary compact L² input, without continuity of its representative. -/
theorem dolbeaultPiBump_convolution_ae (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (piL2BumpAverage n φ (hf.toLp f) : Configuration n → ℂ) =ᵐ[volume]
      piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f := by
  have hK := dolbeaultPiBump_contDiff n φ
  have hKc := piPlanarBump_compact n φ
  have hExists := hKc.convolutionExists_left (lsmul ℝ ℝ) hK.continuous
    (hf.locallyIntegrable (by norm_num))
  -- Each real projection of both sides is the convolution of that projection of `f`.
  have hPart (L : ℂ →L[ℝ] ℝ) : ∀ᵐ x ∂volume,
      L ((piL2BumpAverage n φ (hf.toLp f)) x) =
        L ((piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) x) := by
    filter_upwards [L.coeFn_compLpL (piL2BumpAverage n φ (hf.toLp f)),
      lebesgueL2KernelAverage_projection_convolution_ae n hK hKc L f hf hc] with x hx hy
    rw [← hx]
    refine hy.trans ?_
    rw [convolution_def, convolution_def, ← L.integral_comp_comm (hExists x)]
    simp only [lsmul_apply, Function.comp_apply, map_smul, smul_eq_mul]
  filter_upwards [hPart Complex.reCLM, hPart Complex.imCLM] with x hre him
  exact Complex.ext (by simpa using hre) (by simpa using him)

theorem dolbeaultPiBump_convolution_tendsto (n : ℕ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Tendsto (fun m => (dolbeaultPiBump_convolution_memLp n (φ m) f hf hc).toLp
      (piPlanarBump n (φ m) ⋆[lsmul ℝ ℝ, volume] f)) atTop (𝓝 (hf.toLp f)) := by
  have he (m : ℕ) : (dolbeaultPiBump_convolution_memLp n (φ m) f hf hc).toLp
      (piPlanarBump n (φ m) ⋆[lsmul ℝ ℝ, volume] f) = piL2BumpAverage n (φ m) (hf.toLp f) := by
    apply Lp.ext
    exact (dolbeaultPiBump_convolution_memLp n (φ m) f hf hc).coeFn_toLp.trans
      (dolbeaultPiBump_convolution_ae n (φ m) f hf hc).symm
  simp_rw [he]
  exact piL2BumpAverage_tendsto n φ hφ (hf.toLp f)

end
end GinibrePoincare
