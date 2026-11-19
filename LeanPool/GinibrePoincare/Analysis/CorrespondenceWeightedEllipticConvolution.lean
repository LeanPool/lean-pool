/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticConvolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticMollification
public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Concrete smooth compact convolution in ordinary L²

For compactly supported L² representatives, the actual normalized bump
convolution represents the Bochner L² average. Consequently the concrete
smooth compact functions converge strongly in L² as the bump radius shrinks.

The arguments live in `LeanPool.GinibrePoincare.Analysis.LebesgueL2Convolution`; this file
specializes them to a finite-dimensional real inner-product space with its Lebesgue `volume`.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeighted_integral_bump_convolution_mul_test (φ : ContDiffBump (0 : E))
    (f θ : E → ℝ) (hf : Integrable f volume)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x * θ x) =
      ∫ y, φ.normed volume y * (∫ x, f (x - y) * θ x) :=
  integral_bumpConvolution_mul_test φ f θ hf hθ hc

/-- Concrete convolution has an actual smooth compact representative in ordinary L². -/
theorem correspondenceWeighted_memLp_bump_convolution_compact (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) 2 volume :=
  memLp_bumpConvolution_of_compact φ f hf hc

/-- The actual Bochner L² average is represented by the concrete normalized bump convolution. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_convolution_ae (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (correspondenceWeightedLebesgueL2BumpAverage φ (hf.toLp f) : E → ℝ) =ᵐ[volume]
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) :=
  l2BumpAverage_convolution_ae φ f hf hc

/-- The Lebesgue `L²` class of the mollification `φ.normed volume ⋆ f` of a compactly supported
`f ∈ L²`. -/
def correspondenceWeightedLebesgueSmoothCompactMollification (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Lp ℝ 2 (volume : Measure (E)) :=
  l2SmoothCompactMollification φ f hf hc

theorem correspondenceWeighted_lebesgueSmoothCompactMollification_eq_average
    (φ : ContDiffBump (0 : E)) (f : E → ℝ)
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    correspondenceWeightedLebesgueSmoothCompactMollification φ f hf hc =
        correspondenceWeightedLebesgueL2BumpAverage φ (hf.toLp f) :=
  l2SmoothCompactMollification_eq_average φ f hf hc

/-- Actual smooth compact mollifications of a compact L² function converge strongly in L². -/
theorem correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto
    (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Tendsto (fun m => correspondenceWeightedLebesgueSmoothCompactMollification (φ m) f hf hc)
      atTop (𝓝 (hf.toLp f)) :=
  l2SmoothCompactMollification_tendsto φ hφ f hf hc

end
end GinibrePoincare
