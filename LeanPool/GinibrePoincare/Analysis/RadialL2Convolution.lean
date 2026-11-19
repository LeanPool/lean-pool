/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialL2Convolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialL2MollifierAverage
public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Convolution

/-! # Concrete radial smooth compact convolution in ordinary L²

For compactly supported L² representatives, the actual normalized radial kernel
convolution represents the Bochner L² average. Consequently the concrete
smooth compact functions converge strongly in L² as the kernel radius shrinks.
These are the general smooth-compact-kernel statements of `LebesgueL2Convolution`
specialized to `radialMollifierKernel`.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

theorem integral_radial_convolution_mul_test (n : ℕ) (m : ℕ)
    (f θ : Configuration n → ℝ) (hf : Integrable f volume)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x, (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) x * θ x) =
      ∫ y, radialMollifierKernel n m y * (∫ x, f (x - y) * θ x) :=
  integral_kernel_convolution_mul_test n (radialMollifierKernel_properties n m).2.2.2.1
    f θ hf hθ hc

/-- Concrete convolution has an actual smooth compact representative in ordinary L². -/
theorem memLp_radial_convolution_compact (n : ℕ) (m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) 2 volume :=
  memLp_kernel_convolution_compact n (radialMollifierKernel_properties n m).1
    (hasCompactSupport_radialMollifierKernel n m) f hf hc

/-- The actual Bochner L² average is represented by the concrete normalized radial kernel
convolution. -/
theorem radialL2MollifierAverage_convolution_ae (n : ℕ) (m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (radialL2MollifierAverage n m (hf.toLp f) : Configuration n → ℝ) =ᵐ[volume]
      (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) :=
  lebesgueL2KernelAverage_convolution_ae n (radialMollifierKernel_properties n m).1
    (hasCompactSupport_radialMollifierKernel n m) f hf hc

/-- The convolution of a compactly supported Lebesgue `L²` function `f` with the radial
mollifier kernel `radialMollifierKernel n m`, as a vector of Lebesgue `L²`. -/
def radialSmoothCompactMollification (n : ℕ) (m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Lp ℝ 2 (volume : Measure (Configuration n)) :=
  (memLp_radial_convolution_compact n m f hf hc).toLp
    (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f)

theorem radialSmoothCompactMollification_eq_average (n : ℕ)
    (m : ℕ) (f : Configuration n → ℝ)
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    radialSmoothCompactMollification n m f hf hc = radialL2MollifierAverage n m (hf.toLp f) := by
  apply Lp.ext
  exact (memLp_radial_convolution_compact n m f hf hc).coeFn_toLp.trans
    (radialL2MollifierAverage_convolution_ae n m f hf hc).symm

/-- Actual smooth compact radial-kernel mollifications converge strongly in L². -/
theorem radialSmoothCompactMollification_tendsto (n : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Tendsto (fun m => radialSmoothCompactMollification n m f hf hc)
      atTop (𝓝 (hf.toLp f)) := by
  simp_rw [radialSmoothCompactMollification_eq_average]
  exact radialL2MollifierAverage_tendsto n (hf.toLp f)

end
end GinibrePoincare
