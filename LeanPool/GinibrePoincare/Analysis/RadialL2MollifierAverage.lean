/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialL2MollifierAverage.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialMollifierKernels
public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Mollification

/-! # Strong L² convergence of actual radial kernel averages

The normalized shrinking radial kernels act by Bochner averages of translations
on scalar and vector Lebesgue L² spaces, as the general kernel averages
`lebesgueL2KernelAverage`. Only the kernel-specific facts (smoothness, compact
support, positivity, unit mass and shrinking support) are proved here; the averaging
arguments are the general ones. Identification with pointwise convolution is a
separate step.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The Bochner integral `∫ y, K y • τ_y u` in Lebesgue `L²` of the translates `τ_y u` of `u`
weighted by the radial mollifier kernel `K = radialMollifierKernel n m`. -/
def radialL2MollifierAverage (n m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) : Lp V 2 (volume : Measure (Configuration n))
        :=
  lebesgueL2KernelAverage n (radialMollifierKernel n m) u

theorem continuous_radialMollifierKernel (n m : ℕ) : Continuous (radialMollifierKernel n m) :=
  (radialMollifierKernel_properties n m).1.continuous

theorem hasCompactSupport_radialMollifierKernel (n m : ℕ) :
    HasCompactSupport (radialMollifierKernel n m) :=
  (radialMollifierKernel_properties n m).2.1

omit [CompleteSpace V] in
/-- The actual radial average is a well-defined Bochner integral in L². -/
theorem integrable_radialL2MollifierIntegrand (n m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Integrable (fun y => radialMollifierKernel n m y • lebesgueL2Translate n y u) :=
  integrable_lebesgueL2KernelIntegrand n (continuous_radialMollifierKernel n m)
    (hasCompactSupport_radialMollifierKernel n m) u

/-- Continuous linear test pairings commute with the actual L² bump average. -/
theorem radialL2MollifierAverage_pairing (n : ℕ) (m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n)))
    (L : Lp V 2 (volume : Measure (Configuration n)) →L[ℝ] ℝ) :
    L (radialL2MollifierAverage n m u) =
      ∫ y, radialMollifierKernel n m y * L (lebesgueL2Translate n y u) :=
  lebesgueL2KernelAverage_pairing n (continuous_radialMollifierKernel n m)
    (hasCompactSupport_radialMollifierKernel n m) u L

/-- The Bochner L² average has the expected translated representative pairing
against every actual scalar L² test. -/
theorem radialL2MollifierAverage_test_pairing (n : ℕ) (m : ℕ)
    (u : Lp ℝ 2 (volume : Measure (Configuration n)))
    (w : Configuration n → ℝ) (hw : MemLp w 2 volume) :
    (∫ x, radialL2MollifierAverage n m u x * w x) =
      ∫ y, radialMollifierKernel n m y * (∫ x, u (x - y) * w x) :=
  lebesgueL2KernelAverage_test_pairing n (continuous_radialMollifierKernel n m)
    (hasCompactSupport_radialMollifierKernel n m) u w hw

/-- A bound on translations over the support bounds the radial averaged error. -/
theorem radialL2MollifierAverage_error_le (n m : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) (ε : ℝ)
    (he : ∀ y ∈ Function.support (radialMollifierKernel n m),
      ‖lebesgueL2Translate n y u - u‖ ≤ ε) :
    ‖radialL2MollifierAverage n m u - u‖ ≤ ε :=
  lebesgueL2KernelAverage_error_le n (continuous_radialMollifierKernel n m)
    (hasCompactSupport_radialMollifierKernel n m) (radialMollifierKernel_properties n m).2.2.1
    (radialMollifierKernel_properties n m).2.2.2.2 u ε he

/-- Actual normalized radial kernel averages converge strongly in scalar or vector L². -/
theorem radialL2MollifierAverage_tendsto (n : ℕ)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    Tendsto (fun m => radialL2MollifierAverage n m u) atTop (𝓝 u) := by
  have hr : Tendsto (fun m : ℕ => 2 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have hi : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
    simpa [div_eq_mul_inv] using hi.const_mul 2
  exact lebesgueL2KernelAverage_tendsto n (radialMollifierKernel n)
    (continuous_radialMollifierKernel n) (hasCompactSupport_radialMollifierKernel n)
    (fun m => (radialMollifierKernel_properties n m).2.2.1)
    (fun m => (radialMollifierKernel_properties n m).2.2.2.2) _ hr
    (radialMollifierKernel_support_bound n) u

end
end GinibrePoincare
