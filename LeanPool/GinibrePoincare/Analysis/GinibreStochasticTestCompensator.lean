/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTestCompensator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousLocalIdentity

/-! The actual local Itô compensator is a continuous process. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The compensated test process
`f (X t) - f (X 0) - ∫₀ᵗ Df(X s) (b s) ds - (α / n²) ∫₀ᵗ Δf(X s) ds`. -/
def ginibreConfigurationTestCompensator {Ω : Type*} (n : ℕ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (f : Configuration n → ℝ)
    (b : ℝ → Ω → Configuration n) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f (X t ω)-f (X 0 ω)-
    (∫ s in (0 : ℝ)..t, fderiv ℝ f (X s.toNNReal ω) (b s ω))-
    (α/(n : ℝ)^2)*(∫ s in (0 : ℝ)..t, configurationLaplacian f (X s.toNNReal ω))

theorem ginibreConfigurationTestCompensator_continuous {Ω : Type*} (n : ℕ) (α : ℝ)
    (X : ℝ≥0 → Ω → Configuration n) (hX : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hKU : K ⊆ U) (hRange : ∀ t ω, X t ω ∈ K)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, Continuous (fun s => b s ω)) (ω : Ω) :
    Continuous (fun t => ginibreConfigurationTestCompensator n α X f b t ω) := by
  have hXU : ∀ t, X t ω ∈ U := fun t => hKU (hRange t ω)
  have hval : Continuous (fun t => f (X t ω)) := hf.continuousOn.comp_continuous (hX ω) hXU
  have hdf : Continuous (fun s : ℝ => fderiv ℝ f (X s.toNNReal ω)) :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp_continuous
      ((hX ω).comp continuous_real_toNNReal) (fun s => hXU _)
  have hd : Continuous (fun s : ℝ => fderiv ℝ f (X s.toNNReal ω) (b s ω)) := hdf.clm_apply (hb ω)
  have hl : Continuous (fun s : ℝ => configurationLaplacian f (X s.toNNReal ω)) :=
    (itoConfigurationLaplacian_continuousOn f U hU hf).comp_continuous
      ((hX ω).comp continuous_real_toNNReal) (fun s => hXU _)
  have hiD := (intervalIntegral.continuous_primitive (μ := volume) (fun a b => hd.intervalIntegrable
      a b) 0).comp
    (continuous_subtype_val : Continuous (fun t : ℝ≥0 => (t : ℝ)))
  have hiL := (intervalIntegral.continuous_primitive (μ := volume) (fun a b => hl.intervalIntegrable
      a b) 0).comp
    (continuous_subtype_val : Continuous (fun t : ℝ≥0 => (t : ℝ)))
  exact ((hval.sub continuous_const).sub hiD).sub (continuous_const.mul hiL)
end
end GinibrePoincare
