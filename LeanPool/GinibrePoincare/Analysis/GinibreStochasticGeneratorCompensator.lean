/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGeneratorCompensator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGeneratorNormalization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTestCompensator

/-! The genuine local Itô compensator equals the actual paper generator compensator. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreConfigurationTestCompensator_eq_generator {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (X : ℝ≥0 → Ω → Configuration n) (hX : ∀ ω, Continuous (fun t => X t ω))
    (hCF : ∀ t ω, CollisionFree (X t ω))
    (f : Configuration n → ℝ) (U : Set (Configuration n)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hRange : ∀ t ω, X t ω ∈ U) (T : ℝ≥0) (ω : Ω) :
    ginibreConfigurationTestCompensator n α X f
      (fun s ω => ginibreLangevinDrift n α (X s.toNNReal ω)) T ω =
      f (X T ω)-f (X 0 ω)-
        ∫ s in (0 : ℝ)..T, ginibreRealPaperSpeedGenerator n α f (X s.toNNReal ω) := by
  have hx : Continuous (fun s : ℝ => X s.toNNReal ω) := (hX ω).comp continuous_real_toNNReal
  have hb : Continuous (fun s : ℝ => ginibreLangevinDrift n α (X s.toNNReal ω)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact ContinuousAt.comp (f := fun r : ℝ => X r.toNNReal ω) (x := s)
      (ginibreLangevinDrift_contDiffAt n α (X s.toNNReal ω) (hCF _ _)).continuousAt hx.continuousAt
  have hd : Continuous (fun s : ℝ => fderiv ℝ f (X s.toNNReal ω)
      (ginibreLangevinDrift n α (X s.toNNReal ω))) :=
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp_continuous hx
      (fun s => hRange _ _)).clm_apply hb
  have hl : Continuous (fun s : ℝ => configurationLaplacian f (X s.toNNReal ω)) :=
    (itoConfigurationLaplacian_continuousOn f U hU hf).comp_continuous hx (fun s => hRange _ _)
  have he : (fun s : ℝ => ginibreRealPaperSpeedGenerator n α f (X s.toNNReal ω)) =
      fun s => fderiv ℝ f (X s.toNNReal ω) (ginibreLangevinDrift n α (X s.toNNReal ω))+
        (α/(n : ℝ)^2)*configurationLaplacian f (X s.toNNReal ω) :=
    funext (fun s => (ginibreLangevin_fderiv_generator hn α f (X s.toNNReal ω) (hCF _ _)).symm)
  have hc : Continuous (fun s : ℝ => (α/(n : ℝ)^2)*configurationLaplacian f (X s.toNNReal ω)) :=
    continuous_const.mul hl
  rw [he, intervalIntegral.integral_add (hd.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  unfold ginibreConfigurationTestCompensator
  ring
end
end GinibrePoincare
