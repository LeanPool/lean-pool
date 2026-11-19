/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireRegularity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Gaussian entire regularity

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `gaussian_entire_contDiff_real_one`.
-/

@[expose] public section

open Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Joint continuity and the scalar Weierstrass theorem imply continuity of
every directional complex derivative of a multivariate entire function. -/
theorem gaussian_entire_continuous_directional_fderiv {n : ℕ}
    {f : Configuration n → ℂ} (hf : Differentiable ℂ f) (v : Configuration n) :
    Continuous (fun z => fderiv ℂ f z v) := by
  let F : Configuration n → ℂ → ℂ := fun z t => f (z + t • v)
  have hdiff : ∀ z, Differentiable ℂ (F z) := by
    intro z
    apply hf.comp
    exact (differentiable_const z).add ((differentiable_id).smul_const v)
  have hderiv : ∀ z, deriv (F z) 0 = fderiv ℂ f z v := by
    intro z
    have hc : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    have hff : HasFDerivAt f (fderiv ℂ f z) ((fun t : ℂ => z + t • v) 0) := by
      simpa using (hf z).hasFDerivAt
    exact (hff.comp_hasDerivAt 0 hc).deriv
  apply continuous_iff_continuousAt.mpr
  intro z
  have hloc : TendstoLocallyUniformlyOn F (F z) (𝓝 z) Set.univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
    intro K hKU hK
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    apply Continuous.tendstoUniformly (fun w (t : K) => F w t) _ z
    exact hf.continuous.comp
      (continuous_fst.add (continuous_subtype_val.comp continuous_snd |>.smul continuous_const))
  have hlim := (hloc.deriv (Eventually.of_forall (fun w => (hdiff w).differentiableOn))
    isOpen_univ).tendsto_at (a := (0 : ℂ)) (Set.mem_univ _)
  change Tendsto (fun w => fderiv ℂ f w v) (𝓝 z) (𝓝 (fderiv ℂ f z v))
  simpa only [Function.comp_apply, hderiv] using hlim

/-- Actual multivariate entire functions have continuous Fréchet derivative. -/
theorem gaussian_entire_contDiff_complex_one {n : ℕ}
    {f : Configuration n → ℂ} (hf : Differentiable ℂ f) : ContDiff ℂ 1 f := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨hf, continuous_clm_apply.mpr ?_⟩
  exact fun v => gaussian_entire_continuous_directional_fderiv hf v

theorem gaussian_entire_contDiff_real_one {n : ℕ}
    {f : Configuration n → ℂ} (hf : Differentiable ℂ f) : ContDiff ℝ 1 f :=
  (gaussian_entire_contDiff_complex_one hf).restrict_scalars ℝ

end
end GinibrePoincare
