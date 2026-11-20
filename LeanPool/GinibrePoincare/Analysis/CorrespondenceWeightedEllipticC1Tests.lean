/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticC1Tests.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticConvolution
public import LeanPool.GinibrePoincare.Analysis.WeakDerivativeMollification
public import LeanPool.GinibrePoincare.Analysis.LipschitzMollification
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
/-!
# Correspondence weighted elliptic C 1 tests

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_weak_test_C1`.
-/

@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_pair_toLp (u : Lp ℝ 2 (volume : Measure E))
    (f : E → ℝ) (hf : MemLp f 2 volume) :
    inner ℝ u (hf.toLp f)=∫x, f x*u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, RCLike.inner_apply]

/-- Actual L² weak derivatives can be tested against every compact C¹ test,
proved by simultaneous genuine value-and-derivative mollification. -/
theorem correspondenceWeightedElliptic_weak_test_C1
    (u g : Lp ℝ 2 (volume : Measure E)) (v : E)
    (hw : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
      (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*u x))
    (θ : E→ℝ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫x, θ x*g x)= -(∫x, fderiv ℝ θ x v*u x) := by
  let d : E→ℝ := fun x=>fderiv ℝ θ x v
  have hd : Continuous d := (hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ v
  have hθLp : MemLp θ 2 volume := hθ.continuous.memLp_of_hasCompactSupport hc
  have hdLp : MemLp d 2 volume := hd.memLp_of_hasCompactSupport hdc
  have hweak : ∀ψ : E→ℝ, ContDiff ℝ ∞ ψ→HasCompactSupport ψ→
      (∫x, d x*ψ x)= -(∫x, θ x*fderiv ℝ ψ x v) := by
    intro ψ hψ hψc
    have hDψ : Continuous (fun x=>fderiv ℝ ψ x v) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=(volume : Measure E))
      ((hd.mul hψ.continuous).integrable_of_hasCompactSupport (hdc.mul_right))
      ((hθ.continuous.mul hDψ).integrable_of_hasCompactSupport (hc.mul_right))
      ((hθ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport (hc.mul_right))
      (fun _ _=>hθ.differentiable (by norm_num) _)
      (fun _ _=>hψ.differentiable (by simp) _)
    change (∫x, θ x*fderiv ℝ ψ x v)= -(∫x, d x*ψ x) at hi
    linarith
  let φ := lsiMollifier E
  let A := fun m=>correspondenceWeightedLebesgueSmoothCompactMollification (φ m) θ hθLp hc
  let B := fun m=>correspondenceWeightedLebesgueSmoothCompactMollification (φ m) d hdLp hdc
  have hA := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto φ
    (lsiMollifier_radius_tendsto E) θ hθLp hc
  have hB := correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto φ
    (lsiMollifier_radius_tendsto E) d hdLp hdc
  have hm (m : ℕ) : inner ℝ g (A m)+inner ℝ u (B m)=0 := by
    let θm := (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] θ
    have hsm : ContDiff ℝ ∞ θm := (φ m).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) ((φ m).contDiff_normed (n:=⊤)) (hθLp.locallyIntegrable (by norm_num))
    have hcm : HasCompactSupport θm := (φ m).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc
    have he := hw θm hsm hcm
    have hder := weakDirectionalDerivative_convolution volume θ d ((φ m).normed volume) v
      (hθLp.locallyIntegrable (by norm_num)) ((φ m).contDiff_normed (n:=⊤))
      (φ m).hasCompactSupport_normed hweak
    dsimp only [θm] at he
    simp_rw [hder] at he
    dsimp only [A, B, correspondenceWeightedLebesgueSmoothCompactMollification,
      l2SmoothCompactMollification]
    rw [correspondenceWeightedElliptic_pair_toLp, correspondenceWeightedElliptic_pair_toLp]
    linarith
  have hl : Tendsto (fun m=>inner ℝ g (A m)+inner ℝ u (B m)) atTop
      (𝓝 (inner ℝ g (hθLp.toLp θ)+inner ℝ u (hdLp.toLp d))) :=
    (tendsto_const_nhds.inner hA).add (tendsto_const_nhds.inner hB)
  have he : inner ℝ g (hθLp.toLp θ)+inner ℝ u (hdLp.toLp d)=0 :=
    tendsto_nhds_unique hl (by simpa only [hm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 :
                                 ℝ)) atTop (𝓝 0)))
  rw [correspondenceWeightedElliptic_pair_toLp, correspondenceWeightedElliptic_pair_toLp] at he
  linarith
end
end GinibrePoincare
