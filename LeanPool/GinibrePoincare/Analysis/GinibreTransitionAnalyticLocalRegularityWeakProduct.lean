/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityWeakProduct.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealDerivative

/-!
# Ginibre transition analytic local regularity weak product

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_scalar_weak_product`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

theorem ginibreLocalRegularity_scalar_weak_product
    (u g q : E → ℝ) (hu : MemLp u 2 (volume : Measure E)) (hg : MemLp g 2 volume)
    (v : E) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (hw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*u x)) :
    MemLp (fun x => q x*g x+u x*fderiv ℝ q x v) 2 volume ∧
    ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*(q x*g x+u x*fderiv ℝ q x v)) = -(∫ x, fderiv ℝ θ x v*(q x*u x)) := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ q x v) := (hq.fderiv_right (by simp)).clm_apply
      contDiff_const
  have hdc := hqc.fderiv_apply ℝ v
  have hgq : MemLp (fun x => q x*g x) 2 volume := (hq.continuous.memLp_top_of_hasCompactSupport hqc
      volume).fun_mul (r := 2) hg
  have hud : MemLp (fun x => u x*fderiv ℝ q x v) 2 volume := by
    have hi := (hd.continuous.memLp_top_of_hasCompactSupport hdc volume).fun_mul (r := 2) hu
    apply MemLp.ae_eq (hf_Lp := hi)
    exact ae_of_all volume fun x => by dsimp only; exact mul_comm _ _
  refine ⟨hgq.add hud,?_⟩
  intro θ hθ hc
  have he := hw (q*θ) (hq.mul hθ) hqc.mul_right
  have hD (x) : fderiv ℝ (q*θ) x v = q x*fderiv ℝ θ x v+θ x*fderiv ℝ q x v := by
    rw [fderiv_mul (hq.differentiable (by simp) x) (hθ.differentiable (by simp) x)]
    simp only [smul_apply, add_apply, smul_eq_mul]
  have hi (f : E → ℝ) (hf : MemLp f 2 volume) (a : E → ℝ) (ha : Continuous a) (hac :
      HasCompactSupport a) :
      Integrable (fun x => a x*f x) volume := by
    have hh := hf.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport ha
        hac
    apply hh.congr
    exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
  have h1 := hi g hg (q*θ) (hq.continuous.mul hθ.continuous) hqc.mul_right
  have h2 := hi u hu (fun x => θ x*fderiv ℝ q x v) (hθ.continuous.mul hd.continuous) hc.mul_right
  have hdt : ContDiff ℝ ∞ (fun x => fderiv ℝ θ x v) := (hθ.fderiv_right (by simp)).clm_apply
      contDiff_const
  have h3 := hi u hu (fun x => q x*fderiv ℝ θ x v) (hq.continuous.mul hdt.continuous) hqc.mul_right
  have hleft : (∫ x, θ x*(q x*g x+u x*fderiv ℝ q x v)) =
      (∫ x, (q*θ) x*g x)+(∫ x, θ x*fderiv ℝ q x v*u x) := by
    calc
      _ = ∫ x, (q*θ) x*g x+θ x*fderiv ℝ q x v*u x := by
        apply integral_congr_ae
        exact ae_of_all volume fun x => by dsimp only [Pi.mul_apply]; ring
      _ = _ := integral_add h1 h2
  have hright : (∫ x, fderiv ℝ (q*θ) x v*u x) =
      (∫ x, q x*fderiv ℝ θ x v*u x)+(∫ x, θ x*fderiv ℝ q x v*u x) := by
    simp_rw [hD, add_mul]
    exact integral_add h3 h2
  rw [hright] at he
  rw [hleft]
  have hr : (∫ x, fderiv ℝ θ x v*(q x*u x)) = ∫ x, q x*fderiv ℝ θ x v*u x := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => by dsimp only; ring
  rw [hr]
  linear_combination he

end
end GinibrePoincare
