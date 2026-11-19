/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityRealTests.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityProduct
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ginibre transition analytic local regularity real tests

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_real_tests_complex_equation`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]

omit [MeasureSpace E] [BorelSpace E] in
private theorem derivative_component (L : ℂ →L[ℝ] ℝ) (θ : E → ℂ)
    (hθ : ContDiff ℝ ∞ θ) (v : E) (x : E) :
    fderiv ℝ (fun y => L (θ y)) x v = L (fderiv ℝ θ x v) := by
  have h := L.hasFDerivAt.comp x ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt)
  exact congrArg (fun A => A v) h.fderiv

theorem ginibreLocalRegularity_real_tests_complex_equation
    {ι : Type*} [Fintype ι] (v : ι → E) (U : Set E)
    (u h : E → ℝ) (F : ι → E → ℝ)
    (hu : LocallyIntegrable u (volume : Measure E)) (hh : LocallyIntegrable h volume)
    (hF : ∀ i, LocallyIntegrable (F i) volume)
    (heq : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (v i)) :
    ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, (u x : ℂ)*ginibreLocalRegularityLaplacian v θ x) =
        (∫ x, (h x : ℂ)*θ x)-∑ i, ∫ x, (F i x : ℂ)*ginibreLocalRegularityDirectional (v i) θ x := by
  classical
  intro θ hθ hc hs
  have hL := ginibreLocalRegularityLaplacian_smooth v θ hθ
  have hLc := ginibreLocalRegularityLaplacian_compact v θ hc
  have hD (i) := ginibreLocalRegularityDirectional_smooth θ hθ (v i)
  have hDc (i) := ginibreLocalRegularityDirectional_compact θ hc (v i)
  have hi (f : E → ℝ) (hf : LocallyIntegrable f volume) (q : E → ℂ)
      (hq : Continuous q) (hqc : HasCompactSupport q) : Integrable (fun x => (f x : ℂ)*q x) volume
          := by
    have hfc : LocallyIntegrable (fun x => (f x : ℂ)) volume := fun x =>
        Complex.ofRealCLM.integrableAtFilter_comp (hf x)
    simpa only [smul_eq_mul] using hfc.integrable_smul_right_of_hasCompactSupport hq hqc
  have hil := hi u hu _ hL.continuous hLc
  have hih := hi h hh θ hθ.continuous hc
  have hiF (i) := hi (F i) (hF i) _ (hD i).continuous (hDc i)
  have component (L : ℂ →L[ℝ] ℝ) :
      L (∫ x, (u x : ℂ)*ginibreLocalRegularityLaplacian v θ x) =
        L ((∫ x, (h x : ℂ)*θ x)-∑ i, ∫ x, (F i x : ℂ)*ginibreLocalRegularityDirectional (v i) θ x)
            := by
    let q := fun x => L (θ x)
    have hq : ContDiff ℝ ∞ q := L.contDiff.comp hθ
    have hqc : HasCompactSupport q := hc.comp_left (map_zero L)
    have hqs : tsupport q ⊆ U := (tsupport_comp_subset (map_zero L) θ).trans hs
    have hfirst (x) (i) : fderiv ℝ q x (v i) = L (ginibreLocalRegularityDirectional (v i) θ x) :=
      derivative_component L θ hθ (v i) x
    have hsecond (x) (i) : fderiv ℝ (fun y => fderiv ℝ q y (v i)) x (v i) =
        L (ginibreLocalRegularityDirectional (v i) (ginibreLocalRegularityDirectional (v i) θ) x) :=
            by
      simp_rw [hfirst]
      exact derivative_component L _ (hD i) (v i) x
    have he := heq q hq hqc hqs
    have hl := L.integral_comp_comm hil
    have hr := L.integral_comp_comm hih
    have hfi (i) := L.integral_comp_comm (hiF i)
    rw [← hl, map_sub, map_sum,← hr]
    simp_rw [← hfi]
    convert he using 1
    · apply integral_congr_ae
      exact ae_of_all volume fun x => by
        dsimp only
        rw [show (u x : ℂ)*ginibreLocalRegularityLaplacian v θ x = u x •
            ginibreLocalRegularityLaplacian v θ x by simp]
        rw [map_smul]
        simp only [ginibreLocalRegularityLaplacian, map_sum, hsecond, smul_eq_mul]
    · congr 1
      · apply integral_congr_ae
        exact ae_of_all volume fun x => by
          dsimp only
          rw [show (h x : ℂ)*θ x=h x • θ x by simp, map_smul]
          rfl
      · apply Finset.sum_congr rfl
        intro i hi
        apply integral_congr_ae
        exact ae_of_all volume fun x => by
          dsimp only
          rw [hfirst]
          rw [show (F i x : ℂ)*ginibreLocalRegularityDirectional (v i) θ x=F i x •
              ginibreLocalRegularityDirectional (v i) θ x by simp, map_smul]
          rfl
  apply Complex.ext
  · exact component Complex.reCLM
  · exact component Complex.imCLM

end
end GinibrePoincare
