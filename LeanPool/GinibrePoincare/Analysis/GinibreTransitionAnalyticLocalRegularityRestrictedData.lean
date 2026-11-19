/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityRestrictedData.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityLocalizedData
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Ginibre transition analytic local regularity restricted data

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_restricted_elliptic_exists_weak_derivatives`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_restricted_elliptic_exists_weak_derivatives
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (U : Set E) (hUm : MeasurableSet U)
    (u h : E → ℂ) (F : ι → E → ℂ)
    (hu : MemLp u 2 ((volume : Measure E).restrict U)) (hh : MemLp h 2 (volume.restrict U))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict U))
    (η : E → ℂ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hU : tsupport η ⊆ U)
    (heq : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, u x*ginibreLocalRegularityLaplacian (fun i => b i) θ x) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*ginibreLocalRegularityDirectional (b i) θ x) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), ∀ i (θ : E → ℂ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g i x) = -(∫ x, fderiv ℝ θ x (b i)*(η x*u x)) := by
  classical
  have hup : MemLp (U.indicator u) 2 (volume : Measure E) := (memLp_indicator_iff_restrict
      hUm.nullMeasurableSet).mpr hu
  have hhp : MemLp (U.indicator h) 2 (volume : Measure E) := (memLp_indicator_iff_restrict
      hUm.nullMeasurableSet).mpr hh
  have hFp (i) : MemLp (U.indicator (F i)) 2 (volume : Measure E) := (memLp_indicator_iff_restrict
      hUm.nullMeasurableSet).mpr (hF i)
  have heqp : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, U.indicator u x*ginibreLocalRegularityLaplacian (fun i => b i) θ x) =
        (∫ x, U.indicator h x*θ x)-∑ i, ∫ x, U.indicator (F i) x*ginibreLocalRegularityDirectional
            (b i) θ x := by
    intro θ hθ hθc hs
    have hd (x) (hx : x ∉ U) (i) : ginibreLocalRegularityDirectional (b i) θ x = 0 := by
      exact congrArg (fun L => L (b i)) (fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun ht => hx (hs ht)))
    have hl (x) (hx : x ∉ U) : ginibreLocalRegularityLaplacian (fun i => b i) θ x = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact congrArg (fun L => L (b i)) (fderiv_of_notMem_tsupport (𝕜 := ℝ)
        (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (b i)) ht))))
    have hθz (x) (hx : x ∉ U) : θ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
    have hi (f q : E → ℂ) (hq : ∀ x, x ∉ U → q x = 0) :
        (∫ x, U.indicator f x*q x) = ∫ x, f x*q x := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => by
        dsimp only
        by_cases hx : x ∈ U
        · simp only [Set.indicator_of_mem hx]
        · simp only [Set.indicator_of_notMem hx, hq x hx, mul_zero]
    rw [hi u _ hl, hi h _ hθz]
    simp_rw [hi (F _) _ (fun x hx => hd x hx _)]
    exact heq θ hθ hθc hs
  obtain ⟨g, hg⟩ := ginibreLocalRegularity_localized_elliptic_exists_weak_derivatives b U
    (U.indicator u) (U.indicator h) (fun i => U.indicator (F i)) hup hhp hFp η hη hc hU heqp
  refine ⟨g,?_⟩
  intro i θ hθ hθc
  rw [hg i θ hθ hθc]
  congr 1
  apply integral_congr_ae
  exact ae_of_all volume fun x => by
    dsimp only
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · have hηz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hU ht))
      simp [hηz]

end
end GinibrePoincare
