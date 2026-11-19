/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCompactTests.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityWeakDerivatives
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! Compactly supported elliptic data allow the actual compact test equation
to be tested against arbitrary smooth functions, hence Schwartz functions. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem ginibreLocalRegularity_exists_compact_cutoff
    (K : Set E) (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] 1 := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : E) := ⟨R+1, R+2, by linarith, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport,?_⟩
  intro x hx
  apply χ.eventuallyEq_one_of_mem_ball
  rw [Metric.mem_ball, dist_zero_right]
  exact (hbound x hx).trans_lt (by dsimp [χ]; linarith)

theorem ginibreLocalRegularity_compact_equation_all_smooth_tests
    {ι : Type*} [Fintype ι] (u h : E → ℂ) (F : ι → E → ℂ) (v : ι → E)
    (hu : HasCompactSupport u) (hh : HasCompactSupport h)
    (hF : ∀ i, HasCompactSupport (F i))
    (heq : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (v i))
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) :
    (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i))) =
      (∫ x, h x*θ x)-∑ i, ∫ x, F i x*fderiv ℝ θ x (v i) := by
  classical
  let K := tsupport u ∪ tsupport h ∪ ⋃ i, tsupport (F i)
  have hK : IsCompact K := (hu.union hh).union (isCompact_iUnion hF)
  obtain ⟨χ, hχ, hχc, hχone⟩ := ginibreLocalRegularity_exists_compact_cutoff K hK
  let ψ : E → ℂ := fun x => (χ x : ℂ)*θ x
  have hψ : ContDiff ℝ ∞ ψ := (Complex.ofRealCLM.contDiff.comp hχ).mul hθ
  have hψc : HasCompactSupport ψ := (hχc.comp_left Complex.ofReal_zero).mul_right
  have hnear (x : E) (hx : x ∈ K) : ψ =ᶠ[𝓝 x] θ := by
    filter_upwards [hχone x hx] with y hy
    simp [ψ, hy]
  have hder (x : E) (hx : x ∈ K) (i : ι) :
      fderiv ℝ ψ x (v i)=fderiv ℝ θ x (v i) := by rw [(hnear x hx).fderiv_eq]
  have hder2 (x : E) (hx : x ∈ K) (i : ι) :
      fderiv ℝ (fun y => fderiv ℝ ψ y (v i)) x (v i)=
        fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i) := by
    have he : (fun y => fderiv ℝ ψ y (v i)) =ᶠ[𝓝 x] (fun y => fderiv ℝ θ y (v i)) := by
      simpa only [Function.comp_def] using (hnear x hx).fderiv.fun_comp (fun L : E →L[ℝ] ℂ => L (v
          i))
    exact congrArg (fun L : E →L[ℝ] ℂ => L (v i)) he.fderiv_eq
  have hleft : (∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ ψ y (v i)) x (v i))) =
      ∫ x, u x*(∑ i, fderiv ℝ (fun y => fderiv ℝ θ y (v i)) x (v i)) := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport u
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hder2 x (Or.inl (Or.inl hx)) i
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hvalue : (∫ x, h x*ψ x) = ∫ x, h x*θ x := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport h
    · rw [(hnear x (Or.inl (Or.inr hx))).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright (i : ι) : (∫ x, F i x*fderiv ℝ ψ x (v i)) =
      ∫ x, F i x*fderiv ℝ θ x (v i) := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport (F i)
    · rw [hder x (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)) i]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have he := heq ψ hψ hψc
  rw [hleft, hvalue] at he
  simpa only [hright] using he

end
end GinibrePoincare
