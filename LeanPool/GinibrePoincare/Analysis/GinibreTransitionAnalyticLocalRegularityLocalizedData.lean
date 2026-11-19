/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityLocalizedData.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityLocalization
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCompactData

/-!
# Ginibre transition analytic local regularity localized data

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_localized_elliptic_exists_weak_derivatives`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_compact_multiplier_memLp
    (u η : E → ℂ) (hu : MemLp u 2 (volume : Measure E))
    (hη : Continuous η) (hc : HasCompactSupport η) :
    MemLp (fun x => η x*u x) 2 (volume : Measure E) :=
  (hη.memLp_top_of_hasCompactSupport hc volume).fun_mul (r := 2) hu

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem compact_sum {ι : Type*} [Fintype ι] (f : ι → E → ℂ)
    (hf : ∀ i, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i, f i x) := by
  classical
  have hs (s : Finset ι) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | @insert i s hi ih =>
      have he : (fun x => ∑ j ∈ insert i s, f j x) = f i + (fun x => ∑ j ∈ s, f j x) := by
        funext x
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [he]
      exact (hf i).add ih
  exact hs Finset.univ

theorem ginibreLocalRegularity_localized_elliptic_exists_weak_derivatives
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (U : Set E)
    (u h : E → ℂ) (F : ι → E → ℂ)
    (hu : MemLp u 2 (volume : Measure E)) (hh : MemLp h 2 volume)
    (hF : ∀ i, MemLp (F i) 2 volume)
    (η : E → ℂ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hU : tsupport η ⊆ U)
    (heq : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, u x*ginibreLocalRegularityLaplacian (fun i => b i) θ x) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*ginibreLocalRegularityDirectional (b i) θ x) :
    ∃ g : ι → Lp ℂ 2 (volume : Measure E), ∀ i (θ : E → ℂ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g i x) = -(∫ x, fderiv ℝ θ x (b i)*(η x*u x)) := by
  classical
  let d := fun i => ginibreLocalRegularityDirectional (b i) η
  let L := ginibreLocalRegularityLaplacian (fun i => b i) η
  let H := fun x => η x*h x-(∑ i, F i x*d i x)-u x*L x
  let V := fun i x => η x*F i x+2*u x*d i x
  have hd (i) : ContDiff ℝ ∞ (d i) := ginibreLocalRegularityDirectional_smooth η hη (b i)
  have hdc (i) : HasCompactSupport (d i) := ginibreLocalRegularityDirectional_compact η hc (b i)
  have hL : ContDiff ℝ ∞ L := ginibreLocalRegularityLaplacian_smooth _ η hη
  have hLc : HasCompactSupport L := ginibreLocalRegularityLaplacian_compact _ η hc
  have hmul (f q : E → ℂ) (hf : MemLp f 2 volume) (hq : Continuous q) (hqc : HasCompactSupport q) :
      MemLp (fun x => f x*q x) 2 volume := by
    simpa only [mul_comm] using ginibreLocalRegularity_compact_multiplier_memLp f q hf hq hqc
  have hH : MemLp H 2 volume :=
    ((ginibreLocalRegularity_compact_multiplier_memLp h η hh hη.continuous hc).sub
      (memLp_finsetSum _ (fun i hi => hmul (F i) (d i) (hF i) (hd i).continuous (hdc i)))).sub
      (hmul u L hu hL.continuous hLc)
  have hV (i) : MemLp (V i) 2 volume := by
    have hv := (ginibreLocalRegularity_compact_multiplier_memLp (F i) η (hF i) hη.continuous hc).add
      ((hmul u (d i) hu (hd i).continuous (hdc i)).const_mul 2)
    change MemLp (fun x => η x*F i x+2*(u x*d i x)) 2 volume at hv
    have he : V i = (fun x => η x*F i x+2*(u x*d i x)) := by
      funext x
      dsimp [V]
      ring
    rw [he]
    exact hv
  have hHc : HasCompactSupport H := by
    have h1 : HasCompactSupport (fun x => η x*h x) := hc.mul_right
    have h2 : HasCompactSupport (fun x => ∑ i, F i x*d i x) :=
      compact_sum _ (fun i => (hdc i).mul_left)
    have h3 : HasCompactSupport (fun x => u x*L x) := hLc.mul_left
    exact (h1.sub h2).sub h3
  have hVc (i) : HasCompactSupport (V i) := by
    have h1 : HasCompactSupport (fun x => η x*F i x) := hc.mul_right
    have h2 : HasCompactSupport (fun x => (2*u x)*d i x) := (hdc i).mul_left
    exact h1.add h2
  apply ginibreLocalRegularity_compact_elliptic_exists_weak_derivatives b
    (fun x => η x*u x) H V hc.mul_right hHc hVc
    (ginibreLocalRegularity_compact_multiplier_memLp u η hu hη.continuous hc) hH hV
  exact ginibreLocalRegularity_localize_elliptic_equation (fun i => b i) U u h F
    (hu.locallyIntegrable (by norm_num)) (hh.locallyIntegrable (by norm_num))
    (fun i => (hF i).locallyIntegrable (by norm_num)) η hη hc hU heq

end
end GinibrePoincare
