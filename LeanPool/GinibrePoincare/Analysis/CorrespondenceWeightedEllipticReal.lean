/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticReal.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticDensity
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealTests
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealIndicator
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealDerivative
/-!
# Correspondence weighted elliptic real

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceWeightedElliptic_local_real_derivatives`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeightedElliptic_local_real_derivatives
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (K : Set E) (hKm : MeasurableSet K)
    (u h : E → ℝ) (F : ι → E → ℝ)
    (hu : MemLp u 2 (volume.restrict K)) (hh : MemLp h 2 (volume.restrict K))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict K))
    (η : E → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hK : tsupport η ⊆ K)
    (heq : ∀ θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→tsupport θ⊆K→
      (∫x, u x*(∑i, fderiv ℝ (fun y=>fderiv ℝ θ y (b i)) x (b i)))=
        (∫x, h x*θ x)-∑i,∫x, F i x*fderiv ℝ θ x (b i)) :
    ∃g : ι→E→ℝ, (∀i, MemLp (g i) 2 (volume : Measure E)) ∧
      ∀i (θ : E→ℝ), ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*g i x)= -(∫x, fderiv ℝ θ x (b i)*(η x*u x)) := by
  classical
  let up := K.indicator u
  let hp := K.indicator h
  let Fp := fun i=>K.indicator (F i)
  have hup : MemLp up 2 (volume : Measure E) := (memLp_indicator_iff_restrict
      hKm.nullMeasurableSet).mpr hu
  have hhp : MemLp hp 2 (volume : Measure E) := (memLp_indicator_iff_restrict
      hKm.nullMeasurableSet).mpr hh
  have hFp (i) : MemLp (Fp i) 2 (volume : Measure E) := (memLp_indicator_iff_restrict
      hKm.nullMeasurableSet).mpr (hF i)
  have hei := ginibreLocalRegularity_indicator_real_equation (fun i=>b i) K u h F heq
  have hec := ginibreLocalRegularity_real_tests_complex_equation (fun i=>b i) K up hp Fp
    (hup.locallyIntegrable (by norm_num)) (hhp.locallyIntegrable (by norm_num))
    (fun i=>(hFp i).locallyIntegrable (by norm_num)) hei
  obtain ⟨G, hG⟩ := ginibreLocalRegularity_restricted_elliptic_exists_weak_derivatives b K hKm
    (fun x=>(up x : ℂ)) (fun x=>(hp x : ℂ)) (fun i x=>(Fp i x : ℂ))
    ((hup.ofReal (K:=ℂ)).restrict K) ((hhp.ofReal (K:=ℂ)).restrict K)
    (fun i=>((hFp i).ofReal (K:=ℂ)).restrict K)
    (fun x=>(η x : ℂ)) (Complex.ofRealCLM.contDiff.comp hη)
    (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero η).trans hK) hec
  have hηup (x) : η x*up x=η x*u x := by
    by_cases hx : x∈K
    · simp [up, Set.indicator_of_mem hx]
    · have hz : η x=0 := image_eq_zero_of_notMem_tsupport (fun ht=>hx (hK ht))
      simp [hz]
  have hw : MemLp (fun x=>η x*u x) 2 (volume : Measure E) := by
    have hm := (hη.continuous.memLp_top_of_hasCompactSupport hc volume).fun_mul (r:=2) hup
    simpa only [hηup] using hm
  have hreal (i) : ∃gr : E→ℝ, MemLp gr 2 (volume : Measure E) ∧
      ∀θ : E→ℝ, ContDiff ℝ ∞ θ→HasCompactSupport θ→
        (∫x, θ x*gr x)= -(∫x, fderiv ℝ θ x (b i)*(η x*u x)) := by
    apply ginibreLocalRegularity_complex_weak_derivative_real _ hw (G i) (b i)
    intro θ hθ hθc
    simpa only [← Complex.ofReal_mul, hηup] using hG i θ hθ hθc
  choose g hgm hge using hreal
  exact ⟨g, hgm, hge⟩
end
end GinibrePoincare
