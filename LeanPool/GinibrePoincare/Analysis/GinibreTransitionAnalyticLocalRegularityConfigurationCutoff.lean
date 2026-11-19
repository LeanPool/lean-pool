/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityConfigurationCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRestrictedData
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealIndicator
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateWeak
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityRealDerivative

/-!
# Ginibre transition analytic local regularity configuration cutoff

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_configuration_cutoff_exists_weak_derivatives`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_configuration_cutoff_exists_weak_derivatives
    (n : ℕ) (K : Set (Configuration n)) (hKm : MeasurableSet K)
    (u h : Configuration n → ℝ) (F : (Fin n × Fin 2) → Configuration n → ℝ)
    (hu : MemLp u 2 (volume.restrict K)) (hh : MemLp h 2 (volume.restrict K))
    (hF : ∀ k, MemLp (F k) 2 (volume.restrict K))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hK : tsupport η ⊆ K)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ K →
      (∫ z, u z*(∑ k : Fin n × Fin 2,
        fderiv ℝ (fun y => fderiv ℝ θ y (ginibreCoordinateDirection k)) z
            (ginibreCoordinateDirection k))) =
        (∫ z, h z*θ z)-∑ k, ∫ z, F k z*fderiv ℝ θ z (ginibreCoordinateDirection k)) :
    ∃ g : (Fin n × Fin 2) → Configuration n → ℝ,
      (∀ k, MemLp (g k) 2 (volume : Measure (Configuration n))) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ z, θ z*g k z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*(η z*u z)) := by
  classical
  let e := configurationEuclideanEquiv n
  let b := EuclideanSpace.basisFun (Fin n × Fin 2) ℝ
  let up := K.indicator u
  let hp := K.indicator h
  let Fp := fun k => K.indicator (F k)
  have hup : MemLp up 2 (volume : Measure (Configuration n)) := (memLp_indicator_iff_restrict
      hKm.nullMeasurableSet).mpr hu
  have hhp : MemLp hp 2 (volume : Measure (Configuration n)) := (memLp_indicator_iff_restrict
      hKm.nullMeasurableSet).mpr hh
  have hFp (k) : MemLp (Fp k) 2 (volume : Measure (Configuration n)) :=
      (memLp_indicator_iff_restrict hKm.nullMeasurableSet).mpr (hF k)
  have heind := ginibreLocalRegularity_indicator_real_equation (fun k => ginibreCoordinateDirection
      k) K u h F heq
  have hec := ginibreLocalRegularity_real_tests_complex_equation (fun k =>
      ginibreCoordinateDirection k) K up hp Fp
    (hup.locallyIntegrable (by norm_num)) (hhp.locallyIntegrable (by norm_num))
    (fun k => (hFp k).locallyIntegrable (by norm_num)) heind
  have heb : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ K →
      (∫ z, (up z : ℂ)*ginibreLocalRegularityLaplacian (fun k => e.symm (b k)) θ z) =
        (∫ z, (hp z : ℂ)*θ z)-∑ k, ∫ z, (Fp k z : ℂ)*ginibreLocalRegularityDirectional (e.symm (b
            k)) θ z := by
    simpa only [e, b, ginibreLocalRegularity_coordinate_basis] using hec
  have heE := ginibreLocalRegularity_coordinate_elliptic_equation n (fun k => b k) K
    (fun z => (up z : ℂ)) (fun z => (hp z : ℂ)) (fun k z => (Fp k z : ℂ)) heb
  let ηE := fun x => (η (e.symm x) : ℂ)
  have hηE : ContDiff ℝ ∞ ηE := Complex.ofRealCLM.contDiff.comp (hη.comp e.symm.contDiff)
  have hηEc : HasCompactSupport ηE := (hc.comp_homeomorph e.symm.toHomeomorph).comp_left
      Complex.ofReal_zero
  have hηEs : tsupport ηE ⊆ e '' K := by
    intro x hx
    have hxx : x ∈ tsupport (η ∘ e.symm) := (tsupport_comp_subset Complex.ofReal_zero (η ∘ e.symm))
        hx
    have hy : e.symm x ∈ tsupport η := (Set.ext_iff.mp (tsupport_comp_eq_preimage η
        e.symm.toHomeomorph) x).mp hxx
    exact ⟨e.symm x, hK hy, e.apply_symm_apply x⟩
  have hEm : MeasurableSet (e '' K) := e.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hKm
  obtain ⟨G, hG⟩ := ginibreLocalRegularity_restricted_elliptic_exists_weak_derivatives b (e '' K)
      hEm
    (fun x => (up (e.symm x) : ℂ)) (fun x => (hp (e.symm x) : ℂ)) (fun k x => (Fp k (e.symm x) : ℂ))
    (ginibreLocalRegularity_coordinate_restricted_memLp n K _ ((hup.ofReal (K := ℂ)).restrict K))
    (ginibreLocalRegularity_coordinate_restricted_memLp n K _ ((hhp.ofReal (K := ℂ)).restrict K))
    (fun k => ginibreLocalRegularity_coordinate_restricted_memLp n K _ (((hFp k).ofReal (K :=
        ℂ)).restrict K))
    ηE hηE hηEc hηEs heE
  have hηup (z) : η z*up z = η z*u z := by
    by_cases hz : z ∈ K
    · simp [up, Set.indicator_of_mem hz]
    · have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hK ht))
      simp [hηz]
  have hsource (x) : ηE x*(up (e.symm x) : ℂ) = (η (e.symm x)*u (e.symm x) : ℝ) := by
    simpa only [ηE,← Complex.ofReal_mul] using congrArg Complex.ofReal (hηup (e.symm x))
  have hw : MemLp (fun z => η z*u z) 2 (volume : Measure (Configuration n)) := by
    have hi := (hη.continuous.memLp_top_of_hasCompactSupport hc volume).fun_mul (r := 2) hup
    simpa only [hηup] using hi
  have hcomplex (k) := ginibreLocalRegularity_coordinate_weak_derivative n (fun z => (η z*u z : ℝ))
      (G k) k
    (by intro θ hθ hθc; simpa only [hsource] using hG k θ hθ hθc)
  have hreal (k) : ∃ gr : Configuration n → ℝ, MemLp gr 2 (volume : Measure (Configuration n)) ∧
      ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ z, θ z*gr z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*(η z*u z)) := by
    let gg := (hcomplex k).1.toLp (fun z => G k (e z))
    apply ginibreLocalRegularity_complex_weak_derivative_real (fun z => η z*u z) hw gg
        (ginibreCoordinateDirection k)
    intro θ hθ hθc
    rw [show (∫ z, θ z*gg z) = ∫ z, θ z*G k (e z) by
      apply integral_congr_ae
      filter_upwards [(hcomplex k).1.coeFn_toLp] with z hz
      rw [hz]]
    exact (hcomplex k).2 θ hθ hθc
  choose g hgm hge using hreal
  exact ⟨g, hgm, hge⟩

end
end GinibrePoincare
