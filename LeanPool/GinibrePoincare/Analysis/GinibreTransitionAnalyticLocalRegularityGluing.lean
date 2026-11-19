/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityGluing.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityWeakUniqueness
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Ginibre transition analytic local regularity gluing

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_glue_local_derivatives`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

theorem ginibreLocalRegularity_glue_local_derivatives
    (U : Set E) (hU : IsOpen U) (V : ℕ → Set E)
    (hV : ∀ j, IsOpen (V j)) (hVU : ∀ j, V j ⊆ U) (hmono : Monotone V)
    (hcover : ∀ x ∈ U, ∃ j, x ∈ V j)
    (hcompact : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ j, K ⊆ V j)
    (u : E → ℝ) (v : E) (G : ℕ → E → ℝ)
    (hG : ∀ j, MemLp (G j) 2 (volume : Measure E))
    (hw : ∀ j (θ : E → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ V j →
      (∫ x, θ x*G j x) = -(∫ x, fderiv ℝ θ x v*u x)) :
    ∃ g : E → ℝ, Measurable g ∧
      (∀ K : Set E, IsCompact K → K ⊆ U → MemLp g 2 (volume.restrict K)) ∧
      ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
        (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*u x) := by
  classical
  let R := fun j => (hG j).aestronglyMeasurable.mk (G j)
  have hR (j) : Measurable (R j) := (hG j).aestronglyMeasurable.measurable_mk
  have hRAE : ∀ᵐ x ∂(volume : Measure E), ∀ j, G j x = R j x :=
    ae_all_iff.mpr (fun j => (hG j).aestronglyMeasurable.ae_eq_mk)
  let p := fun j x => x ∈ V j ∨ x ∉ U
  let : ∀ j, DecidablePred (p j) := fun j x => Classical.propDecidable _
  have hp (x) : ∃ j, p j x := by
    by_cases hx : x ∈ U
    · obtain ⟨j, hj⟩ := hcover x hx
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hx⟩
  let g := U.indicator (fun x => R (Nat.find (hp x)) x)
  have hpm (j) : MeasurableSet {x | p j x} := (hV j).measurableSet.union hU.measurableSet.compl
  have hgm : Measurable g := (Measurable.find (p := p) hR hpm hp).indicator hU.measurableSet
  have hpatch (m) : ∀ᵐ x ∂(volume : Measure E), x ∈ V m → g x = G m x := by
    have hpair (j) : ∀ᵐ x ∂(volume : Measure E), j ≤ m → x ∈ V j → G j x = G m x := by
      by_cases hjm : j ≤ m
      · have he := ginibreLocalRegularity_local_weak_derivative_unique (V j) (hV j) u (G j) (G m) v
          (hG j) (hG m) (hw j) (fun θ hθ hc hs => hw m θ hθ hc (hs.trans (hmono hjm)))
        exact he.mono (fun x hx => fun _ => hx)
      · exact ae_of_all volume fun x h => (hjm h).elim
    have hall : ∀ᵐ x ∂(volume : Measure E), ∀ j, j ≤ m → x ∈ V j → G j x = G m x := ae_all_iff.mpr
        hpair
    filter_upwards [hall, hRAE] with x hx hr
    intro hxm
    have hxU : x ∈ U := hVU m hxm
    have hsel : x ∈ V (Nat.find (hp x)) := (Nat.find_spec (hp x)).resolve_right (not_not.mpr hxU)
    have hle : Nat.find (hp x) ≤ m := Nat.find_min' (hp x) (Or.inl hxm)
    change U.indicator (fun y => R (Nat.find (hp y)) y) x = _
    rw [Set.indicator_of_mem hxU]
    exact (hr _).symm.trans (hx _ hle hsel)
  refine ⟨g, hgm,?_,?_⟩
  · intro K hK hs
    obtain ⟨m, hm⟩ := hcompact K hK hs
    apply MemLp.ae_eq (hf_Lp := (hG m).restrict K)
    filter_upwards [ae_restrict_of_ae (hpatch m), ae_restrict_mem hK.measurableSet] with x hx hxm
    exact (hx (hm hxm)).symm
  · intro θ hθ hc hs
    obtain ⟨m, hm⟩ := hcompact (tsupport θ) hc hs
    rw [show (∫ x, θ x*g x) = ∫ x, θ x*G m x by
      apply integral_congr_ae
      filter_upwards [hpatch m] with x hx
      by_cases hxt : x ∈ tsupport θ
      · rw [hx (hm hxt)]
      · simp only [image_eq_zero_of_notMem_tsupport hxt, zero_mul]]
    exact hw m θ hθ hc hm

end
end GinibrePoincare
