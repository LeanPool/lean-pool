/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityQuotient
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityGluing
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCompactExhaustion
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Ginibre transition analytic local regularity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreTransitionAnalytic_weighted_resolvent_exists_local_gradient`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Genuine local H¹ regularity of a weighted Ginibre resolvent solution. The
only analytic premise is its literal compact-test adjoint equation. -/
theorem ginibreTransitionAnalytic_weighted_resolvent_exists_local_gradient
    (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(ℓ*u z-f z)*θ z)) :
    ∃ g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2), Measurable g ∧
      (∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
        MemLp g 2 (volume.restrict K)) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, θ z*g z k) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) := by
  classical
  let η := ginibreLocalRegularityExhaustionCutoff n hn
  have hGex (j : ℕ) : ∃ G : (Fin n × Fin 2) → Configuration n → ℝ,
      (∀ k, MemLp (G k) 2 (volume : Measure (Configuration n))) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ z, θ z*G k z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*(η j z*u z)) := by
    obtain ⟨hη, hηc, hηs, hηone⟩ := ginibreLocalRegularityExhaustionCutoff_properties n hn j
    exact ginibreLocalRegularity_weighted_resolvent_cutoff_gradient n hn ℓ u f hu hf heq
      (tsupport (η j)) hηc hηs (η j) hη hηc Set.Subset.rfl
  choose G hGm hGw using hGex
  have hw (j k) (θ : Configuration n → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
      (hs : tsupport θ ⊆ ginibreLocalRegularityOpenSet n j) :
      (∫ z, θ z*G j k z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) := by
    rw [hGw j k θ hθ hc]
    congr 1
    apply integral_congr_ae
    exact ae_of_all volume fun z => by
      dsimp only
      by_cases hz : z ∈ tsupport θ
      · have hηz := ginibreLocalRegularityExhaustionCutoff_one n hn j z
          (ginibreLocalRegularityOpenSet_subset_compact n j (hs hz))
        change fderiv ℝ θ z (ginibreCoordinateDirection k)*(η j z*u z) = _
        change η j z = 1 at hηz
        rw [hηz, one_mul]
      · have hd : fderiv ℝ θ z (ginibreCoordinateDirection k) = 0 :=
          congrArg (fun L => L (ginibreCoordinateDirection k)) (fderiv_of_notMem_tsupport (𝕜 := ℝ)
              hz)
        simp only [hd, zero_mul]
  have hex (k : Fin n × Fin 2) : ∃ gk : Configuration n → ℝ, Measurable gk ∧
      (∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
        MemLp gk 2 (volume.restrict K)) ∧
      ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, θ z*gk z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) := by
    apply ginibreLocalRegularity_glue_local_derivatives {z | CollisionFree z} (isOpen_collisionFree
        n)
      (ginibreLocalRegularityOpenSet n) (ginibreLocalRegularityOpenSet_isOpen n)
      (fun j => (ginibreLocalRegularityOpenSet_subset_compact n j).trans
          (ginibreLocalRegularityCompactSet_subset n j))
      (ginibreLocalRegularityOpenSet_monotone n)
      (fun z hz => by
        have hi : z ∈ ⋃ j, ginibreLocalRegularityOpenSet n j := by
          rw [ginibreLocalRegularityOpenSet_iUnion]; exact hz
        exact Set.mem_iUnion.mp hi)
      (fun K hK hs => ginibreLocalRegularityOpenSet_contains_compact K hK hs)
      u (ginibreCoordinateDirection k) (fun j => G j k) (fun j => hGm j k)
    exact fun j θ hθ hc hs => hw j k θ hθ hc hs
  choose gk hgkm hgkL hgkw using hex
  let g := fun z => WithLp.toLp 2 (fun k => gk k z)
  have hgm : Measurable g := (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval hgkm)
  refine ⟨g, hgm,?_,?_⟩
  · intro K hK hs
    apply memLp_piLp_iff.mpr
    exact fun k => hgkL k K hK hs
  · intro k θ hθ hc hs
    exact hgkw k θ hθ hc hs

end
end GinibrePoincare
