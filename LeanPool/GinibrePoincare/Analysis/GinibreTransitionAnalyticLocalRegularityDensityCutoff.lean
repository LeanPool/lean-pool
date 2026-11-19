/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityDensityCutoff.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityConfigurationCutoff
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityEquation
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityWeightedData

/-!
# Ginibre transition analytic local regularity density cutoff

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_weighted_resolvent_density_cutoff_gradient`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_weighted_resolvent_density_cutoff_gradient
    (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(ℓ*u z-f z)*θ z))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z})
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηK : tsupport η ⊆
        K) :
    ∃ g : (Fin n × Fin 2) → Configuration n → ℝ,
      (∀ k, MemLp (g k) 2 (volume : Measure (Configuration n))) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ z, θ z*g k z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*
          (η z*(ginibreLebesgueDensityReal n z*u z))) := by
  obtain ⟨hw, hH, hF⟩ := ginibreLocalRegularity_density_resolvent_data_memLp n hn ℓ u f hu hf K hK
      hs
  have hF' (k : Fin n × Fin 2) : MemLp
      (fun z => u z*fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)) 2
          (volume.restrict K) := by
    have he : (fun z => u z*fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection
        k)) =
        (fun z => fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)*u z) :=
            by
      funext z
      ring
    rw [he]
    exact hF _
  apply ginibreLocalRegularity_configuration_cutoff_exists_weak_derivatives n K hK.measurableSet
    (fun z => ginibreLebesgueDensityReal n z*u z)
    (fun z => (n : ℝ)*ginibreLebesgueDensityReal n z*(ℓ*u z-f z))
    (fun k z => u z*fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k))
    hw hH hF' η hη hc hηK
  intro θ hθ hθc hθK
  exact ginibreLocalRegularity_density_resolvent_elliptic_equation n hn ℓ u f hu heq θ hθ hθc
      (hθK.trans hs)

end
end GinibrePoincare
