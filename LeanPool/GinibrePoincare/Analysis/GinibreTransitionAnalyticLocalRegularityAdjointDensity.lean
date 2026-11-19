/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityAdjointDensity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularity

/-!
# Ginibre transition analytic local regularity adjoint density

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreTransitionAnalytic_compact_adjoint_exists_local_gradient`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_compact_adjoint_density
    (n : ℕ) (hn : 0 < n) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        (∫ z, f z*θ z ∂ginibreMeasure n)) :
    ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(1*u z-f z)*θ z) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  intro θ hθ hc hs
  have hθL : MemLp θ 2 (ginibreMeasure n) := hθ.continuous.memLp_of_hasCompactSupport hc
  have hui : Integrable (fun z => ginibreLebesgueDensityReal n z*(u z*θ z)) volume :=
    (integrable_ginibre_iff_density hn (fun z => u z*θ z)).mp (hu.integrable_mul hθL)
  have hfi : Integrable (fun z => ginibreLebesgueDensityReal n z*(f z*θ z)) volume :=
    (integrable_ginibre_iff_density hn (fun z => f z*θ z)).mp (hf.integrable_mul hθL)
  have he := heq θ hθ hc hs
  simp_rw [integral_ginibreMeasure_eq_density_volume hn] at he
  have hm0 : (ginibreNormalizingMass n).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(ginibreMassEvaluation n hn).1.ne', (ginibreMassEvaluation n
        hn).2.ne⟩
  have he' := congrArg (fun a : ℝ => (ginibreNormalizingMass n).toReal*a) he
  simp only [mul_sub,← mul_assoc, mul_inv_cancel₀ hm0, one_mul] at he'
  have hright : (∫ z, ginibreLebesgueDensityReal n z*(1*u z-f z)*θ z) =
      (∫ z, ginibreLebesgueDensityReal n z*(u z*θ z))-
      (∫ z, ginibreLebesgueDensityReal n z*(f z*θ z)) := by
    calc
      _ = ∫ z, ginibreLebesgueDensityReal n z*(u z*θ z)-ginibreLebesgueDensityReal n z*(f z*θ z) :=
          by
        apply integral_congr_ae
        exact ae_of_all volume fun z => by dsimp only; ring
      _ = _ := integral_sub hui hfi
  simp only [← mul_assoc] at hright
  rw [hright]
  linear_combination -he'

/-- The literal probabilistic adjoint resolvent equation directly supplies
an actual measurable local H¹ gradient. -/
theorem ginibreTransitionAnalytic_compact_adjoint_exists_local_gradient
    (n : ℕ) (hn : 0 < n) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        (∫ z, f z*θ z ∂ginibreMeasure n)) :
    ∃ g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2), Measurable g ∧
      (∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
        MemLp g 2 (volume.restrict K)) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, θ z*g z k) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) :=
  ginibreTransitionAnalytic_weighted_resolvent_exists_local_gradient n hn 1 u f hu hf
    (ginibreLocalRegularity_compact_adjoint_density n hn u f hu hf heq)

end
end GinibrePoincare
