/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityDensityEquation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityDivergence
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff

/-!
# Ginibre transition analytic local regularity density equation

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_density_resolvent_elliptic_equation`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_density_resolvent_elliptic_equation
    (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(ℓ*u z-f z)*θ z)) :
    ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, (ginibreLebesgueDensityReal n z*u z)*(∑ k : Fin n × Fin 2,
        fderiv ℝ (fun y => fderiv ℝ θ y (ginibreCoordinateDirection k)) z
            (ginibreCoordinateDirection k))) =
      (∫ z, ((n : ℝ)*ginibreLebesgueDensityReal n z*(ℓ*u z-f z))*θ z)-
      ∑ k : Fin n × Fin 2, ∫ z, (u z*fderiv ℝ (ginibreLebesgueDensityReal n) z
          (ginibreCoordinateDirection k))*
        fderiv ℝ θ z (ginibreCoordinateDirection k) := by
  classical
  intro θ hθ hc hs
  let ρ := ginibreLebesgueDensityReal n
  let D := fun k z => fderiv ℝ θ z (ginibreCoordinateDirection k)
  let DD := fun k z => fderiv ℝ (D k) z (ginibreCoordinateDirection k)
  let A := fun z => (ρ z*u z)*(∑ k : Fin n × Fin 2, DD k z)
  let C := fun k z => (u z*fderiv ℝ ρ z (ginibreCoordinateDirection k))*D k z
  have hul := ginibre_memLp_locallyIntegrable_collisionFree hn u hu
  have hD (k) : ContDiff ℝ ∞ (D k) := (hθ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDD (k) : ContDiff ℝ ∞ (DD k) := ((hD k).fderiv_right (by simp)).clm_apply contDiff_const
  have hDs (k) : tsupport (D k) ⊆ tsupport θ := tsupport_fderiv_apply_subset ℝ _
  have hDDs (k) : tsupport (DD k) ⊆ tsupport θ := (tsupport_fderiv_apply_subset ℝ _).trans (hDs k)
  have hAi (k) : Integrable (fun z => u z*(ρ z*DD k z)) volume :=
    ginibreLocalRegularity_local_compact_test_integrable _ u _ hul
      ((contDiff_ginibreLebesgueDensityReal n).continuous.mul (hDD k).continuous)
      ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_left
      (tsupport_mul_subset_right.trans ((hDDs k).trans hs))
  have hA : Integrable A volume := by
    have hi := integrable_finsetSum Finset.univ (fun k hk => hAi k)
    apply hi.congr
    exact ae_of_all volume fun z => by
      dsimp only [A]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
  have hCi (k) : Integrable (C k) volume := by
    have hρd : ContDiff ℝ ∞ (fun z => fderiv ℝ ρ z (ginibreCoordinateDirection k)) :=
      ((contDiff_ginibreLebesgueDensityReal n).fderiv_right (by simp)).clm_apply contDiff_const
    have hi := ginibreLocalRegularity_local_compact_test_integrable _ u _ hul
      (hρd.continuous.mul (hD k).continuous) (hc.fderiv_apply ℝ _).mul_left
      (tsupport_mul_subset_right.trans ((hDs k).trans hs))
    apply hi.congr
    exact ae_of_all volume fun z => by dsimp only [C, Pi.mul_apply]; ring
  have hCS : Integrable (fun z => ∑ k : Fin n × Fin 2, C k z) volume :=
    integrable_finsetSum _ (fun k hk => hCi k)
  have hflux : (n : ℝ)*(∫ z, ρ z*u z*ginibrePregenerator n θ z) =
      (∫ z, A z)+∑ k : Fin n × Fin 2, ∫ z, C k z := by
    rw [← integral_const_mul]
    calc
      _ = ∫ z, A z+∑ k : Fin n × Fin 2, C k z := by
        apply integral_congr_ae
        filter_upwards [(volume_absolutelyContinuous_ginibreMeasure n hn).ae_le
            (ginibre_ae_collisionFree n hn)] with z hz
        have hp := congrArg (fun a : ℝ => u z*a) (ginibreLocalRegularity_density_generator_pointwise
            n hn θ hθ z hz)
        dsimp only [A, C, DD, D, ρ]
        rw [mul_add, Finset.mul_sum] at hp
        simp_rw [Finset.mul_sum] at hp ⊢
        convert hp using 1
        · ring
        · congr 1
          · apply Finset.sum_congr rfl
            intro k hk
            ring
          · apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = _ := by rw [integral_add hA hCS, integral_finsetSum _ (fun k hk => hCi k)]
  have he := congrArg (fun a : ℝ => (n : ℝ)*a) (heq θ hθ hc hs)
  change (n : ℝ)*(∫ z, ρ z*u z*ginibrePregenerator n θ z) = _ at he
  rw [hflux,← integral_const_mul] at he
  have hsource : (∫ z, (n : ℝ)*(ginibreLebesgueDensityReal n z*(ℓ*u z-f z)*θ z)) =
      (∫ z, ((n : ℝ)*ginibreLebesgueDensityReal n z*(ℓ*u z-f z))*θ z) := by
    apply integral_congr_ae
    exact ae_of_all volume fun z => by dsimp only; ring
  rw [hsource] at he
  change (∫ z, A z) = _
  linear_combination he

end
end GinibrePoincare
