/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionFourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Continuous functions are separated by the actual Schwartz pairings

Continuity supplies local integrability. The proved fundamental lemma for
compact smooth tests gives almost-everywhere zero, and Lebesgue open positivity
gives everywhere zero. No polynomial growth of the derivatives is required.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace VacuumBellSeparation

theorem continuous_eq_zero_of_schwartz_pairings
    (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : Continuous f)
    (h : ∀ φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ,
      (∫ p, φ p * f p) = 0) : f = 0 := by
  have hae : ∀ᵐ p ∂volume, f p = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
    intro g hg hgc
    have hcompact : HasCompactSupport (fun x => (g x : ℂ)) :=
      hgc.comp_left Complex.ofReal_zero
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hg
    have ht := h (hcompact.toSchwartzMap hsmooth)
    change (∫ x, (g x : ℂ) * f x) = 0 at ht
    simpa only [Complex.real_smul] using ht
  exact MeasureTheory.Measure.eq_of_ae_eq hae hf continuous_const

/-- A distributional multiplier equation between actual compact Fourier
representations becomes the literal pointwise equation. -/
theorem compactDistributionFourier_relation
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (T S : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hT : Distribution.IsVanishingOn T Kᶜ) (hS : Distribution.IsVanishingOn S Kᶜ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x ∈ K, (fun y => χ y) =ᶠ[nhds x] (fun _ => 1))
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (hg : Function.HasTemperateGrowth g)
    (heq : 𝓕 T + TemperedDistribution.smulLeftCLM ℂ g (𝓕 S) = 0) :
    ∀ p, compactDistributionFourier T χ p + g p * compactDistributionFourier S χ p = 0 := by
  have hc : Continuous (fun p => compactDistributionFourier T χ p +
      g p * compactDistributionFourier S χ p) :=
    (continuous_compactDistributionFourier T χ hχ).add
      (hg.1.continuous.mul (continuous_compactDistributionFourier S χ hχ))
  have hz := continuous_eq_zero_of_schwartz_pairings _ hc (fun φ => by
    have hiT := integrable_distribution_cutoffFourierKernel T φ χ hχ
    have hiS := integrable_distribution_cutoffFourierKernel S
      (SchwartzMap.smulLeftCLM ℂ g φ) χ hχ
    have hiS' : Integrable (fun p => φ p * (g p * compactDistributionFourier S χ p)) := by
      convert hiS using 1
      funext p
      rw [SchwartzMap.smulLeftCLM_apply_apply hg]
      change φ p * (g p * S (cutoffFourierKernel χ p)) = (g p * φ p) * S (cutoffFourierKernel χ p)
      ring
    have hp := DFunLike.congr_fun heq φ
    change (𝓕 T) φ + (TemperedDistribution.smulLeftCLM ℂ g (𝓕 S)) φ = 0 at hp
    rw [TemperedDistribution.smulLeftCLM_apply_apply] at hp
    rw [fourier_distribution_eq_integral_compactDistributionFourier T hT χ hχ hχone,
      fourier_distribution_eq_integral_compactDistributionFourier S hS χ hχ hχone] at hp
    calc
      _ = (∫ p, φ p * compactDistributionFourier T χ p) +
          ∫ p, φ p * (g p * compactDistributionFourier S χ p) := by
        simp_rw [mul_add]
        exact integral_add hiT hiS'
      _ = 0 := by
        convert hp using 1
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          dsimp only
          rw [SchwartzMap.smulLeftCLM_apply_apply hg]
          simp only [smul_eq_mul]
          ring)
  exact fun p => congrFun hz p

end VacuumBellSeparation
