/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionFourierSliceDefs
public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionFourierDefs
public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionCutoff
public import LeanPool.VacuumBellSeparation.FreeField.CutoffFourierIntegral

/-!
# Actual Fourier representation of compactly supported distributions

The cutoff evaluation defines a continuous scalar function. Its integral
pairing is proved equal to the existing distributional Fourier transform.
The function is independent of the cutoff and has entire affine slices.
All support hypotheses are actual vanishing of the original distribution on
exterior test functions.
-/

@[expose] public section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform InnerProductSpace Topology

namespace VacuumBellSeparation



theorem continuous_compactDistributionFourier
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ) :
    Continuous (compactDistributionFourier T χ) := by
  obtain ⟨s, L, hL⟩ := temperedDistribution_banach_factorization T
  exact (L.continuous.comp (continuous_schwartzDerivativeMap_cutoffFourierKernel s χ hχ)).congr
    (fun p => hL (cutoffFourierKernel χ p))

/-- Representation of the genuine Fourier transform, in Mathlib's normalized convention. -/
theorem fourier_distribution_eq_integral_compactDistributionFourier
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hT : Distribution.IsVanishingOn T Kᶜ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x ∈ K, (fun y => χ y) =ᶠ[𝓝 x] (fun _ => 1))
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    (𝓕 T) ψ = ∫ p, ψ p * compactDistributionFourier T χ p := by
  rw [TemperedDistribution.fourier_apply, distribution_eq_cutoff_pairing T hT χ hχone]
  exact distribution_cutoffFourier_integral T ψ χ hχ

theorem compactDistributionFourier_independent
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hT : Distribution.IsVanishingOn T Kᶜ)
    (χ₁ χ₂ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hχ₁ : ∀ x ∈ K, (fun y => χ₁ y) =ᶠ[𝓝 x] (fun _ => 1))
    (hχ₂ : ∀ x ∈ K, (fun y => χ₂ y) =ᶠ[𝓝 x] (fun _ => 1)) :
    compactDistributionFourier T χ₁ = compactDistributionFourier T χ₂ := by
  funext p
  unfold compactDistributionFourier
  rw [distribution_eq_cutoff_pairing T hT χ₂ hχ₂ (cutoffFourierKernel χ₁ p),
    distribution_eq_cutoff_pairing T hT χ₁ hχ₁ (cutoffFourierKernel χ₂ p)]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply χ₁.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply χ₂.hasTemperateGrowth, cutoffFourierKernel_apply,
    smul_eq_mul]
  ring

/-- Vanishing of the representing Fourier function implies vanishing of the
actual distribution by the existing Fourier equivalence. -/
theorem distribution_eq_zero_of_compactDistributionFourier_eq_zero
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hT : Distribution.IsVanishingOn T Kᶜ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x ∈ K, (fun y => χ y) =ᶠ[𝓝 x] (fun _ => 1))
    (hz : ∀ p, compactDistributionFourier T χ p = 0) : T = 0 := by
  apply (FourierTransform.fourierCLE ℂ
    (TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)).injective
  simp only [FourierTransform.fourierCLE_apply]
  ext ψ
  rw [fourier_distribution_eq_integral_compactDistributionFourier T hT χ hχ hχone ψ]
  simp [hz]





theorem analyticOnNhd_compactDistributionFourierSlice
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (p a : EuclideanSpace ℝ (Fin 3)) :
    AnalyticOnNhd ℂ (compactDistributionFourierSlice T χ hχ p a) Set.univ := by
  intro z hz
  have h := analyticOnNhd_distribution_spatialSchwartzExponential T (innerSL ℝ a)
    (cutoffFourierKernel χ p) (hasCompactSupport_cutoffFourierKernel χ hχ p)
  exact (h _ (Set.mem_univ _)).comp (by fun_prop)

theorem compactDistributionFourierSlice_ofReal
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hχ : HasCompactSupport χ)
    (p a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    compactDistributionFourierSlice T χ hχ p a (t : ℂ) =
      compactDistributionFourier T χ (p + t • a) := by
  unfold compactDistributionFourierSlice compactDistributionFourier
  congr 1
  ext x
  simp only [spatialSchwartzExponential_apply, cutoffFourierKernel_apply,
    spatialFourierCharacter, Real.fourierChar_apply, innerSL_apply_apply]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [inner_add_left, real_inner_smul_left]
  push_cast
  ring

end VacuumBellSeparation
