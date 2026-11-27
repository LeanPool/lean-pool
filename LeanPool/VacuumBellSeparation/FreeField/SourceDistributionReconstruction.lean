/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceDistributions

/-!
# Reconstruction from the two completed source distributions

The normalized inverse Fourier map is injective. The second momentum
multiplier is invertible on actual tempered distributions, with temperate
growth proved for both factors. These identities reconstruct the physical
one-particle vector from the two component distributions, hence the completed
real source map into pairs of distributions is injective.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace VacuumBellSeparation

theorem spatialDistributionScale_injective (c : ℝ) (hc : 0 < c) :
    Function.Injective (spatialDistributionScale c hc) := by
  intro T S h
  ext φ
  have he := DFunLike.congr_fun h (spatialSchwartzScale c hc φ)
  have hinv : spatialSchwartzScale c⁻¹ (inv_pos.mpr hc)
      (spatialSchwartzScale c hc φ) = φ := by
    ext x
    simp only [spatialSchwartzScale_apply, smul_inv_smul₀ hc.ne']
  rw [spatialDistributionScale_apply, spatialDistributionScale_apply, hinv] at he
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero 3 hc.ne'))) he

theorem sourceInverseFourier_injective : Function.Injective sourceInverseFourier := by
  intro T S h
  apply spatialDistributionScale_injective (2 * Real.pi) (by positivity)
  have hf := congrArg (fun X : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ => 𝓕 X) h
  simpa only [sourceInverseFourier_apply, FourierTransform.fourier_fourierInv_eq] using hf

/-- The actual inverse multiplier to the second component extraction. -/
noncomputable def sourceSecondInverseMultiplier (m : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ := Complex.I * (dispersion m p : ℂ)

theorem hasTemperateGrowth_sourceSecondInverseMultiplier {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (sourceSecondInverseMultiplier m) :=
  (Function.HasTemperateGrowth.const _).mul
    (Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_dispersion hm))

theorem sourceSecondMultiplier_mul_inverse {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    sourceSecondMultiplier m p * sourceSecondInverseMultiplier m p = 1 := by
  have hω : (dispersion m p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hm.trans_le (le_dispersion hm.le p)).ne'
  simp only [sourceSecondMultiplier, sourceSecondInverseMultiplier, Complex.ofReal_inv]
  calc
    _ = -(Complex.I ^ 2) * ((dispersion m p : ℂ)⁻¹ * (dispersion m p : ℂ)) := by ring
    _ = 1 := by rw [Complex.I_sq, inv_mul_cancel₀ hω]; norm_num

theorem sourceSecondMultiplier_recover {m : ℝ} (hm : 0 < m)
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    TemperedDistribution.smulLeftCLM ℂ (sourceSecondInverseMultiplier m)
      (TemperedDistribution.smulLeftCLM ℂ (sourceSecondMultiplier m) T) = T := by
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_sourceSecondMultiplier hm)
    (hasTemperateGrowth_sourceSecondInverseMultiplier hm)]
  have hprod : sourceSecondMultiplier m * sourceSecondInverseMultiplier m = fun _ => 1 := by
    funext p
    exact sourceSecondMultiplier_mul_inverse hm p
  rw [hprod, TemperedDistribution.smulLeftCLM_const, one_smul]

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- The distributional formula `κ = f̂ + iω ĝ` holds on the actual completed source space. -/
theorem sourceMomentum_reconstruction (u : SourceHilbert hm U) :
    unweightedMomentumDistribution hm (sourceEmbedding hm U u) =
      sourceFirstMomentum hm U u +
        TemperedDistribution.smulLeftCLM ℂ (sourceSecondInverseMultiplier m)
          (sourceSecondMomentum hm U u) := by
  change unweightedMomentumDistribution hm (sourceEmbedding hm U u) =
    unweightedMomentumDistribution hm (sourceEmbedding hm U (sourceFirst hm U u)) +
      TemperedDistribution.smulLeftCLM ℂ (sourceSecondInverseMultiplier m)
        (TemperedDistribution.smulLeftCLM ℂ (sourceSecondMultiplier m)
          (unweightedMomentumDistribution hm (sourceEmbedding hm U (sourceSecond hm U u))))
  rw [sourceSecondMultiplier_recover hm, ← map_add, ← map_add, sourceFirst_add_second]

/-- Vanishing of both actual position distributions forces the completed source to vanish. -/
theorem source_eq_zero_of_distributions_eq_zero (u : SourceHilbert hm U)
    (hf : sourceFirstDistribution hm U u = 0)
    (hg : sourceSecondDistribution hm U u = 0) : u = 0 := by
  have hf' : sourceFirstMomentum hm U u = 0 := by
    apply sourceInverseFourier_injective
    change sourceInverseFourier (sourceFirstMomentum hm U u) = 0 at hf
    simpa only [map_zero] using hf
  have hg' : sourceSecondMomentum hm U u = 0 := by
    apply sourceInverseFourier_injective
    change sourceInverseFourier (sourceSecondMomentum hm U u) = 0 at hg
    simpa only [map_zero] using hg
  have hk : unweightedMomentumDistribution hm (sourceEmbedding hm U u) = 0 := by
    rw [sourceMomentum_reconstruction hm U u, hf', hg', map_zero, add_zero]
  apply (sourceEmbedding hm U).injective
  apply unweightedMomentumDistribution_injective hm
  simpa only [map_zero] using hk

/-- The two actual position distributions faithfully represent the real source completion. -/
theorem sourceDistributions_injective :
    Function.Injective (fun u : SourceHilbert hm U =>
      (sourceFirstDistribution hm U u, sourceSecondDistribution hm U u)) := by
  intro u v h
  apply sub_eq_zero.mp
  apply source_eq_zero_of_distributions_eq_zero hm U (u - v)
  · rw [map_sub, (Prod.mk.inj h).1, sub_self]
  · rw [map_sub, (Prod.mk.inj h).2, sub_self]

end VacuumBellSeparation
