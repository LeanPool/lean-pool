/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceComponents
public import LeanPool.VacuumBellSeparation.FreeField.UnweightedMomentumDistribution
public import LeanPool.VacuumBellSeparation.FreeField.DistributionFourierNormalization
public import Mathlib.Analysis.Distribution.Support

/-!
# Actual position distributions of completed local sources

The two component projections are mapped to physical `L²`, the mass-shell
density is removed, and the second component's `iω` is inverted by a genuine
temperate multiplier. The normalized inverse Fourier transform reconstructs
the two original test functions. Continuity of every test pairing then proves
that completed local sources have distributional support in `closure U`.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace VacuumBellSeparation

/-- The literal multiplier recovering `ĝ` from `iω ĝ`. -/
noncomputable def sourceSecondMultiplier (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  -Complex.I * ((dispersion m p)⁻¹ : ℝ)

theorem hasTemperateGrowth_sourceSecondMultiplier {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (sourceSecondMultiplier m) :=
  (Function.HasTemperateGrowth.const _).mul
    (Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_inv_dispersion hm))

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

/-- The first component's actual unweighted momentum distribution. -/
noncomputable def sourceFirstMomentum : SourceHilbert hm U →L[ℝ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  ((unweightedMomentumDistribution hm).restrictScalars ℝ).comp
    ((sourceEmbedding hm U).toContinuousLinearMap.comp (sourceFirst hm U))

/-- The second component's actual unweighted momentum distribution. -/
noncomputable def sourceSecondMomentum : SourceHilbert hm U →L[ℝ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  ((TemperedDistribution.smulLeftCLM ℂ (sourceSecondMultiplier m)).restrictScalars ℝ).comp
    (((unweightedMomentumDistribution hm).restrictScalars ℝ).comp
      ((sourceEmbedding hm U).toContinuousLinearMap.comp (sourceSecond hm U)))

theorem sourceFirstMomentum_coe (u : SourceTestSpace hm U) :
    sourceFirstMomentum hm U (u : SourceHilbert hm U) =
      (spatialFourierSchwartz u.1.1 : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  ext φ
  change unweightedMomentumDistribution hm
    (sourceEmbedding hm U (sourceFirst hm U (u : SourceHilbert hm U))) φ = _
  rw [sourceEmbedding_first_coe, unweightedMomentumDistribution_apply, SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [(ae_oneParticleMeasure_iff hm).mp (coeFn_timeZeroL2 hm (u.1.1, 0))]
    with p hp
  simp only [hp, timeZeroOneParticle, spatialFourier_zero, mul_zero, add_zero,
    spatialFourierSchwartz_apply, smul_eq_mul]

theorem sourceSecondMomentum_coe (u : SourceTestSpace hm U) :
    sourceSecondMomentum hm U (u : SourceHilbert hm U) =
      (spatialFourierSchwartz u.1.2 : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  ext φ
  change unweightedMomentumDistribution hm
    (sourceEmbedding hm U (sourceSecond hm U (u : SourceHilbert hm U)))
      (SchwartzMap.smulLeftCLM ℂ (sourceSecondMultiplier m) φ) = _
  rw [sourceEmbedding_second_coe, unweightedMomentumDistribution_apply, SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [(ae_oneParticleMeasure_iff hm).mp (coeFn_timeZeroL2 hm (0, u.1.2))]
    with p hp
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_sourceSecondMultiplier hm)]
  simp only [hp, timeZeroOneParticle, spatialFourier_zero, zero_add,
    spatialFourierSchwartz_apply, smul_eq_mul, sourceSecondMultiplier, Complex.ofReal_inv]
  have hω : (dispersion m p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hm.trans_le (le_dispersion hm.le p)).ne'
  field_simp [hω]
  linear_combination -φ p * spatialFourier u.1.2 p * Complex.I_sq

/-- The completed first position component, as an actual tempered distribution. -/
noncomputable def sourceFirstDistribution : SourceHilbert hm U →L[ℝ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (sourceInverseFourier.restrictScalars ℝ).comp (sourceFirstMomentum hm U)

/-- The completed second position component, as an actual tempered distribution. -/
noncomputable def sourceSecondDistribution : SourceHilbert hm U →L[ℝ]
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (sourceInverseFourier.restrictScalars ℝ).comp (sourceSecondMomentum hm U)

theorem sourceFirstDistribution_coe (u : SourceTestSpace hm U) :
    sourceFirstDistribution hm U (u : SourceHilbert hm U) =
      (spatialSchwartz u.1.1 : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  change sourceInverseFourier (sourceFirstMomentum hm U (u : SourceHilbert hm U)) = _
  rw [sourceFirstMomentum_coe, sourceInverseFourier_spatialFourier]

theorem sourceSecondDistribution_coe (u : SourceTestSpace hm U) :
    sourceSecondDistribution hm U (u : SourceHilbert hm U) =
      (spatialSchwartz u.1.2 : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  change sourceInverseFourier (sourceSecondMomentum hm U (u : SourceHilbert hm U)) = _
  rw [sourceSecondMomentum_coe, sourceInverseFourier_spatialFourier]

private theorem spatialSchwartz_pairing_eq_zero_of_support (f : SpatialTestFunction)
    (hf : tsupport f.1 ⊆ U)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hφ : tsupport φ ⊆ (closure U)ᶜ) :
    (spatialSchwartz f : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) φ = 0 := by
  rw [SchwartzMap.coe_apply]
  apply integral_eq_zero_of_ae
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : φ x = 0
  · simp [hx]
  · have hxout : x ∉ closure U := hφ (subset_tsupport φ hx)
    have hfx : x ∉ tsupport f.1 := fun h => hxout (subset_closure (hf h))
    simp [spatialSchwartz_apply, image_eq_zero_of_notMem_tsupport hfx]

/-- Continuity propagates vanishing of every exterior test pairing through the actual completion. -/
theorem sourceFirstDistribution_isVanishingOn (u : SourceHilbert hm U) :
    Distribution.IsVanishingOn (sourceFirstDistribution hm U u) (closure U)ᶜ := by
  intro φ hφ
  have hcont : Continuous (fun v : SourceHilbert hm U => sourceFirstDistribution hm U v φ) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
      (sourceFirstDistribution hm U).continuous
  refine UniformSpace.Completion.induction_on u (isClosed_eq hcont continuous_const) ?_
  intro v
  rw [sourceFirstDistribution_coe]
  exact spatialSchwartz_pairing_eq_zero_of_support U v.1.1 v.2.1 φ hφ

theorem sourceSecondDistribution_isVanishingOn (u : SourceHilbert hm U) :
    Distribution.IsVanishingOn (sourceSecondDistribution hm U u) (closure U)ᶜ := by
  intro φ hφ
  have hcont : Continuous (fun v : SourceHilbert hm U => sourceSecondDistribution hm U v φ) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
      (sourceSecondDistribution hm U).continuous
  refine UniformSpace.Completion.induction_on u (isClosed_eq hcont continuous_const) ?_
  intro v
  rw [sourceSecondDistribution_coe]
  exact spatialSchwartz_pairing_eq_zero_of_support U v.1.2 v.2.2 φ hφ

/-- Completion enlarges the support bound to `closure U`, exactly as required. -/
theorem dsupport_sourceFirstDistribution_subset (u : SourceHilbert hm U) :
    Distribution.dsupport (sourceFirstDistribution hm U u) ⊆ closure U := by
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx (closure U)
    (sourceFirstDistribution_isVanishingOn hm U u) isClosed_closure

theorem dsupport_sourceSecondDistribution_subset (u : SourceHilbert hm U) :
    Distribution.dsupport (sourceSecondDistribution hm U u) ⊆ closure U := by
  intro x hx
  exact (Distribution.mem_dsupport_iff x).mp hx (closure U)
    (sourceSecondDistribution_isVanishingOn hm U u) isClosed_closure

/-- Bounded localization gives genuinely compact distributional support. -/
theorem isCompact_dsupport_sourceFirstDistribution (hU : Bornology.IsBounded U)
    (u : SourceHilbert hm U) : IsCompact (Distribution.dsupport (sourceFirstDistribution hm U u)) :=
  hU.isCompact_closure.of_isClosed_subset Distribution.isClosed_dsupport
    (dsupport_sourceFirstDistribution_subset hm U u)

theorem isCompact_dsupport_sourceSecondDistribution (hU : Bornology.IsBounded U)
    (u : SourceHilbert hm U) : IsCompact (Distribution.dsupport
      (sourceSecondDistribution hm U u)) :=
  hU.isCompact_closure.of_isClosed_subset Distribution.isClosed_dsupport
    (dsupport_sourceSecondDistribution_subset hm U u)

end VacuumBellSeparation
