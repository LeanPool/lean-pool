/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimeSliceSquareIntegrability

/-!
# Actual absolute integrability for scalar time-slice pairings

The first factor is an arbitrary vector of the physical mass-shell L²
space. Compact time support and the elementary product-square inequality
give a genuine integrable majorant on the product measure.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Set
open scoped ComplexConjugate

theorem exists_spacetimeEvolvedFourier_timeSupport (m : ℝ) (F : RealTestFunction) :
    ∃ T : ℝ, 0 < T ∧ ∀ t ∉ Icc (-T) T, ∀ p,
      spacetimeEvolvedFourier m F t p = 0 := by
  obtain ⟨T, hT, hs⟩ := (F.2.2.image continuous_fst).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  refine ⟨T, hT, ?_⟩
  intro t ht p
  have hz : spacetimeSpatialSlice F t = 0 := by
    apply Subtype.ext
    funext x
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have h := hs ⟨(t, x), tsupport_spatialSlice_subset F t hx, rfl⟩
    have habs : |t| ≤ T := by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using h
    exact ht (abs_le.mp habs)
  rw [spacetimeEvolvedFourier, spacetimePartialFourier_eq_zero_of_slice_zero F hz, mul_zero]

theorem integrable_spacetimeSlicePairing {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Integrable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
      conj (ψ z.2) * spacetimeEvolvedFourier m F z.1 z.2)
      (volume.prod (oneParticleMeasure m)) := by
  let := oneParticleMeasure_isLocallyFinite hm
  obtain ⟨T, _, hT⟩ := exists_spacetimeEvolvedFourier_timeSupport m F
  have hi : Integrable ((Icc (-T) T).indicator (fun _ : ℝ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const isCompact_Icc.measure_ne_top)
  have hdom := (hi.mul_prod (Lp.memLp ψ).norm.integrable_sq).add
    (integrable_spacetimeEvolvedFourier_sq hm F)
  apply hdom.mono'
  · exact ((Lp.memLp ψ).aestronglyMeasurable.comp_snd.star).mul
      (continuous_spacetimeEvolvedFourier m F).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      dsimp only [Pi.add_apply]
      by_cases ht : z.1 ∈ Icc (-T) T
      · simp only [Set.indicator_of_mem ht, one_mul, norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖ψ z.2‖ - ‖spacetimeEvolvedFourier m F z.1 z.2‖),
          mul_nonneg (norm_nonneg (ψ z.2))
            (norm_nonneg (spacetimeEvolvedFourier m F z.1 z.2))]
      · simp only [Set.indicator_of_notMem ht, hT z.1 ht z.2, mul_zero, norm_zero,
          zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, le_refl]

end VacuumBellSeparation
