/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEnergyCompare

/-!
# Continuous weights on compact short-time supports

A continuous scalar weight preserves integrability of data restricted to
the compact support of the short-time cutoff.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Multiplication by a continuous real weight preserves integrability
on a compact measurable set. -/
theorem bu_integrableOn_mul_continuous_compact
    {K : Set ParabolicPoint} (hK : IsCompact K)
    (f g : ParabolicPoint → ℝ)
    (hf : IntegrableOn f K volume)
    (hg : ContinuousOn g K) :
    IntegrableOn (fun z => g z * f z) K volume := by
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hgm : AEStronglyMeasurable g (volume.restrict K) :=
    hg.aestronglyMeasurable_of_isCompact hK hKmeas
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.norm
  have hbound : ∀ᵐ z ∂(volume.restrict K), ‖g z‖ ≤ C := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hC (mem_image_of_mem (fun z => ‖g z‖) hz)
  change Integrable (fun z => g z * f z) (volume.restrict K)
  convert hf.mul_bdd hgm hbound using 1
  funext z
  ring

end ESS
