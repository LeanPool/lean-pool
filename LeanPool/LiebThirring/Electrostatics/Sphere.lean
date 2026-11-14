/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Configuration
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Uniform Euclidean spherical shells

Normalized sphere measure and spherical shell charges on `Position`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace LiebThirring

/-- Uniform probability measure on the physical Euclidean unit sphere. -/
@[expose] noncomputable def unitSphereMeasure : Measure (sphere (0 : Position) 1) :=
  ((volume : Measure Position).toSphere univ)⁻¹ • (volume : Measure Position).toSphere

instance instIsProbabilityMeasureUnitSphereMeasure : IsProbabilityMeasure unitSphereMeasure := by
  let : NeZero (volume : Measure Position).toSphere :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereMeasure
  infer_instance

/-- The pushforward of uniform unit-sphere probability by `ω ↦ a + r • ω`. -/
@[expose] noncomputable def shell (a : Position) (r : ℝ) : Measure Position :=
  unitSphereMeasure.map (fun ω : sphere (0 : Position) 1 => a + r • (ω : Position))

theorem measurable_shellMap (a : Position) (r : ℝ) :
    Measurable (fun ω : sphere (0 : Position) 1 => a + r • (ω : Position)) :=
  measurable_const.add (measurable_subtype_coe.const_smul r)

instance instIsProbabilityMeasureShell (a : Position) (r : ℝ) : IsProbabilityMeasure (shell a r) :=
  by
  unfold shell
  infer_instance

theorem ae_shell_norm (a : Position) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ y ∂shell a r, ‖y - a‖ = r := by
  unfold shell
  apply (ae_map_iff (measurable_shellMap a r).aemeasurable
    (show MeasurableSet {y : Position | ‖y - a‖ = r} from
      (isClosed_eq (continuous_norm.comp (continuous_id.sub continuous_const))
        continuous_const).measurableSet)).2
  apply Filter.Eventually.of_forall
  intro ω
  have hω : ‖(ω : Position)‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using ω.property
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hω, mul_one]

/-- The Euclidean unit sphere has area `4π` in Mathlib's cone normalization. -/
theorem sphere_area : (volume : Measure Position).toSphere univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.toSphere_apply_univ]
  simp only [Position, finrank_euclideanSpace_fin, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_natCast]
  norm_num only [Nat.cast_ofNat]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- The restriction of a linear isometry to the unit sphere. -/
@[expose] def unitSphereRotation (Q : Position ≃ₗᵢ[ℝ] Position)
    (ω : sphere (0 : Position) 1) : sphere (0 : Position) 1 :=
  ⟨Q ω, by simpa only [mem_sphere_zero_iff_norm, Q.norm_map] using ω.property⟩

theorem measurable_unitSphereRotation (Q : Position ≃ₗᵢ[ℝ] Position) :
    Measurable (unitSphereRotation Q) :=
  (Q.continuous.measurable.comp measurable_subtype_coe).subtype_mk

theorem map_toSphere_unitSphereRotation (Q : Position ≃ₗᵢ[ℝ] Position) :
    (volume : Measure Position).toSphere.map (unitSphereRotation Q) =
      (volume : Measure Position).toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_unitSphereRotation Q) hs,
    Measure.toSphere_apply' _ (hs.preimage (measurable_unitSphereRotation Q)),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hsector : Ioo (0 : ℝ) 1 • (Subtype.val '' (unitSphereRotation Q ⁻¹' s)) =
      Q ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨t, ht, z, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨t, ht, Q ω, ⟨unitSphereRotation Q ω, hω, rfl⟩, (Q.map_smul t ω).symm⟩
    · rintro ⟨t, ht, z, ⟨ω, hω, rfl⟩, hx⟩
      refine ⟨t, ht, Q.symm ω, ⟨unitSphereRotation Q.symm ω, ?_, rfl⟩, ?_⟩
      · change unitSphereRotation Q (unitSphereRotation Q.symm ω) ∈ s
        have heq : unitSphereRotation Q (unitSphereRotation Q.symm ω) = ω :=
          Subtype.ext (Q.apply_symm_apply ω)
        rw [heq]
        exact hω
      · apply Q.injective
        simpa only [Q.map_smul, Q.apply_symm_apply] using hx
  rw [hsector]
  exact Q.measurePreserving.measure_preimage_emb Q.toHomeomorph.measurableEmbedding _

theorem map_unitSphereMeasure_rotation (Q : Position ≃ₗᵢ[ℝ] Position) :
    unitSphereMeasure.map (unitSphereRotation Q) = unitSphereMeasure := by
  rw [unitSphereMeasure, Measure.map_smul, map_toSphere_unitSphereRotation]
  exact (measurable_unitSphereRotation Q).aemeasurable

end LiebThirring

end
