/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Sphere
import LeanPool.LiebThirring.Electrostatics.SphereCap
import LeanPool.LiebThirring.Electrostatics.SphereRealMarginal
/-!
# Archimedes' angular marginal

The height coordinate of uniform sphere probability is uniform on `[-1,1]`.

Archimedes' hat-box identity for every Euclidean unit direction.
-/

public section

open MeasureTheory Set Metric WithLp
open scoped ENNReal Pointwise
namespace LiebThirring

/-- The height coordinate of uniform sphere probability is uniform on `[-1,1]`. -/
theorem sphereHeight_uniform :
    unitSphereMeasure.map (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) =
      (ENNReal.ofReal 2)⁻¹ • (volume : Measure ℝ).restrict (Icc (-1) 1) := by
  exact eq_uniform_interval_of_symmetric_positive_tails _ sphereHeight_neg_invariant
    (fun t ht => sphereHeight_Ioi ht)

/-- Archimedes' hat-box identity for every Euclidean unit direction. -/
theorem unitSphereMeasure_inner_uniform (e : Position) (he : ‖e‖ = 1) :
    unitSphereMeasure.map (fun ω : sphere (0 : Position) 1 => inner ℝ (ω : Position) e) =
      (ENNReal.ofReal 2)⁻¹ • (volume : Measure ℝ).restrict (Icc (-1) 1) := by
  let v : Position := EuclideanSpace.single 2 1
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.single, PiLp.norm_single]
  let Q : Position ≃ₗᵢ[ℝ] Position := (Submodule.span ℝ {v - e})ᗮ.reflection
  have hQ : Q v = e := Submodule.reflection_sub (hv.trans he.symm)
  have hm : Measurable (fun ω : sphere (0 : Position) 1 => inner ℝ (ω : Position) e) :=
    (continuous_subtype_val.inner continuous_const).measurable
  have hc : (fun ω : sphere (0 : Position) 1 => inner ℝ (ω : Position) e) ∘ unitSphereRotation Q =
      (fun ω : sphere (0 : Position) 1 => (ω : Position) 2) := by
    funext ω
    change inner ℝ (Q (ω : Position)) e = _
    rw [← hQ, Q.inner_map_map]
    simp only [v, EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul]
  calc
    _ = (unitSphereMeasure.map (unitSphereRotation Q)).map
        (fun ω : sphere (0 : Position) 1 => inner ℝ (ω : Position) e) := by
      rw [map_unitSphereMeasure_rotation]
    _ = _ := by
      rw [Measure.map_map hm (measurable_unitSphereRotation Q), hc, sphereHeight_uniform]
end LiebThirring

end
