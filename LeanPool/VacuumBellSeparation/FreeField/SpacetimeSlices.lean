/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CauchySpatialTest

/-!
# Literal spatial slices and their common double-cone support margin

Each fixed-time slice of a real spacetime test function is itself a genuine
spatial test function. Compact support in an open double cone supplies one
strictly smaller radius for all slices, including their subsequent finite
propagation to time zero.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem tsupport_spatialSlice_subset (F : RealTestFunction) (t : ℝ) :
    tsupport (fun x => F.1 (t, x)) ⊆ (fun x => (t, x)) ⁻¹' tsupport F.1 :=
  tsupport_comp_subset_preimage F.1 (by fun_prop)

theorem hasCompactSupport_spatialSlice (F : RealTestFunction) (t : ℝ) :
    HasCompactSupport (fun x => F.1 (t, x)) := by
  apply (F.2.2.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  exact ⟨(t, x), tsupport_spatialSlice_subset F t hx, rfl⟩

/-- The spatial Schwartz function obtained by fixing the time coordinate of a spacetime test
function. -/
noncomputable def spacetimeSpatialSlice (F : RealTestFunction) (t : ℝ) :
    SpatialTestFunction :=
  ⟨fun x => F.1 (t, x), F.2.1.comp (contDiff_const.prodMk contDiff_id),
    hasCompactSupport_spatialSlice F t⟩

@[simp] theorem spacetimeSpatialSlice_apply (F : RealTestFunction) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : (spacetimeSpatialSlice F t).1 x = F.1 (t, x) := rfl

/-- The same smaller cone controls every actual slice. Adding the center
to the compact set also handles the identically zero source. -/
theorem exists_doubleCone_support_margin {R : ℝ} (hR : 0 < R)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ doubleCone (0, x₀) R) :
    ∃ r : ℝ, 0 ≤ r ∧ r < R ∧
      ∀ y ∈ tsupport F.1, |y.1| + ‖y.2 - x₀‖ ≤ r := by
  let K : Set Spacetime := tsupport F.1 ∪ {(0, x₀)}
  have hK : IsCompact K := F.2.2.union isCompact_singleton
  have hne : K.Nonempty := ⟨(0, x₀), Set.mem_union_right _ rfl⟩
  have hc : Continuous (fun y : Spacetime => |y.1| + ‖y.2 - x₀‖) := by fun_prop
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  refine ⟨|y.1| + ‖y.2 - x₀‖, by positivity, ?_, ?_⟩
  · rcases hy with hy | hy
    · simpa only [doubleCone, Set.mem_ofPred_eq, sub_zero] using hF hy
    · have hy' : y = (0, x₀) := Set.mem_singleton_iff.mp hy
      simpa only [hy', abs_zero, sub_self, norm_zero, add_zero] using hR
  · intro z hz
    exact hmax (Set.mem_union_left _ hz)

theorem tsupport_spacetimeSpatialSlice_subset {r : ℝ}
    (x₀ : EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction)
    (hF : ∀ y ∈ tsupport F.1, |y.1| + ‖y.2 - x₀‖ ≤ r) (t : ℝ) :
    tsupport (spacetimeSpatialSlice F t).1 ⊆ Metric.closedBall x₀ (r - |t|) := by
  intro x hx
  have h := hF (t, x) (tsupport_spatialSlice_subset F t hx)
  change dist x x₀ ≤ r - |t|
  rw [dist_eq_norm]
  linarith

theorem spacetimeSpatialSlice_eq_zero_outside {r : ℝ}
    (x₀ : EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction)
    (hF : ∀ y ∈ tsupport F.1, |y.1| + ‖y.2 - x₀‖ ≤ r)
    {t : ℝ} (ht : r < |t|) : spacetimeSpatialSlice F t = 0 := by
  apply Subtype.ext
  funext x
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have h := tsupport_spacetimeSpatialSlice_subset x₀ F hF t hx
  have hd : dist x x₀ ≤ r - |t| := h
  linarith [(dist_nonneg : 0 ≤ dist x x₀)]

end VacuumBellSeparation
