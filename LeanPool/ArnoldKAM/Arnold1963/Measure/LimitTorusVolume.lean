/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Measure.CumulativeVolume
public import LeanPool.ArnoldKAM.Arnold1963.Measure.LimitImage
public import LeanPool.ArnoldKAM.Arnold1963.Measure.PhaseVolume
public import LeanPool.ArnoldKAM.Arnold1963.Dynamics.RealOrbits

/-!
Apply compact-image bounds to the KAM limit on the periodic phase quotient. Half-open cells
compute finite-stage volume, while closed cells supply compactness for the uniform limit.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
namespace KamProject.Arnold1963
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem torus_phase_volume {n : ℕ} (G : Set (ComplexSpace n)) :
    volume (realSlice G ×ˢ (univ : Set (RealTorus n))) =
      realVolume G * ENNReal.ofReal (2 * Real.pi) ^ n := by
  change (volume.prod volume) _ = _
  rw [Measure.prod_prod]
  congr 1
  change (Measure.pi fun _ : Fin n => (volume : Measure (AddCircle (2 * Real.pi)))) univ = _
  simp [Measure.pi_univ, AddCircle.measure_univ]

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- The limiting real action domain paired with a closed fundamental angle cell. -/
def retainedClosedCell : Set (RealPhaseCover n) :=
  realSlice (h.limitDomain b) ×ˢ Icc 0 (fun _ => 2 * Real.pi)

theorem retainedClosedCell_compact : IsCompact (h.retainedClosedCell b) :=
  (isCompact_realSlice (h.limit_compact b)).prod isCompact_Icc

theorem retainedCell_subset_closed : h.retainedCell b ⊆ h.retainedClosedCell b := by
  intro x hx
  exact ⟨hx.1, (fun j => (hx.2 j (mem_univ j)).1.le), fun j => (hx.2 j (mem_univ j)).2⟩

theorem realLimitMap_continuous : ContinuousOn (h.realLimitMap b)
    (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealSpace n))) := by
  change ContinuousOn ((realPartPhaseCLM n) ∘ h.limitMap b ∘ (complexifyPhaseCLM n)) _
  apply (realPartPhaseCLM n).continuous.comp_continuousOn
  exact (h.limitMap_continuous b).comp (complexifyPhaseCLM n).continuous.continuousOn
    (fun _ hx => h.commonPhase_subset b ⟨hx.1, complexify_mem_angleStrip _ _⟩)

theorem projected_cumulative_uniform :
    TendstoUniformlyOn (fun s => torusProjection ∘ h.realCumulative b s)
      (torusProjection ∘ h.realLimitMap b) atTop (h.retainedClosedCell b) := by
  have hc := ((h.cumulative_uniform b).comp (@complexifyPhase n)).mono
    (show h.retainedClosedCell b ⊆ complexifyPhase ⁻¹' h.limitPhase b from
      fun _ hx => h.commonPhase_subset b ⟨hx.1, complexify_mem_angleStrip _ _⟩)
  exact torusProjection_lipschitz.uniformContinuous.comp_tendstoUniformlyOn
    ((realPartPhaseCLM n).uniformContinuous.comp_tendstoUniformlyOn hc)

theorem projected_limit_continuous :
    ContinuousOn (torusProjection ∘ h.realLimitMap b) (h.retainedClosedCell b) :=
  continuous_torusProjection.comp_continuousOn ((h.realLimitMap_continuous b).mono
    (fun _ hx => ⟨hx.1, mem_univ _⟩))

theorem projected_limit_image :
    (torusProjection ∘ h.realLimitMap b) '' h.retainedClosedCell b =
      h.torusLimitMap b '' (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n))) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨torusProjection x, ⟨hx.1, mem_univ _⟩, h.torusLimitMap_projection b hx.1⟩
  · rintro ⟨x, hx, rfl⟩
    have hr := torusRepresentative_mem_cell x
    refine ⟨torusRepresentative x, ?_, rfl⟩
    exact h.retainedCell_subset_closed b ⟨hx.1, hr.2⟩

theorem torusLimitMap_image_compact : IsCompact
    (h.torusLimitMap b '' (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))) := by
  rw [← h.projected_limit_image b]
  exact (h.retainedClosedCell_compact b).image_of_continuousOn (h.projected_limit_continuous b)

theorem torusLimitMap_volume_ge :
    realVolume (h.limitDomain b) * ENNReal.ofReal (2 * Real.pi) ^ n ≤
      volume (h.torusLimitMap b ''
        (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))) := by
  let : (volume : Measure (RealPhaseSpace n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [← h.projected_limit_image b]
  have ha : realVolume (h.limitDomain b) * ENNReal.ofReal (2 * Real.pi) ^ n =
      volume (h.retainedCell b) :=
    (realPhaseLebesgue_physicalCell (h.limitDomain b)).symm
  rw [ha]
  apply measure_image_ge_of_uniform_limit (h.retainedClosedCell_compact b)
    (h.projected_limit_continuous b) (h.projected_cumulative_uniform b)
  exact Eventually.of_forall fun s => (h.cumulative_torus_volume b s).symm.le.trans
    (measure_mono (image_mono (h.retainedCell_subset_closed b)))

theorem torusLimitMap_volume_gt :
    ENNReal.ofReal (1 - κ) * volume (realSlice h.domain ×ˢ (univ : Set (RealTorus n))) <
      volume (h.torusLimitMap b ''
        (realSlice (h.limitDomain b) ×ˢ (univ : Set (RealTorus n)))) := by
  have ht := h.limit_physicalCell_volume_gt b
  rw [realPhaseLebesgue_physicalCell, realPhaseLebesgue_physicalCell] at ht
  rw [torus_phase_volume]
  exact ht.trans_le (h.torusLimitMap_volume_ge b)

end Iteration.InitialData
end KamProject.Arnold1963
