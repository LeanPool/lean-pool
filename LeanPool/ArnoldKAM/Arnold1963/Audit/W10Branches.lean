/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Audit.W10Example

/-!
The good set meets both separated action branches and supplies distinct invariant tori
in each branch. Strict measure bounds and torus continuity establish these witnesses.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace KamProject.Arnold1963.Audit.W10Example
open W9Example
local instance w10BranchesPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- The real phase cylinder over the action ball centered at the specified branch. -/
def branchPhase (a : ℝ) : Set (RealPhaseSpace 1) :=
  closedBall (center a) (1 / 4) ×ˢ (univ : Set (RealTorus 1))

theorem branchPhase_partition : realSlice ambient ×ˢ (univ : Set (RealTorus 1)) =
    branchPhase 1 ∪ branchPhase (-1) := by
  rw [realSlice_ambient, union_prod]
  rfl

theorem branchPhase_disjoint : Disjoint (branchPhase 1) (branchPhase (-1)) := by
  have hd : Disjoint (closedBall (center 1) (1 / 4))
      (closedBall (center (-1)) (1 / 4)) := closedBall_disjoint_closedBall (by
    norm_num [dist_eq_norm, W9Example.center, Pi.sub_def, pi_norm_const])
  exact disjoint_left.mpr (fun _ hx hy => disjoint_left.mp hd hx.1 hy.1)

theorem branchPhase_volume_eq : volume (branchPhase 1) = volume (branchPhase (-1)) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  simp only [branchPhase, Measure.prod_prod,
    Measure.addHaar_closedBall_center]

theorem branchPhase_half_volume :
    ENNReal.ofReal (1 / 2 : ℝ) *
      volume (realSlice ambient ×ˢ (univ : Set (RealTorus 1))) = volume (branchPhase 1) := by
  rw [branchPhase_partition, measure_union branchPhase_disjoint
    (measurableSet_closedBall.prod MeasurableSet.univ), ← branchPhase_volume_eq,
    ← two_mul, ← mul_assoc]
  norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat, one_div]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem actual_good_meets_both_branches :
    (result.goodSet ∩ branchPhase 1).Nonempty ∧
      (result.goodSet ∩ branchPhase (-1)).Nonempty := by
  have hsub : result.goodSet ⊆ branchPhase 1 ∪ branchPhase (-1) := by
    rw [← branchPhase_partition, ← result.partition]
    exact subset_union_left
  have hlarge : volume (branchPhase 1) < volume result.goodSet := by
    rw [← branchPhase_half_volume]
    exact actual_large_measure
  constructor
  · by_contra hn
    have hs : result.goodSet ⊆ branchPhase (-1) := by
      intro z hz
      exact (hsub hz).resolve_left (fun hp => hn ⟨z, hz, hp⟩)
    exact (not_le_of_gt hlarge) (branchPhase_volume_eq ▸ measure_mono hs)
  · by_contra hn
    have hs : result.goodSet ⊆ branchPhase 1 := by
      intro z hz
      exact (hsub hz).resolve_right (fun hp => hn ⟨z, hz, hp⟩)
    exact (not_le_of_gt hlarge) (measure_mono hs)

private theorem branch_coordinate {a : ℝ} {z : RealPhaseSpace 1}
    (hz : z ∈ branchPhase a) : |z.1 0 - a| ≤ (1 / 4 : ℝ) := by
  have hd : ‖z.1 - center a‖ ≤ (1 / 4 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hz.1
  simpa only [Pi.sub_apply, W9Example.center, Real.norm_eq_abs] using
    (norm_le_pi_norm (z.1 - center a) 0).trans hd

theorem actual_torus_in_one_branch {T : Set (RealPhaseSpace 1)} (hT : T ∈ result.tori) :
    T ⊆ branchPhase 1 ∨ T ⊆ branchPhase (-1) := by
  obtain ⟨R⟩ := actual_torus_realization T hT
  have hc : IsPreconnected T := R.embedding_range ▸
    isPreconnected_range R.closedEmbedding.continuous
  have hs : T ⊆ branchPhase 1 ∪ branchPhase (-1) := by
    intro z hz
    rw [← branchPhase_partition, ← result.partition]
    exact Or.inl (result.union_eq ▸ mem_sUnion.mpr ⟨T, hT, hz⟩)
  have hn : ∀ z ∈ T, z.1 0 ≠ 0 := by
    intro z hz he
    rcases hs hz with hp | hm
    · have hh := branch_coordinate hp
      norm_num [he] at hh
    · have hh := branch_coordinate hm
      norm_num [he] at hh
  have hf : Continuous (fun z : RealPhaseSpace 1 => z.1 0) :=
    (continuous_apply 0).comp continuous_fst
  rcases hc.mapsTo_Ioi_or_Iio hf.continuousOn hn with hp | hm
  · left
    intro z hz
    rcases hs hz with h | h
    · exact h
    · have hh := (abs_le.mp (branch_coordinate h)).2
      have hpos := hp hz
      change 0 < z.1 0 at hpos
      linarith
  · right
    intro z hz
    rcases hs hz with h | h
    · have hh := (abs_le.mp (branch_coordinate h)).1
      have hneg := hm hz
      change z.1 0 < 0 at hneg
      linarith
    · exact h

theorem actual_two_branch_tori :
    ∃ Tpos ∈ result.tori, ∃ Tneg ∈ result.tori,
      Tpos.Nonempty ∧ Tneg.Nonempty ∧ Tpos ⊆ branchPhase 1 ∧ Tneg ⊆ branchPhase (-1) ∧
      Tpos ≠ Tneg ∧ Disjoint Tpos Tneg := by
  obtain ⟨⟨z, hz, hzpos⟩, ⟨w, hw, hwneg⟩⟩ := actual_good_meets_both_branches
  rw [result.union_eq] at hz hw
  obtain ⟨Tpos, hTpos, hzT⟩ := mem_sUnion.mp hz
  obtain ⟨Tneg, hTneg, hwT⟩ := mem_sUnion.mp hw
  have hp : Tpos ⊆ branchPhase 1 := (actual_torus_in_one_branch hTpos).resolve_right (by
    intro h
    exact disjoint_left.mp branchPhase_disjoint hzpos (h hzT))
  have hm : Tneg ⊆ branchPhase (-1) := (actual_torus_in_one_branch hTneg).resolve_left (by
    intro h
    exact disjoint_left.mp branchPhase_disjoint (h hwT) hwneg)
  have hd : Disjoint Tpos Tneg := branchPhase_disjoint.mono hp hm
  refine ⟨Tpos, hTpos, Tneg, hTneg, ⟨z, hzT⟩, ⟨w, hwT⟩, hp, hm, ?_, hd⟩
  intro he
  exact disjoint_left.mp hd hzT (he ▸ hzT)

end KamProject.Arnold1963.Audit.W10Example
