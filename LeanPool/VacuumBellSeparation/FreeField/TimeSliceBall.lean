/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroToSpacetime
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroL2
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Reverse time-slice correspondence for the manuscript's open spatial balls

Compact supports contained in the open ball admit one common strictly smaller
radius. The actual construction therefore realizes every such physical
time-zero vector by a real spacetime source in the corresponding double cone.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem exists_spacetimeSource_of_timeZeroSource_ball {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ Metric.ball x₀ R)
    (hg : tsupport u.2.1 ⊆ Metric.ball x₀ R) :
    ∃ F : RealTestFunction, tsupport F.1 ⊆ doubleCone (0, x₀) R ∧
      ∀ p, oneParticle m F p = timeZeroOneParticle m u p := by
  obtain ⟨r, hr, hs⟩ := exists_pos_lt_subset_ball hR
    ((isClosed_tsupport u.1.1).union (isClosed_tsupport u.2.1))
    (Set.union_subset hf hg)
  apply exists_spacetimeSource_of_timeZeroSource_radius_lt hm hr.1.le hr.2 x₀ u
  · exact (Set.subset_union_left.trans hs).trans Metric.ball_subset_closedBall
  · exact (Set.subset_union_right.trans hs).trans Metric.ball_subset_closedBall

theorem oneParticleL2_eq_timeZeroL2_of_eq {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (u : TimeZeroSource)
    (h : ∀ p, oneParticle m F p = timeZeroOneParticle m u p) :
    oneParticleL2 hm F = timeZeroL2 hm u := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_oneParticleL2 hm F, coeFn_timeZeroL2 hm u] with p hpF hpu
  rw [hpF, hpu, h p]

theorem exists_spacetimeSourceL2_of_timeZeroSource_ball {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ Metric.ball x₀ R)
    (hg : tsupport u.2.1 ⊆ Metric.ball x₀ R) :
    ∃ F : RealTestFunction, tsupport F.1 ⊆ doubleCone (0, x₀) R ∧
      oneParticleL2 hm F = timeZeroL2 hm u := by
  obtain ⟨F, hs, heq⟩ := exists_spacetimeSource_of_timeZeroSource_ball hm hR x₀ u hf hg
  exact ⟨F, hs, oneParticleL2_eq_timeZeroL2_of_eq hm F u heq⟩

/-- Pointwise physical representative existence for every compact test pair. -/
theorem exists_spacetimeSource_of_timeZeroSource_any {m : ℝ}
    (hm : 0 < m) (u : TimeZeroSource) :
    ∃ F : RealTestFunction, ∀ p, oneParticle m F p = timeZeroOneParticle m u p := by
  have hs : IsCompact (tsupport u.1.1 ∪ tsupport u.2.1) := u.1.2.2.union u.2.2.2
  obtain ⟨R, hR, hsub⟩ := hs.isBounded.subset_ball_lt 0
    (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨F, _, heq⟩ := exists_spacetimeSource_of_timeZeroSource_ball hm hR 0 u
    (Set.subset_union_left.trans hsub) (Set.subset_union_right.trans hsub)
  exact ⟨F, heq⟩

/-- No spatial localization assumption is needed for existence of some
spacetime representative of an actual compact time-zero test pair. -/
theorem exists_spacetimeSourceL2_of_timeZeroSource {m : ℝ}
    (hm : 0 < m) (u : TimeZeroSource) :
    ∃ F : RealTestFunction, oneParticleL2 hm F = timeZeroL2 hm u := by
  have hs : IsCompact (tsupport u.1.1 ∪ tsupport u.2.1) := u.1.2.2.union u.2.2.2
  obtain ⟨R, hR, hsub⟩ := hs.isBounded.subset_ball_lt 0
    (0 : EuclideanSpace ℝ (Fin 3))
  obtain ⟨F, _, heq⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 u
    (Set.subset_union_left.trans hsub) (Set.subset_union_right.trans hsub)
  exact ⟨F, heq⟩

end VacuumBellSeparation
