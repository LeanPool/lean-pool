/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscMerge
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section2StraightArcChart
import LeanPool.GraphMinor.GM12.Section4ThinStripDisc
import LeanPool.GraphMinor.Surface.ArcDisc
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Empty discs around normal arcs

For the discs used in XII (4.3), page 250, straighten the arc
inside a surface chart and apply the thin-disc construction. A
closed set that meets the arc just at its ends then meets the disc
at exactly those two boundary points.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric

/-- The empty-disc construction of XII (4.3), page 250, for an
arc contained in one ball chart. -/
theorem exists_thin_disc_of_arc_in_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {R : ℝ} {U : Set S} {h : S → ℂ} {g : ℂ → S} (c : BallChart R U h g)
    {a : unitInterval → S} (ha : IsArcMap a) (haU : range a ⊆ U)
    {B : Set S} (hB : IsClosed B) (hleft : a 0 ∈ B) (hright : a 1 ∈ B)
    (hmeet : range a ∩ B ⊆ {a 0, a 1}) :
    ∃ D : Set S, IsClosedDisc D ∧ D ∩ B = {a 0, a 1} ∧
      ({a 0, a 1} : Set S) ⊆ discBd D ∧ range a ⊆ D := by
  obtain ⟨O, K, θ, hO, hKc, hKi, _, hθc, hθm, hθK⟩ :=
    exists_straight_arc_chart hman c ha haU
  exact exists_thin_disc_of_strip_arc hO hKc hKi ha hθc hθm hθK hB hleft hright hmeet

/-- In a closed surface, an arc with no forbidden point between
its ends has a thin disc whose only forbidden points are those ends. -/
theorem exists_thin_disc_of_arc
    {S : Type} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {a : unitInterval → S} (ha : IsArcMap a)
    {B : Set S} (hB : IsClosed B) (hleft : a 0 ∈ B) (hright : a 1 ∈ B)
    (hmeet : range a ∩ B ⊆ {a 0, a 1}) :
    ∃ D : Set S, IsClosedDisc D ∧ D ∩ B = {a 0, a 1} ∧
      ({a 0, a 1} : Set S) ⊆ discBd D ∧ range a ⊆ D := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨E, hE, haE⟩ := Surface.exists_disc_of_arc hS ha
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    refine ⟨c.isOpen_image_ball hman, c.hc.mono ?_, c.gc.mono ball_subset_closedBall,
      ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact c.gm (ball_subset_closedBall hz)
    · rintro _ ⟨z, hz, rfl⟩
      rwa [c.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [c.hg (ball_subset_closedBall hz)]
    · exact fun z hz => c.hg (ball_subset_closedBall hz)
  have haU : range a ⊆ g '' ball 0 1 := by
    rw [← c.discInt_eq]
    exact haE
  exact exists_thin_disc_of_arc_in_chart hman hbc ha haU hB hleft hright hmeet

end GraphMinor.GM12
