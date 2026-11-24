/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4StripMotion
import LeanPool.GraphMinor.Surface.ArcDisc
import LeanPool.GraphMinor.Surface.Wedge

/-!
# Ambient motion along an arc

For XII (4.3), claim (7), page 251, straighten an arc in a disc
chart and slide its last endpoint to its first. Taking the strip
inside the complement of a closed forbidden set makes the motion
fix that set pointwise.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- Move one endpoint of an arc to the other while fixing a closed
set disjoint from the arc. -/
theorem exists_endpoint_motion_of_arc
    {S : Type} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {a : unitInterval → S} (ha : IsArcMap a)
    {F : Set S} (hF : IsClosed F) (havoid : Disjoint (range a) F) :
    ∃ e : S ≃ₜ S, e (a 1) = a 0 ∧ ∀ x ∈ F, e x = x := by
  let : CompactSpace S := hS.1
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
  obtain ⟨O, K, θ, hK, hθc, hθm, hθK⟩ :=
    Surface.exists_stripChart hman hbc ha haU
  exact exists_endpoint_motion_of_strip hK hθc hθm hθK hF havoid

end GraphMinor.GM12
