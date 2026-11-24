/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
import LeanPool.GraphMinor.Surface.Crossing
import LeanPool.GraphMinor.Surface.PlaneSeparation
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A disc interior with a slit ending inside it

The final leaf-edge gluing in XII (7.4), pages 262--263, uses a
disc meeting the old drawing in a slit with one end on its
boundary and one end inside. The slit does not disconnect the
disc interior. In plane coordinates this follows from
Janiszewski: the boundary circle and the slit meet in one point;
neither separates two points of the disc interior off the slit.
Their common complementary component stays inside the disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric

/-- A line meeting the boundary circle in one point does not
disconnect the open ball after it is removed. This is the plane
slit-disc fact used for leaf deletion in XII (7.4). -/
theorem isPreconnected_ball_sdiff_line_of_singleton_boundary
    {c : ℂ} {ρ : ℝ} {L : Set ℂ} {w : ℂ}
    (hL : IsLine L) (hinter : sphere c ρ ∩ L = {w}) :
    IsPreconnected (ball c ρ \ L) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxout : x ∉ sphere c ρ ∪ L := by
    rintro (h | h)
    · exact (ne_of_lt (mem_ball.mp hx.1)) h
    · exact hx.2 h
  have hyout : y ∉ sphere c ρ ∪ L := by
    rintro (h | h)
    · exact (ne_of_lt (mem_ball.mp hy.1)) h
    · exact hy.2 h
  have hsameCircle : y ∈ connectedComponentIn (sphere c ρ)ᶜ x :=
    (convex_ball c ρ).isPreconnected.subset_connectedComponentIn hx.1
      (fun z hz => (ne_of_lt (mem_ball.mp hz))) hy.1
  have hsameLine : y ∈ connectedComponentIn Lᶜ x := by
    obtain ⟨φ⟩ := hL
    rw [component_eq_of_arc φ hx.2 hy.2]
    exact mem_connectedComponentIn hy.2
  have hLc : IsCompact L := by
    obtain ⟨e⟩ := hL
    exact (show IsLineWithEnds L (e 0).1 (e 1).1 from ⟨e, rfl, rfl⟩).isCompact
  have hsame := janiszewski (isCompact_sphere c ρ) hLc
    (hinter.symm ▸ isConnected_singleton.isPreconnected) hxout hyout hsameCircle hsameLine
  let C := connectedComponentIn (sphere c ρ ∪ L)ᶜ x
  have hCsub : C ⊆ (sphere c ρ ∪ L)ᶜ := connectedComponentIn_subset _ _
  have hxC : x ∈ C := mem_connectedComponentIn hxout
  have hCball : C ⊆ ball c ρ := by
    apply isPreconnected_connectedComponentIn.subset_left_of_subset_union
      isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_left.mpr fun z hz hzc => hzc (ball_subset_closedBall hz))
      (fun z hz => ?_) ⟨x, hxC, hx.1⟩
    by_cases hzball : z ∈ ball c ρ
    · exact Or.inl hzball
    · refine Or.inr fun hzclosed => ?_
      have hzSphere : z ∈ sphere c ρ := le_antisymm hzclosed (not_lt.mp hzball)
      exact hCsub hz (Or.inl hzSphere)
  exact ⟨C, fun z hz => ⟨hCball hz, fun hzL => hCsub hz (Or.inr hzL)⟩,
    hxC, hsame, isPreconnected_connectedComponentIn⟩

/-- A line contained in a closed disc and meeting its boundary
in just one point does not disconnect the disc interior. This
transfers the plane slit argument through a disc chart. -/
theorem isPreconnected_discInt_sdiff_line_of_singleton_boundary
    {S : Type*} [TopologicalSpace S] {D L : Set S} {u v w : S}
    (hD : IsClosedDisc D) (hL : IsLineWithEnds L u v) (hLD : L ⊆ D)
    (hinter : discBd D ∩ L = {w}) : IsPreconnected (discInt D \ L) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hi : InjOn h D := c.gh.injOn
  have hLine : IsLine (h '' L) := by
    obtain ⟨a, ha, har, _, _⟩ := hL.exists_arc
    have haD : ∀ t, a t ∈ D := fun t => hLD (har ▸ mem_range_self t)
    have hc : Continuous (h ∘ a) := c.hc.comp_continuous ha.1 haD
    have hinj : Function.Injective (h ∘ a) := fun s t hst => ha.2 (hi (haD s) (haD t) hst)
    have hr : range (h ∘ a) = h '' L := by rw [range_comp, har]
    obtain ⟨e, _, _⟩ := (show IsArcMap (h ∘ a) from ⟨hc, hinj⟩).isLineWithEnds
    exact hr ▸ ⟨e⟩
  have hw : w ∈ discBd D ∩ L := hinter.symm ▸ mem_singleton w
  have hInter : sphere (0 : ℂ) 1 ∩ h '' L = {h w} := by
    apply Subset.antisymm
    · rintro z ⟨hzsphere, x, hxL, hxz⟩
      obtain ⟨y, hybd, hyz⟩ := c.bd.symm ▸ hzsphere
      have hyx : y = x := hi (Surface.discBd_subset D hybd) (hLD hxL) (hyz.trans hxz.symm)
      have hxw : x = w := by
        have hh : x ∈ discBd D ∩ L := ⟨hyx ▸ hybd, hxL⟩
        rw [hinter] at hh
        exact hh
      exact hxz.symm.trans (congrArg h hxw)
    · refine singleton_subset_iff.mpr ⟨?_, ⟨w, hw.2, rfl⟩⟩
      rw [← c.bd]
      exact ⟨w, hw.1, rfl⟩
  have hpre := isPreconnected_ball_sdiff_line_of_singleton_boundary hLine hInter
  have heq : g '' (ball (0 : ℂ) 1 \ h '' L) = discInt D \ L := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨c.discInt_eq.symm ▸ ⟨z, hz.1, rfl⟩, ?_⟩
      intro hxL
      exact hz.2 ⟨g z, hxL, c.hg (ball_subset_closedBall hz.1)⟩
    · rintro x ⟨hxD, hxL⟩
      obtain ⟨z, hz, hzx⟩ := c.discInt_eq ▸ hxD
      refine ⟨z, ⟨hz, ?_⟩, hzx⟩
      rintro ⟨y, hyL, hyz⟩
      have hyx : y = x := (c.gh (hLD hyL)).symm.trans
        ((congrArg g hyz).trans hzx)
      exact hxL (hyx ▸ hyL)
  rw [← heq]
  exact hpre.image g (c.gc.mono (sdiff_subset.trans ball_subset_closedBall))

end GraphMinor.GM12
