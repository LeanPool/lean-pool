/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM12.Section2SectorContraction
import Mathlib.Analysis.Convex.PathConnected

/-!
# A simply-connected patch at a sector vertex

For the entry-edge construction on XII page 243, shrink a closed sector
near its boundary vertex. In disc coordinates, take the open unit disc
with that one boundary point, intersected with a small ball around the
point. It contracts to the boundary point and contains all interior
points of the sector sufficiently near the vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric Surface

/-- Near a boundary point of a closed disc there is a simply-connected
patch that contains the nearby disc interior and no other boundary
point. The whole patch can be kept in a prescribed neighbourhood. -/
theorem exists_simplyConnected_sector_patch_with_puncture {S : Type*} [TopologicalSpace S]
    {D W : Set S} (hD : IsClosedDisc D) {v : S} (hv : v ∈ discBd D)
    (hW : IsOpen W) (hvW : v ∈ W) :
    ∃ N X : Set S, IsOpen N ∧ v ∈ N ∧ v ∈ X ∧ IsSimplyConnectedSet X ∧
      X ⊆ ((D \ discBd D) ∩ W) ∪ {v} ∧ (N ∩ D) \ discBd D ⊆ X ∧
      IsPathConnected (X \ {v}) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hvD : v ∈ D := Surface.discBd_subset D hv
  let q := h v
  have hq : q ∈ closedBall (0 : ℂ) 1 := c.hm hvD
  have hgq : g q = v := c.gh hvD
  have hpre : g ⁻¹' W ∈ 𝓝[closedBall (0 : ℂ) 1] q :=
    (c.gc q hq).preimage_mem_nhdsWithin (hW.mem_nhds (hgq.symm ▸ hvW))
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let A : Set ℂ := insert q (ball (0 : ℂ) 1) ∩ ball q δ
  have hqA : q ∈ A := ⟨mem_insert _ _, mem_ball_self hδ⟩
  have hA : A ⊆ closedBall (0 : ℂ) 1 := by
    intro x hx
    rcases hx.1 with rfl | hx
    · exact hq
    · exact ball_subset_closedBall hx
  have hstar : StarConvex ℝ q A :=
    (starConvex_insert_unitBall hq).inter ((convex_ball q δ) (mem_ball_self hδ))
  have hX : IsSimplyConnectedSet (g '' A) := chart_image_starConvex_isSimplyConnected c hA hstar hqA
  have hpreH : h ⁻¹' ball q δ ∈ 𝓝[D] v :=
    (c.hc v hvD).preimage_mem_nhdsWithin (isOpen_ball.mem_nhds (mem_ball_self hδ))
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpreH
  obtain ⟨N, hNU, hN, hvN⟩ := mem_nhds_iff.mp hU
  refine ⟨N ∩ W, g '' A, hN.inter hW, ⟨hvN, hvW⟩,
    ⟨q, hqA, hgq⟩, hX, ?_, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    by_cases hzq : z = q
    · right
      exact mem_singleton_iff.mpr (hzq ▸ hgq)
    · left
      have hzball : z ∈ ball (0 : ℂ) 1 := hz.1.resolve_left hzq
      refine ⟨⟨c.gm (hA hz), ?_⟩, hδW ⟨hz.2, hA hz⟩⟩
      intro hbd
      have hzbd : z ∈ sphere (0 : ℂ) 1 := by
        have hm : h (g z) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hbd
        rwa [c.hg (hA hz)] at hm
      exact (mem_ball.mp hzball).ne (mem_sphere.mp hzbd)
  · rintro x ⟨⟨⟨hxN, _⟩, hxD⟩, hxBd⟩
    have hxball : h x ∈ ball q δ := hUsub ⟨hNU hxN, hxD⟩
    have hxnot : h x ∉ sphere (0 : ℂ) 1 := by
      intro hsph
      have hm : g (h x) ∈ discBd D := c.g_sphere ▸ mem_image_of_mem g hsph
      exact hxBd (c.gh hxD ▸ hm)
    have hxunit : h x ∈ ball (0 : ℂ) 1 := by
      rw [← closedBall_sdiff_sphere]
      exact ⟨c.hm hxD, hxnot⟩
    exact ⟨h x, ⟨Or.inr hxunit, hxball⟩, c.gh hxD⟩
  · let B : Set ℂ := ball (0 : ℂ) 1 ∩ ball q δ
    have hqcl : q ∈ closure (ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      exact hq
    obtain ⟨z, hzδ, hzunit⟩ := mem_closure_iff.mp hqcl (ball q δ)
      isOpen_ball (mem_ball_self hδ)
    have hB : IsPathConnected B :=
      ((convex_ball (0 : ℂ) 1).inter (convex_ball q δ)).isPathConnected ⟨z, hzunit, hzδ⟩
    have heq : (g '' A) \ {v} = g '' B := by
      ext x
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hzv⟩
        refine ⟨z, ⟨?_, hz.2⟩, rfl⟩
        rcases hz.1 with hzq | hzball
        · exact (hzv (mem_singleton_iff.mpr (hzq ▸ hgq))).elim
        · exact hzball
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨z, ⟨Or.inr hz.1, hz.2⟩, rfl⟩, ?_⟩
        intro hzv
        have hbd : g z ∈ discBd D := mem_singleton_iff.mp hzv ▸ hv
        have hsph : z ∈ sphere (0 : ℂ) 1 := by
          have hm : h (g z) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hbd
          rwa [c.hg (ball_subset_closedBall hz.1)] at hm
        exact (mem_ball.mp hz.1).ne (mem_sphere.mp hsph)
    rw [heq]
    exact hB.image' (c.gc.mono (fun _ hx => ball_subset_closedBall hx.1))

/-- A sector has a simply-connected patch at a boundary vertex containing
all sufficiently near interior points and lying in a prescribed neighbourhood. -/
theorem exists_simplyConnected_sector_patch {S : Type*} [TopologicalSpace S]
    {D W : Set S} (hD : IsClosedDisc D) {v : S} (hv : v ∈ discBd D)
    (hW : IsOpen W) (hvW : v ∈ W) :
    ∃ N X : Set S, IsOpen N ∧ v ∈ N ∧ v ∈ X ∧ IsSimplyConnectedSet X ∧
      X ⊆ ((D \ discBd D) ∩ W) ∪ {v} ∧ (N ∩ D) \ discBd D ⊆ X := by
  obtain ⟨N, X, hN, hvN, hvX, hX, hsub, hnear, _⟩ :=
    exists_simplyConnected_sector_patch_with_puncture hD hv hW hvW
  exact ⟨N, X, hN, hvN, hvX, hX, hsub, hnear⟩

end GraphMinor.GM12
