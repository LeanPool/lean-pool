/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscsInSurface
import Mathlib.Analysis.Convex.Topology

/-!
# Disc uniqueness when the two discs do not cover the surface

In XII (3.1), page 245, the sphere case is handled by a point outside
the enclosing discs. Two distinct discs with the same boundary would
form a sphere embedded in the original connected surface. Invariance
of domain makes that sphere open and closed, hence onto. The outside
point therefore ensures uniqueness just as nonsphericity does.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric OnePoint Surface

/-- An injective continuous sphere map fills a connected surface.
Invariance of domain gives openness of its compact image. -/
theorem range_sphere_map_eq_univ
    {S : Type*} [TopologicalSpace S] [T2Space S] [PreconnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {T : OnePoint EuclideanPlane → S}
    (hT : Continuous T) (hi : Function.Injective T) : range T = univ := by
  have hopen : IsOpen (range T) := by
    refine isOpen_iff_forall_mem_open.mpr ?_
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : OnePoint EuclideanPlane, q ≠ p := by
      by_cases hp : p = ∞
      · exact ⟨sph 0, hp ▸ sph_ne_infty 0⟩
      · exact ⟨∞, Ne.symm hp⟩
    obtain ⟨H, hH⟩ := exists_homeomorph_onePoint q
    let ρ : ℂ → S := fun z => T (H.symm (sph z))
    have hρc : Continuous ρ :=
      hT.comp (H.symm.continuous.comp isOpenEmbedding_sph.continuous)
    have hρi : InjOn ρ univ := fun z _ w _ he =>
      isOpenEmbedding_sph.injective (H.symm.injective (hi he))
    have hO := isOpen_image_of_manifold isOpen_univ hρc.continuousOn hρi fun _ _ => hman _
    refine ⟨_, ?_, hO, ?_⟩
    · rintro _ ⟨z, -, rfl⟩
      exact ⟨_, rfl⟩
    · rcases eq_infty_or_sph (H p) with h | ⟨z, hz⟩
      · exact absurd (H.injective (h.trans hH.symm)) (Ne.symm hq)
      · exact ⟨z, mem_univ _, by
          change T (H.symm (sph z)) = T p
          rw [← hz, H.symm_apply_apply]⟩
  have hcl : IsClosed (range T) := (isCompact_range hT).isClosed
  exact IsClopen.eq_univ ⟨hcl, hopen⟩ (range_nonempty T)

/-- Two closed discs with the same boundary coincide if their union
does not fill the connected surface. -/
theorem eq_of_discBd_eq_of_union_ne_univ
    {S : Type*} [TopologicalSpace S] [T2Space S] [PreconnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {Δ₁ Δ₂ : Set S}
    (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂)
    (hb : discBd Δ₁ = discBd Δ₂) (hnotcover : Δ₁ ∪ Δ₂ ≠ univ) : Δ₁ = Δ₂ := by
  obtain ⟨h₁', g₁, c₁⟩ := h₁.exists_isChart
  obtain ⟨h₂', g₂, c₂⟩ := h₂.exists_isChart
  obtain ⟨u1, d1⟩ := c₁.union_ball
  obtain ⟨u2, d2⟩ := c₂.union_ball
  have o1 := c₁.isOpen_image_ball hman
  have o2 := c₂.isOpen_image_ball hman
  have p1 : IsPreconnected (g₁ '' ball 0 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g₁ (c₁.gc.mono ball_subset_closedBall)
  have p2 : IsPreconnected (g₂ '' ball 0 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected.image g₂ (c₂.gc.mono ball_subset_closedBall)
  have cl1 : IsClosed (g₁ '' ball 0 1 ∪ discBd Δ₁) := by
    rw [u1]
    exact h₁.isCompact.isClosed
  have cl2 : IsClosed (g₂ '' ball 0 1 ∪ discBd Δ₁) := by
    rw [hb, u2]
    exact h₂.isCompact.isClosed
  by_cases hne : (g₁ '' ball 0 1 ∩ g₂ '' ball 0 1).Nonempty
  · have s1 := subset_of_side p1 o2 cl2 d1 hne
    have s2 := subset_of_side p2 o1 cl1 (hb ▸ d2) (by rwa [inter_comm])
    rw [← u1, ← u2, Subset.antisymm s1 s2, hb]
  · exfalso
    have hm : Δ₁ ∩ Δ₂ = discBd Δ₁ := by
      refine Subset.antisymm ?_ fun x hx => ⟨discBd_subset _ hx, discBd_subset _ (hb ▸ hx)⟩
      rintro x ⟨hx1, hx2⟩
      rw [← u1] at hx1
      rw [← u2] at hx2
      rcases hx1 with h1 | h1
      · rcases hx2 with h2 | h2
        · exact absurd ⟨x, h1, h2⟩ hne
        · exact hb ▸ h2
      · exact h1
    obtain ⟨T, hT, hi, hcov⟩ := exists_sphere_map h₁ h₂ hb hm
    exact hnotcover (hcov.symm.trans (range_sphere_map_eq_univ hman hT hi))

end GraphMinor.GM12
