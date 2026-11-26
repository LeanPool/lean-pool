/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.Cap

/-!
# Extending the boundary map used in XII (7.2)

A continuous bijection between the boundaries of two closed discs extends
to a continuous bijection of the discs. In disc coordinates, the boundary
map is a homeomorphism of the unit circle. Schoenflies extends it to the
plane and maps the closed unit disc to itself.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface

universe u v

/-- Extend a prescribed boundary map between closed discs. This supplies the
disc replacement in the merged-region argument of XII (7.2), page 260. -/
theorem exists_disc_boundary_extension
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {D : Set X} {E : Set Y}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (f : X → Y)
    (hf : ContinuousOn f (discBd D)) (hi : InjOn f (discBd D))
    (himage : f '' discBd D = discBd E) :
    ∃ g : X → Y, ContinuousOn g D ∧ InjOn g D ∧ g '' D = E ∧
      EqOn g f (discBd D) := by
  classical
  obtain ⟨a, b, c⟩ := hD.exists_isChart
  obtain ⟨a', b', c'⟩ := hE.exists_isChart
  have hb : MapsTo b (sphere 0 1) (discBd D) := fun z hz => c.g_sphere ▸ mem_image_of_mem b hz
  have ha' : MapsTo a' (discBd E) (sphere 0 1) := fun z hz => c'.bd ▸ mem_image_of_mem a' hz
  have hfbd : MapsTo f (discBd D) (discBd E) := fun z hz => himage ▸ mem_image_of_mem f hz
  let F : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1 :=
    fun z => ⟨a' (f (b z)), ha' (hfbd (hb z.2))⟩
  have hFc : Continuous F := by
    refine Continuous.subtype_mk ?_ _
    exact (c'.hc.comp (hf.comp (c.gc.mono sphere_subset_closedBall) hb)
      (fun z hz => Surface.discBd_subset E (hfbd (hb hz)))).comp_continuous
        continuous_subtype_val (fun z => z.2)
  have hFi : Function.Injective F := by
    intro z w hzw
    have h₁ : a' (f (b z)) = a' (f (b w)) := congrArg Subtype.val hzw
    have h₂ : f (b z) = f (b w) := c'.gh.injOn
      (Surface.discBd_subset E (hfbd (hb z.2)))
      (Surface.discBd_subset E (hfbd (hb w.2))) h₁
    have h₃ : b z = b w := hi (hb z.2) (hb w.2) h₂
    exact Subtype.ext (c.hg.injOn (sphere_subset_closedBall z.2) (sphere_subset_closedBall w.2) h₃)
  have hFs : Function.Surjective F := by
    rintro ⟨z, hz⟩
    have hb'z : b' z ∈ discBd E := c'.g_sphere ▸ mem_image_of_mem b' hz
    rw [← himage] at hb'z
    obtain ⟨x, hx, hfx⟩ := hb'z
    have hax : a x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem a hx
    refine ⟨⟨a x, hax⟩, Subtype.ext ?_⟩
    change a' (f (b (a x))) = z
    rw [c.gh (Surface.discBd_subset D hx), hfx, c'.hg (sphere_subset_closedBall hz)]
  let e : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
    hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩)
  obtain ⟨p, q, m, hp⟩ := exists_bdMatch e
  obtain ⟨G, hGbd, hGball⟩ := exists_plane_homeomorph oArc_sphere oArc_sphere m
  rw [closedInner_sphere] at hGball
  have hGmem : MapsTo G (closedBall 0 1) (closedBall 0 1) :=
    fun z hz => hGball ▸ mem_image_of_mem G hz
  let g : X → Y := fun x => b' (G (a x))
  refine ⟨g, c'.gc.comp (G.continuous.continuousOn.comp c.hc (fun _ _ => mem_univ _))
    (fun x hx => hGmem (c.hm hx)), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h₁ : G (a x) = G (a y) := c'.hg.injOn (hGmem (c.hm hx)) (hGmem (c.hm hy)) hxy
    exact c.gh.injOn hx hy (G.injective h₁)
  · change (b' ∘ G ∘ a) '' D = E
    have haD : a '' D = closedBall (0 : ℂ) 1 := by
      rw [← c.g_closedBall, c.h_g Subset.rfl]
    rw [image_comp, image_comp, haD, hGball, c'.g_closedBall]
  · intro x hx
    have hax : a x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem a hx
    have hpx : p (a x) = a' (f x) := by
      have h := hp ⟨a x, hax⟩
      change p (a x) = a' (f (b (a x))) at h
      rwa [c.gh (Surface.discBd_subset D hx)] at h
    change b' (G (a x)) = f x
    rw [hGbd hax, hpx, c'.gh (Surface.discBd_subset E (hfbd hx))]

end GraphMinor.GM12
