/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.Schoenflies
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Extending a map of disc boundaries

The capped surfaces used in XII (3.1), page 245, are independent of
which disc is pasted onto a cuff. The local ingredient is that a
homeomorphism of disc boundaries extends to the discs. Disc charts
reduce this to the extension theorem for the unit circle.
-/

public section

namespace GraphMinor.GM12

open Set Metric Topology Surface

private def chartHomeomorph {S : Type*} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) :
    D ≃ₜ closedBall (0 : ℂ) 1 where
  toFun x := ⟨h x.val, c.hm x.property⟩
  invFun z := ⟨g z.val, c.gm z.property⟩
  left_inv x := Subtype.ext (c.gh x.property)
  right_inv z := Subtype.ext (c.hg z.property)
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp c.hc).subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp c.gc).subtype_mk _

private theorem chart_mem_sphere_iff {S : Type*} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) (x : D) :
    x.val ∈ discBd D ↔ h x.val ∈ sphere (0 : ℂ) 1 := by
  constructor
  · intro hx
    rw [← c.bd]
    exact mem_image_of_mem h hx
  · intro hx
    rw [← c.bd] at hx
    obtain ⟨y, hy, he⟩ := hx
    have hyx := c.gh.injOn (discBd_subset D hy) x.property he
    exact hyx ▸ hy

private def chartBoundaryHomeomorph {S : Type*} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) :
    discBd D ≃ₜ sphere (0 : ℂ) 1 where
  toFun x := ⟨h x.val, (chart_mem_sphere_iff c ⟨x.val, discBd_subset D x.property⟩).mp x.property⟩
  invFun z := ⟨g z.val, by rw [← c.g_sphere]; exact mem_image_of_mem g z.property⟩
  left_inv x := Subtype.ext (c.gh (discBd_subset D x.property))
  right_inv z := Subtype.ext (c.hg (sphere_subset_closedBall z.property))
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp (c.hc.mono
    (discBd_subset D))).subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp (c.gc.mono
    sphere_subset_closedBall)).subtype_mk _

/-- A homeomorphism of the boundaries of two closed discs extends to
a homeomorphism of the discs, agreeing at every boundary point. -/
theorem exists_disc_homeomorph_extending_boundary
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {D : Set S} {E : Set T} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (p : discBd D ≃ₜ discBd E) :
    ∃ f : D ≃ₜ E, ∀ x : discBd D,
      (f ⟨x.val, discBd_subset D x.property⟩).val = (p x).val := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨h', g', c'⟩ := hE.exists_isChart
  let b := (chartBoundaryHomeomorph c).symm.trans (p.trans (chartBoundaryHomeomorph c'))
  obtain ⟨h₀, k₀, m, hm⟩ := exists_bdMatch b
  obtain ⟨o⟩ := oArc_sphere
  obtain ⟨H, hH⟩ := exists_homeomorph_closedInner ⟨o⟩ ⟨o⟩ m
  let B : Set ℂ := closedBall 0 1
  let q : B ≃ₜ closedInner (sphere (0 : ℂ) 1) := Homeomorph.setCongr closedInner_sphere.symm
  let f := (chartHomeomorph c).trans (q.trans (H.trans (q.symm.trans (chartHomeomorph c').symm)))
  refine ⟨f, fun x => ?_⟩
  have hx : h x.val ∈ sphere (0 : ℂ) 1 :=
    (chart_mem_sphere_iff c ⟨x.val, discBd_subset D x.property⟩).mp x.property
  have hcoord : (H (q (chartHomeomorph c ⟨x.val, discBd_subset D x.property⟩))).val =
      h' (p x).val := by
    rw [hH _ hx]
    change h₀ (h x.val) = h' (p x).val
    rw [hm ⟨h x.val, hx⟩]
    have heq : (chartBoundaryHomeomorph c).symm ⟨h x.val, hx⟩ = x := by
      apply Subtype.ext
      exact c.gh (discBd_subset D x.property)
    change h' (p ((chartBoundaryHomeomorph c).symm ⟨h x.val, hx⟩)).val = _
    rw [heq]
  change g' (H (q (chartHomeomorph c ⟨x.val, discBd_subset D x.property⟩))).val = _
  rw [hcoord]
  exact c'.gh (discBd_subset E (p x).property)

end GraphMinor.GM12
