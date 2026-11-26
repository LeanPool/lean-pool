/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.Surface.DiscUnion
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM14.WhitneyFaces

/-!
# Cutting the source disc with a specified boundary arc

The net exchange of VII (2.6), page 218, cuts along a proper
line. One of its two pieces has as boundary that line and the
selected subarc of the paired side. Extend the selected subarc
to the two boundary arcs of the disc, then cut using those arcs.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Surface

/-- Complete a parametrized boundary arc of a closed disc to its
other boundary arc, keeping both ends. This fixes the side of
the cut used in VII (2.6), page 218. -/
theorem exists_complementary_disc_boundary_arc
    {S : Type*} [TopologicalSpace S] {D : Set S} (hD : IsClosedDisc D)
    (f : unitInterval → S) (hf : IsArcMap f) (hfbd : range f ⊆ discBd D) :
    ∃ g : unitInterval → S, IsArcMap g ∧ g 0 = f 0 ∧ g 1 = f 1 ∧
      range f ∪ range g = discBd D ∧
      ∀ s t, f s = g t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  obtain ⟨h, k, c⟩ := hD.exists_isChart
  have hfD : ∀ t, f t ∈ D := fun t => discBd_subset D (hfbd ⟨t, rfl⟩)
  let f₀ : unitInterval → ℂ := h ∘ f
  have hf₀ : IsArcMap f₀ :=
    ⟨c.hc.comp_continuous hf.1 hfD,
      fun s t heq => hf.2 (c.gh.injOn (hfD s) (hfD t) heq)⟩
  have hf₀bd : range f₀ ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← c.bd]
    exact mem_image_of_mem h (hfbd ⟨t, rfl⟩)
  obtain ⟨φ⟩ := oArc_sphere
  obtain ⟨g₀, hg₀, hg0, hg1, hcover, hmeet⟩ := exists_other_arc φ hf₀ hf₀bd
  have hg₀bd : ∀ t, g₀ t ∈ sphere (0 : ℂ) 1 :=
    fun t => hcover ▸ Or.inr (mem_range_self t)
  have hg₀D : ∀ t, g₀ t ∈ closedBall (0 : ℂ) 1 :=
    fun t => sphere_subset_closedBall (hg₀bd t)
  let g : unitInterval → S := k ∘ g₀
  have hg : IsArcMap g :=
    ⟨c.gc.comp_continuous hg₀.1 hg₀D,
      fun s t heq => hg₀.2 (c.hg.injOn (hg₀D s) (hg₀D t) heq)⟩
  have hg_bd : ∀ t, g t ∈ discBd D := by
    intro t
    rw [← c.g_sphere]
    exact mem_image_of_mem k (hg₀bd t)
  refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
  · change k (g₀ 0) = f 0
    rw [hg0]
    exact c.gh (hfD 0)
  · change k (g₀ 1) = f 1
    rw [hg1]
    exact c.gh (hfD 1)
  · apply Subset.antisymm
    · rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact hfbd ⟨t, rfl⟩
      · exact hg_bd t
    · intro x hx
      have hhx : h x ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hx
      rcases hcover.symm ▸ hhx with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact Or.inl ⟨t, c.gh.injOn (hfD t) (discBd_subset D hx) ht⟩
      · refine Or.inr ⟨t, ?_⟩
        change k (g₀ t) = x
        rw [ht]
        exact c.gh (discBd_subset D hx)
  · intro s t heq
    apply hmeet s t
    change h (f s) = g₀ t
    rw [heq]
    exact c.hg (hg₀D t)

/-- Cut a disc along a proper line while specifying which
boundary arc belongs to its first piece. This is the cutting
step of VII (2.6), page 218. -/
theorem exists_disc_cut_with_boundary_arc
    {S : Type*} [TopologicalSpace S] [T2Space S] {D F : Set S}
    (hD : IsClosedDisc D) (f : unitInterval → S) (hf : IsArcMap f)
    (hfbd : range f ⊆ discBd D) (hF : IsLineWithEnds F (f 0) (f 1))
    (hFD : F ⊆ D) (hFbd : F ∩ discBd D = {f 0, f 1}) :
    ∃ C A B : Set S, IsLineWithEnds C (f 0) (f 1) ∧
      range f ∪ C = discBd D ∧ IsClosedDisc A ∧ IsClosedDisc B ∧
      A ∪ B = D ∧ A ∩ B = F ∧
      discBd A = range f ∪ F ∧ discBd B = C ∪ F ∧
      discBd D \ range f ⊆ B := by
  obtain ⟨g, hg, hg0, hg1, hcover, hmeet⟩ :=
    exists_complementary_disc_boundary_arc hD f hf hfbd
  have hfg : range f ∩ range g = {f 0, f 1} := by
    apply Subset.antisymm
    · rintro x ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
      rcases hmeet s t ht.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro x (rfl | rfl)
      · exact ⟨mem_range_self 0, ⟨0, hg0⟩⟩
      · exact ⟨mem_range_self 1, ⟨1, hg1⟩⟩
  have hLf : F ∩ range f = {f 0, f 1} := by
    apply Subset.antisymm
    · exact fun x hx => hFbd.subset ⟨hx.1, hfbd hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨hF.left_mem, mem_range_self 0⟩
      · exact ⟨hF.right_mem, mem_range_self 1⟩
  have hLg : F ∩ range g = {f 0, f 1} := by
    apply Subset.antisymm
    · exact fun x hx => hFbd.subset ⟨hx.1, hcover ▸ Or.inr hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨hF.left_mem, ⟨0, hg0⟩⟩
      · exact ⟨hF.right_mem, ⟨1, hg1⟩⟩
  have hgL : IsLineWithEnds (range g) (f 0) (f 1) := by
    simpa only [hg0, hg1] using hg.isLineWithEnds
  have hne : f 0 ≠ f 1 := fun h => zero_ne_one (hf.2 h)
  obtain ⟨A, B, hA, hB, hAB, hI, hbA, hbB⟩ := GM14.Whitney.disc_split hD hF
    hf.isLineWithEnds hgL hfg hLf hLg hcover.symm hFD hne
  refine ⟨range g, A, B, hgL, hcover, hA, hB, hAB, hI, hbA, hbB, ?_⟩
  intro x hx
  have hxg : x ∈ range g := (hcover.symm ▸ hx.1).resolve_left hx.2
  exact discBd_subset B (hbB ▸ Or.inl hxg)

end GraphMinor.GM07
