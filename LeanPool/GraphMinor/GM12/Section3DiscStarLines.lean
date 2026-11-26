/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3RadialLines
public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Lines from a disc centre to its boundary

For XII (3.1), page 245, disc coordinates carry the unit-disc radii
to a feasibility disc. Each resulting line joins the chosen centre
to its prescribed boundary point, stays in the disc, and has no other
boundary contact. Distinct lines meet only at the centre.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- Disc charts give an internally disjoint star of lines to any set
of prescribed boundary points. Finiteness is needed only when making
the resulting drawing. -/
theorem exists_star_lines_in_disc
    {S : Type*} [TopologicalSpace S]
    {D Z : Set S} (hD : IsClosedDisc D) (hZ : Z ⊆ discBd D) :
    ∃ c ∈ discInt D, ∃ L : S → Set S,
      (∀ a ∈ Z, IsLineWithEnds (L a) c a ∧ L a ⊆ D ∧ L a ∩ discBd D = {a}) ∧
      ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → L a ∩ L b = {c} := by
  obtain ⟨h, g, chart⟩ := hD.exists_isChart
  let L : S → Set S := fun a => g '' radialLine (h a)
  have hnorm : ∀ a ∈ Z, ‖h a‖ = 1 := by
    intro a ha
    apply mem_sphere_zero_iff_norm.mp
    rw [← chart.bd]
    exact mem_image_of_mem h (hZ ha)
  have hrad : ∀ a ∈ Z, radialLine (h a) ⊆ closedBall 0 1 :=
    fun a ha => radialLine_subset_unitDisc (hnorm a ha)
  have hcentre : g 0 ∈ discInt D := by
    rw [chart.discInt_eq]
    exact ⟨0, by simp, rfl⟩
  refine ⟨g 0, hcentre, L, ?_, ?_⟩
  · intro a ha
    have haD : a ∈ D := discBd_subset D (hZ ha)
    have hga : g (h a) = a := chart.gh haD
    have hcont : ContinuousOn h (g '' radialLine (h a)) :=
      chart.hc.mono (chart.g_subset (hrad a ha))
    obtain ⟨e, he⟩ := exists_homeomorph_image (chart.gc.mono (hrad a ha)) hcont
      (chart.hg.mono (hrad a ha))
    obtain ⟨φ, hφ0, hφ1⟩ := isLineWithEnds_radialLine (hnorm a ha)
    have hline : IsLineWithEnds (L a) (g 0) a := by
      refine ⟨φ.trans e, ?_, ?_⟩
      · change (e (φ 0)).val = g 0
        rw [he, hφ0]
      · change (e (φ 1)).val = a
        rw [he, hφ1, hga]
    refine ⟨hline, chart.g_subset (hrad a ha), ?_⟩
    change g '' radialLine (h a) ∩ discBd D = {a}
    rw [← chart.g_sphere, ← chart.g_inter (hrad a ha) sphere_subset_closedBall,
      radialLine_inter_unitCircle (hnorm a ha), image_singleton, hga]
  · intro a ha b hb hab
    have hne : h a ≠ h b := by
      intro he
      exact hab (chart.gh.injOn (discBd_subset D (hZ ha)) (discBd_subset D (hZ hb)) he)
    change g '' radialLine (h a) ∩ g '' radialLine (h b) = {g 0}
    rw [← chart.g_inter (hrad a ha) (hrad b hb),
      radialLine_inter_radialLine (hnorm a ha) (hnorm b hb) hne, image_singleton]

end GraphMinor.GM12
