/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2PathHomotopy

/-!
# Deforming one region visit to its two spokes

In Case 1 of XII (2.1), page 244, cut a region visit at an interior
point. Reverse its first half so that both approaches start at that
point. The exit and entry comparisons continue these approaches
along their spokes to the region hub. Their comparison paths lie
in the simply connected region, so they are homotopic. Cancelling
the two approach halves leaves a homotopy from the original visit
to the two-spoke path, with both ends fixed.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The path algebra for the paper's deformation of a single region
visit. Both entry comparison paths are in one simply connected region,
so the original two halves deform to the two spokes through its hub. -/
theorem region_visit_homotopic_to_spokes
    {X : Type*} [TopologicalSpace X] {R : Set X}
    (hR : IsSimplyConnectedSet R) {x u v w : X}
    (G : Path x u) (F : Path x v) (β : Path u w) (α : Path v w)
    (σ ρ : Path x w) (hσ : ∀ t, σ t ∈ R) (hρ : ∀ t, ρ t ∈ R)
    (hleft : (G.trans β).Homotopic σ) (hright : (F.trans α).Homotopic ρ) :
    (G.symm.trans F).Homotopic (β.trans α.symm) := by
  have hσρ := paths_homotopic_of_range_in_simplyConnected hR σ ρ hσ hρ
  have hentry : (G.trans β).Homotopic (F.trans α) := hleft.trans (hσρ.trans hright.symm)
  have hcancel : (G.symm.trans (G.trans β)).Homotopic β :=
    (Path.Homotopic.trans_assoc G.symm G β).symm.trans
      (((Path.Homotopic.symm_trans G).hcomp (Path.Homotopic.refl β)).trans
        (Path.Homotopic.refl_trans β))
  have hβ : β.Homotopic ((G.symm.trans F).trans α) :=
    hcancel.symm.trans (((Path.Homotopic.refl G.symm).hcomp hentry).trans
      (Path.Homotopic.trans_assoc G.symm F α).symm)
  have hreduce : (((G.symm.trans F).trans α).trans α.symm).Homotopic (G.symm.trans F) :=
    (Path.Homotopic.trans_assoc (G.symm.trans F) α α.symm).trans
      (((Path.Homotopic.refl (G.symm.trans F)).hcomp (Path.Homotopic.trans_symm α)).trans
        (Path.Homotopic.trans_refl (G.symm.trans F)))
  exact ((hβ.hcomp (Path.Homotopic.refl α.symm)).trans hreduce).symm

end GraphMinor.GM12
