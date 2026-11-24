/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2LeafPatch
import LeanPool.GraphMinor.GM12.Section2LeafSlitPatch
import LeanPool.GraphMinor.GM11.Regions

/-!
# The leaf entry patch

The omitted entry-edge lemma of XII, page 243, requires the incoming
curve and spoke to be compared in the incident region with the leaf
restored. The slit patch at the unique incident edge has a connected
puncture off the drawing. Since the leaf is in the region's closure,
that puncture meets the region and therefore lies wholly in it. This
proves the patch statement at leaves, including its local coverage.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- The leaf patch needed in the omitted entry-edge existence proof
on XII page 243. The punctured slit patch lies in the incident region,
and its contraction restores the leaf point. -/
theorem leafEntryPatch : LeafEntryPatchStatement.{u} := by
  intro S _ _ hS _ Γ γ hγ v hv hcard r hr hvr
  obtain ⟨e, w, he, _, _, hL, hleaf⟩ := exists_incident_line_at_leaf Γ hγ hv hcard
  obtain ⟨N, X, hN, hvN, hvX, hsimple, hpath, hXoff, hcover⟩ :=
    exists_slit_patch_at_leaf_line hS Γ he hL hleaf
  have hdis : Disjoint (X \ {v}) Γ.U := disjoint_left.mpr (by
    intro x hx hxU
    rcases hXoff hx.1 with hxoff | hxv
    · exact hxoff hxU
    · exact hx.2 hxv)
  obtain ⟨x, hxN, hxr⟩ := mem_closure_iff.mp hvr N hN hvN
  have hxoff : x ∉ Γ.U := region_subset hr hxr
  have hxX : x ∈ X := hcover ⟨hxN, hxoff⟩
  have hxv : x ≠ v := fun heq => hxoff (heq.symm ▸ Γ.V_subset_U hv)
  have hYr : X \ {v} ⊆ r := subset_region hr hpath.isConnected.isPreconnected hdis ⟨hxX, hxv⟩ hxr
  refine ⟨N, X, hN, hvN, hvX, hsimple, hpath, ?_, hcover⟩
  intro y hy
  by_cases hyv : y = v
  · exact Or.inr hyv
  · exact Or.inl (hYr ⟨hy, hyv⟩)

end GraphMinor.GM12
