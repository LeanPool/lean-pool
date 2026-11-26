/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section74LeafDiscGlue
import LeanPool.GraphMinor.GM12.Section74SlitDisc
import LeanPool.GraphMinor.GM12.Section74BoundaryParam
import LeanPool.GraphMinor.GM11.Section4c

/-!
# Bounding a circle through the slit disc at a leaf

In the leaf case needed for XII (7.4), pages 262--263, a slit
disc `N` meets the old drawing in one line `L`, and that line
meets its boundary at one point. Every other point of `N` is in
the old open-disc region. Its boundary is therefore a circle
punctured at that point, and its interior off the drawing is
preconnected by the slit lemma. The disc-gluing construction
then bounds any circle whose part outside `N` is in the old
region, with the bounding disc wholly in the enlarged region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A slit disc gives the circle-enclosure required for the
open-disc criterion at a deleted leaf. All local disc conditions
come from the geometric lens construction. -/
theorem exists_disc_bounding_circle_in_leaf_region_of_slit_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {r Y N L F : Set S} {w a b : S}
    (hr : r ∈ Γ.R) (hdr : IsOpenDisc r) (hrY : r ⊆ Y)
    (hShape : Y ⊆ r ∪ Γ.U) (hN : IsClosedDisc N) (hNY : N ⊆ Y)
    (hLine : IsLineWithEnds L a b) (hLN : L ⊆ N)
    (hNG : N ∩ Γ.U = L) (hbdL : discBd N ∩ L = {w})
    (hF : IsOArc F) (hFA : F \ discInt N ⊆ r) :
    ∃ D : Set S, D ⊆ Y ∧ IsClosedDisc D ∧ discBd D = F := by
  have hLG : L ⊆ Γ.U := by intro x hx; exact (hNG.symm ▸ hx).2
  have hw : w ∈ discBd N ∩ L := hbdL.symm ▸ mem_singleton w
  have hbd : discBd N ∩ r = discBd N \ {w} := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨hx.1, ?_⟩
      intro hxw
      exact region_subset hr hx.2 (hxw.symm ▸ hLG hw.2)
    · intro x hx
      have hxN : x ∈ N := Surface.discBd_subset N hx.1
      refine ⟨hx.1, ?_⟩
      apply (hShape (hNY hxN)).resolve_right
      intro hxG
      have hxL : x ∈ L := hNG ▸ (⟨hxN, hxG⟩ : x ∈ N ∩ Γ.U)
      exact hx.2 (hbdL ▸ (⟨hx.1, hxL⟩ : x ∈ discBd N ∩ L))
  have hint : discInt N ∩ r = discInt N \ L := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hx.1, fun hxL => region_subset hr hx.2 (hLG hxL)⟩
    · intro x hx
      have hxN := discInt_subset N hx.1
      exact ⟨hx.1, (hShape (hNY hxN)).resolve_right (fun hxG => hx.2 (hNG ▸ ⟨hxN, hxG⟩))⟩
  have hT : IsPreconnected (discInt N ∩ r) := by
    rw [hint]
    exact isPreconnected_discInt_sdiff_line_of_singleton_boundary hN hLine hLN hbdL
  have hTne : (discInt N ∩ r).Nonempty := by
    obtain ⟨x, hxN, hxG⟩ := exists_notMem_U (Γ := Γ) hS
      (hN.isOpen_discInt (fun x => (hS.2.2 x).isManifoldPoint)) hN.nonempty_discInt
    exact ⟨x, hxN, (hShape (hNY (discInt_subset N hxN))).resolve_right hxG⟩
  obtain ⟨ℓ, hℓ, h0, h1, hinj, hrange⟩ := exists_punctured_oArc_parameter hN.isOArc_discBd hw.1
  have hwG : w ∈ Γ.U := hLG hw.2
  have hwr : w ∉ r := fun h => region_subset hr h hwG
  obtain ⟨D, hDsub, hD, hDb⟩ := exists_disc_bounding_circle_by_leaf_gluing hS hdr hN hF hℓ
    (h0 ▸ hwr) (h1 ▸ hwr) hinj (hbd.trans hrange.symm) hT hTne hFA
  exact ⟨D, hDsub.trans (union_subset hrY hNY), hD, hDb⟩

end GraphMinor.GM12
