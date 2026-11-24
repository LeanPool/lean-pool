/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73SupportedCollapse
public import LeanPool.GraphMinor.GM12.Section73RadialContraction
import LeanPool.GraphMinor.GM12.Section73CellularContraction
import LeanPool.GraphMinor.GM12.Section73ContractedFaces
import LeanPool.GraphMinor.GM12.Section73RadialMaximal

/-!
# The radial contraction with a supporting disc

For the disc comparison in XII (7.3), Claim (1), page 262,
choose the star collapse supported in a closed disc inside the
merged region. Assemble its image drawing and clean up the empty
parallel bigons as before. The resulting radial drawing retains
this same collapse map and its fixed boundary and outside.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The radial-star construction with its supporting disc, for
the controlled boundary homotopy in XII (7.3), Claim (1), page 262.
The image and the cleaned radial drawing use the same map. -/
theorem exists_supported_radial_star_contraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r) :
    ∃ (D : Set S) (f : C(S, S)) (H J : Drawing S), IsClosedDisc D ∧ D ⊆ r ∧
      ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ discInt D ∧
      Function.Surjective f ∧ (∀ x ∉ discInt D, f x = x) ∧
      (∀ x ∉ r, f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} ∧
      J.IsSubdrawing H ∧ J.V = H.V ∧
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J := by
  obtain ⟨D, f, hD, hDr, hAD, hsurj, hfixD, hcollapse, hfibre⟩ :=
    exists_radial_star_collapse_supported_in_disc hS ⟨hK.1, hK.2.1⟩ hv hunique hr hvr
      (htwo.2 r hr)
  have hfix : ∀ x ∉ r, f x = x := fun x hxr => hfixD x
    (fun hxD => hxr (hDr (Surface.discInt_subset D hxD)))
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_radial_star_image_drawing hS ⟨hK.1, hK.2.1⟩ hv
    f hcollapse hfibre
  have hinter := image_radial_inter_deleted_drawing hS ⟨hK.1, hK.2.1⟩ hv hr hvr hfix hfibre
  have hcap : (deleteVertices Γ {v}).U ∩ H.U = (deleteVertices Γ {v}).V := by
    rw [hHU]
    exact hinter.1
  have hV : (deleteVertices Γ {v}).V ⊆ H.V := by rw [hHV]; exact hinter.2
  have hhub : ∀ s ∈ (deleteVertices Γ {v}).R, ∃! w, w ∈ s ∧ w ∈ H.V := by
    rw [hHV]
    exact image_radial_region_hub_unique hS hK hE hv hr hvr hfix hcollapse hfibre
  have hregion : ∀ w ∈ H.V \ (deleteVertices Γ {v}).V,
      ∃ s ∈ (deleteVertices Γ {v}).R, w ∈ s := by
    intro w hw
    apply exists_region_of_notMem
    intro hwU
    exact hw.2 (hcap.subset ⟨hwU, H.V_subset_U hw.1⟩)
  have hlink : ∀ e ∈ H.E, ∃ a ∈ (deleteVertices Γ {v}).V,
      ∃ b ∈ H.V \ (deleteVertices Γ {v}).V, closure e ∩ H.V = {a, b} := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := hHE.subset he
    obtain ⟨a, ha, b, hb, hends⟩ := image_radial_edge_ends hS ⟨hK.1, hK.2.1⟩ hv hr hvr
      f hfix hfibre hg.1 hg.2
    rw [hHV]
    exact ⟨a, ha, b, hb, hends⟩
  have hHtwo := radial_star_image_isTwoCell hS hK hv f hsurj hfibre hHU
  have hface : ∀ s ∈ H.R, ∀ a ∈ (deleteVertices Γ {v}).E,
      ∀ b ∈ (deleteVertices Γ {v}).E, a ⊆ s → b ⊆ s → a = b := by
    intro s hs
    obtain ⟨_, _, _, _, huniq⟩ := contracted_radial_region_edges hS hK hE hv hr hvr
      f hsurj hfix hfibre hHU hs
    exact huniq
  obtain ⟨J, hJH, hJV, hJtwo, hJpre, hJface⟩ :=
    exists_preRadial_subdrawing_by_cleanup hS hHtwo hcap hV hhub hregion hlink hface
  have hJ := isRadial_of_twoCell_unique_edges hS htwo hE' hJpre hJtwo hJface
  exact ⟨D, f, H, J, hD, hDr, hAD, hsurj, hfixD, hfix, hcollapse, hfibre, hHU,
    hHV, hHE, hJH, hJV, hJ⟩

end GraphMinor.GM12
