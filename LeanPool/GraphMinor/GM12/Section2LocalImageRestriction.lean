/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryImageRestriction
import LeanPool.GraphMinor.GM12.Section2TerminalPatch
import LeanPool.GraphMinor.GM12.Section2EntryIndependence
import LeanPool.GraphMinor.GM11.Regions

/-!
# Restriction needs image inclusion only near vertex visits

In Case 2 of XII (2.1), page 244, the smaller circle contains a
new chord in a region. The chord is closed and misses every drawing
vertex. Near a vertex the smaller curve therefore still lies in the
original curve image. Shorten each entry interval to that part and
apply the image-entry restriction theorem. This records its edge
without requiring the new chord to lie in the original image.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- To preserve an entry edge it suffices that a terminal interval
of the approach lie in the original curve image. -/
theorem trace_mem_edges_of_entry_locally_in_image
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {v w : S} (hv : v ∈ Γ.V) {r e : Set S} (hr : r ∈ Γ.R)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E)
    {g : ℝ → S} (hg : Continuous g) {c d c₀ : ℝ} (hc₀ : c₀ ∈ Ioo c d) (hgd : g d = v)
    (hgr : ∀ t ∈ Ioo c d, g t ∈ r) (himage : ∀ t ∈ Icc c₀ d, g t ∈ range φ)
    (hentry : EntersLike g c d e r v w) : e ∈ W.edges := by
  have hvE : v ∉ e := fun hz => (he.2.1 hz).2 (hK.2.1.2.1 hv)
  have hwE : w ∉ e := fun hz => (he.2.1 hz).2 hw.2
  have hvw : v ≠ w := fun h => region_subset hr (h.symm ▸ hw.1) (Γ.V_subset_U hv)
  have hentry₀ := (entersLike_iff_tail_interval (hK.1.2 r hr) hw.1 hvE hwE hvw
    hg hc₀.1.le hc₀.2 hgd hgr).mp hentry
  exact trace_mem_edges_of_entry_in_image hS hK hE W hW hv hr hw he hg hc₀.2 hgd
    (fun t ht => hgr t ⟨hc₀.1.trans ht.1, ht.2⟩) himage hentry₀

/-- Adding a closed set disjoint from drawing vertices to the curve
image creates no new trace entry edges. This applies to the region
chord in Case 2 of XII (2.1), page 244. -/
theorem trace_mem_edges_of_entry_off_closed_set
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {L : Set S} (hL : IsClosed L) (hLV : Disjoint L Γ.V)
    {v w : S} (hv : v ∈ Γ.V) {r e : Set S} (hr : r ∈ Γ.R)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E)
    {g : ℝ → S} (hg : Continuous g) {c d : ℝ} (hcd : c < d) (hgd : g d = v)
    (hgr : ∀ t ∈ Ioo c d, g t ∈ r) (himage : ∀ t ∈ Icc c d, g t ∈ range φ ∪ L)
    (hentry : EntersLike g c d e r v w) : e ∈ W.edges := by
  have hvL : v ∉ L := fun hz => disjoint_left.mp hLV hz hv
  have hvφ : v ∈ range φ := (hgd ▸ himage d ⟨hcd.le, le_rfl⟩).resolve_right hvL
  have hcover : Lᶜ ∩ (range φ ∪ L) ⊆ range φ := fun _ hz => hz.2.resolve_right hz.1
  obtain ⟨c₀, hc₀, hlocal⟩ := exists_terminal_interval_in_patch hg hcd hgd
    (fun t ht => himage t ⟨ht.1.le, ht.2.le⟩) hL.isOpen_compl hvL hvφ hcover
  exact trace_mem_edges_of_entry_locally_in_image hS hK hE W hW hv hr hw he
    hg hc₀ hgd hgr hlocal hentry

/-- The outgoing version of closed-set avoidance is the incoming
version for the reversed real interval. -/
theorem trace_mem_edges_of_leaving_off_closed_set
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {L : Set S} (hL : IsClosed L) (hLV : Disjoint L Γ.V)
    {v w : S} (hv : v ∈ Γ.V) {r e : Set S} (hr : r ∈ Γ.R)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E)
    {g : ℝ → S} (hg : Continuous g) {c d : ℝ} (hcd : c < d) (hgc : g c = v)
    (hgr : ∀ t ∈ Ioo c d, g t ∈ r) (himage : ∀ t ∈ Icc c d, g t ∈ range φ ∪ L)
    (hleave : LeavesLike g c d e r v w) : e ∈ W.edges := by
  apply trace_mem_edges_of_entry_off_closed_set hS hK hE W hW hL hLV hv hr hw he
    (hg.comp continuous_neg) (neg_lt_neg hcd)
    (by simpa only [Function.comp_apply, neg_neg] using hgc) _ _ hleave
  · intro t ht
    exact hgr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro t ht
    exact himage (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩

end GraphMinor.GM12
