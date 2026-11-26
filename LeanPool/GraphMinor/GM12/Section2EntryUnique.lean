/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM12.Section2EntryComparison
import LeanPool.GraphMinor.GM12.Section2PathHomotopy
import LeanPool.GraphMinor.GM12.Section2SpokeUniqueness
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Section7b
import LeanPool.GraphMinor.GM12.Section2EntryPaths

/-!
# Uniqueness of the entry edge

This file proves the uniqueness assertion omitted in XII, page 243.
Start the approach before both chosen entry starting points. Normalize
each entry as that approach followed by its spoke. The two comparison
paths lie in the open-disc region, so they are homotopic. Cancelling
the common approach makes the spokes homotopic. XI (7.2) and the
pre-radial condition then force the edges to be equal.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- The uniqueness part of the entry-edge definition of XII, page 243,
including comparisons whose witnesses choose different starting points.
The proof uses the proved XI (7.2), over its original objects. -/
theorem entersLike_edge_unique
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hends : closure e ∩ K.V = {v, w}) (hends' : closure e' ∩ K.V = {v, w})
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hfc : f c = v)
    (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike f a c e' r v w) : e = e' := by
  classical
  obtain ⟨h, hh, ξ, ρ, hξ, hρ, hhom⟩ := hentry
  obtain ⟨h', hh', ξ', ρ', hξ', hρ', hhom'⟩ := hentry'
  let h₀ : ℝ := min h h'
  have h₀a : a < h₀ := lt_min hh.1 hh'.1
  have h₀c : h₀ < c := lt_of_le_of_lt (min_le_left _ _) hh.2
  have hpos : 0 < c - h₀ := sub_pos.mpr h₀c
  obtain ⟨F, hFval, hFinside⟩ :=
    exists_affine_approach_path h₀c hf.continuousOn hfc
      (fun t ht => hfr t ⟨h₀a.trans_le ht.1, ht.2⟩)
  let s : unitInterval := ⟨(h - h₀) / (c - h₀),
    div_nonneg (sub_nonneg.mpr (min_le_left _ _)) hpos.le,
    (div_le_one hpos).mpr (by linarith [hh.2])⟩
  let s' : unitInterval := ⟨(h' - h₀) / (c - h₀),
    div_nonneg (sub_nonneg.mpr (min_le_right _ _)) hpos.le,
    (div_le_one hpos).mpr (by linarith [hh'.2])⟩
  have hs : s < 1 := (div_lt_one hpos).mpr (by linarith [hh.2])
  have hs' : s' < 1 := (div_lt_one hpos).mpr (by linarith [hh'.2])
  have hstart : h = h₀ + s.val * (c - h₀) := by
    change h = h₀ + (h - h₀) / (c - h₀) * (c - h₀)
    field_simp [ne_of_gt hpos]
    ring
  have hstart' : h' = h₀ + s'.val * (c - h₀) := by
    change h' = h₀ + (h' - h₀) / (c - h₀) * (c - h₀)
    field_simp [ne_of_gt hpos]
    ring
  have hvE : v ∉ e := fun hx => (he.2.1 hx).2 (hK.2.1.2.1 hv)
  have hwE : w ∉ e := fun hx => (he.2.1 hx).2 hw.2
  have hvE' : v ∉ e' := fun hx => (he'.2.1 hx).2 (hK.2.1.2.1 hv)
  have hwE' : w ∉ e' := fun hx => (he'.2.1 hx).2 hw.2
  have hvw : v ≠ w := fun h => region_subset hr (h.symm ▸ hw.1) (Γ.V_subset_U hv)
  obtain ⟨β, σ, hβinj, hβrange, _, hσr, hβhom⟩ := compare_entry_to_approach
    hw.1 F hFval hstart hfc hvE hwE hvw hξ hρ hhom
  obtain ⟨β', σ', hβinj', hβrange', _, hσr', hβhom'⟩ := compare_entry_to_approach
    hw.1 F hFval hstart' hfc hvE' hwE' hvw hξ' hρ' hhom'
  let R : Set (r ∪ {v} : Set S) := (Subtype.val : (r ∪ {v} : Set S) → S) ⁻¹' r
  have hR : IsSimplyConnectedSet R :=
    (openDisc_in_subspace (hK.1.2 r hr) (show r ⊆ r ∪ {v} from
      subset_union_left)).isSimplyConnectedSet
  have hββ' : β.Homotopic β' := terminal_paths_homotopic_of_entries hR F
    (fun t ht => hFinside t ht) β β' hs hs' σ σ' hσr hσr' hβhom hβhom'
  apply spoke_eq_of_paths_homotopic hS hConn hK.2.1 hr hv hw he he' hends hends'
    (β.cast F.target.symm rfl) (β'.cast F.target.symm rfl)
  · intro x y hxy
    exact hβinj (congrArg Subtype.val hxy)
  · intro x y hxy
    exact hβinj' (congrArg Subtype.val hxy)
  · exact hβrange
  · exact hβrange'
  · exact hββ'.pathCast F.target.symm rfl

/-- The leaving edge is unique as well: reverse the real parameter and
apply entry uniqueness. This is the outgoing half of the omitted
uniqueness assertion in XII's trace definition, page 243. -/
theorem leavesLike_edge_unique
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hends : closure e ∩ K.V = {v, w}) (hends' : closure e' ∩ K.V = {v, w})
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hfa : f a = v)
    (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hleave : LeavesLike f a c e r v w) (hleave' : LeavesLike f a c e' r v w) : e = e' := by
  apply entersLike_edge_unique hS hConn hK hr hv hw he he' hends hends'
    (hf.comp continuous_neg) (by simpa only [Function.comp_apply, neg_neg] using hfa) _ hleave
      hleave'
  intro t ht
  apply hfr
  constructor <;> linarith [ht.1, ht.2]

end GraphMinor.GM12
