/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2CommonCornerEntry
import LeanPool.GraphMinor.GM11.Regions

/-!
# Shortening real approaches into a corner patch

For the local comparison in XII (2.1), pages 243--244, continuity
puts the end of each approach in the chosen neighbourhood of its
vertex. Its other points are in the region, so local coverage puts
them in the corner patch. The common-patch comparison then applies
without requiring normalized paths in its hypotheses.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A terminal real interval lies in a patch whenever the patch
contains the region part of a neighbourhood of the limiting vertex. -/
theorem exists_terminal_interval_in_patch
    {S : Type*} [TopologicalSpace S] {f : ℝ → S} (hf : Continuous f)
    {a c : ℝ} (hac : a < c) {r N X : Set S} {v : S}
    (hfc : f c = v) (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hN : IsOpen N) (hvN : v ∈ N) (hvX : v ∈ X) (hcover : N ∩ r ⊆ X) :
    ∃ s ∈ Ioo a c, ∀ t ∈ Icc s c, f t ∈ X := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((hN.preimage hf).mem_nhds (hfc.symm ▸ hvN))
  let δ := min ((c - a) / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδa : δ ≤ (c - a) / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 2 := min_le_right _ _
  refine ⟨c - δ, ⟨by linarith, by linarith⟩, ?_⟩
  intro t ht
  by_cases htc : t = c
  · simpa only [htc, hfc] using hvX
  · apply hcover
    refine ⟨hball ?_, hfr t ⟨by linarith [ht.1], lt_of_le_of_ne ht.2 htc⟩⟩
    change dist t c < ε
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Two approaches in a region have the same entry edge if a normal
patch covers that region near their common limiting vertex. -/
theorem entersLike_edge_eq_of_normal_patch
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' N X : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hN : IsOpen N) (hvN : v ∈ N) (hvX : v ∈ X)
    (hX : IsSimplyConnectedSet X) (hXZ : X ⊆ r ∪ {v})
    (hpuncture : IsPathConnected (X \ {v})) (hcover : N \ Γ.U ⊆ X)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a c b d : ℝ} (hac : a < c) (hbd : b < d)
    (hfc : f c = v) (hgd : g d = v)
    (hfr : ∀ z ∈ Ioo a c, f z ∈ r) (hgr : ∀ z ∈ Ioo b d, g z ∈ r)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike g b d e' r v w) : e = e' := by
  have hNr : N ∩ r ⊆ X := fun _ hz => hcover ⟨hz.1, region_subset hr hz.2⟩
  obtain ⟨s, hs, hfX⟩ := exists_terminal_interval_in_patch hf hac hfc hfr hN hvN hvX hNr
  obtain ⟨t, ht, hgX⟩ := exists_terminal_interval_in_patch hg hbd hgd hgr hN hvN hvX hNr
  have hXR : X \ {v} ⊆ r := by
    intro z hz
    exact (hXZ hz.1).resolve_right hz.2
  exact entersLike_edge_eq_of_common_terminal_patch hS hConn hK hr hv hw he he'
    hX hXZ hpuncture hXR hf hg hs ht hfc hgd hfr hgr hentry hentry' hfX hgX

end GraphMinor.GM12
