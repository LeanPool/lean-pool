/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TerminalPatch
import LeanPool.GraphMinor.GM12.Section2SectorPatch

/-!
# The entering sector determines the entry edge

For image restriction in XII (2.1), pages 243--244, two curves
entering a vertex through the same sector must use the same spoke.
Shrink both approaches into the simply connected patch of that
closed sector disc. Their entry comparisons agree by the common
patch lemma, regardless of the curves' parameterizations.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Two normal approaches through the same closed-disc sector have
the same entry edge. Only the local inclusion of the sector interior
in the region is used; the curves themselves can be different. -/
theorem entersLike_edge_eq_of_common_sector
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' D W : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hD : IsClosedDisc D) (hvD : v ∈ discBd D)
    (hW : IsOpen W) (hvW : v ∈ W) (hregion : (D \ discBd D) ∩ W ⊆ r)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a c b d a₀ b₀ : ℝ} (haa₀ : a ≤ a₀) (ha₀c : a₀ < c)
    (hbb₀ : b ≤ b₀) (hb₀d : b₀ < d)
    (hfc : f c = v) (hgd : g d = v)
    (hfr : ∀ z ∈ Ioo a c, f z ∈ r) (hgr : ∀ z ∈ Ioo b d, g z ∈ r)
    (hfD : ∀ z ∈ Ioo a₀ c, f z ∈ D \ discBd D)
    (hgD : ∀ z ∈ Ioo b₀ d, g z ∈ D \ discBd D)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike g b d e' r v w) : e = e' := by
  obtain ⟨N, X, hN, hvN, hvX, hX, hlocal, hnear, hpuncture⟩ :=
    exists_simplyConnected_sector_patch_with_puncture hD hvD hW hvW
  have hcover : N ∩ (D \ discBd D) ⊆ X := by
    intro z hz
    exact hnear ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
  obtain ⟨s, hs, hfX⟩ := exists_terminal_interval_in_patch hf ha₀c hfc hfD hN hvN hvX hcover
  obtain ⟨t, ht, hgX⟩ := exists_terminal_interval_in_patch hg hb₀d hgd hgD hN hvN hvX hcover
  have hXZ : X ⊆ r ∪ {v} := by
    intro z hz
    rcases hlocal hz with hz | hz
    · exact Or.inl (hregion hz)
    · exact Or.inr hz
  have hXR : X \ {v} ⊆ r := fun _ hz => (hXZ hz.1).resolve_right hz.2
  exact entersLike_edge_eq_of_common_terminal_patch hS hConn hK hr hv hw he he'
    hX hXZ hpuncture hXR hf hg ⟨haa₀.trans_lt hs.1, hs.2⟩ ⟨hbb₀.trans_lt ht.1, ht.2⟩ hfc hgd hfr
      hgr hentry hentry' hfX hgX

end GraphMinor.GM12
