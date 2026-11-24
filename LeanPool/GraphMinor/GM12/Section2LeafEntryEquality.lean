/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TerminalPatch
public import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM12.Section2LeafEntryPatchProof
import LeanPool.GraphMinor.GM11.Regions

/-!
# A leaf has one incident region and one entry corner

For trace restriction in XII (2.1), pages 243--244, the leaf case
has no sector choice. The punctured normal patch is connected and
lies in any incident region, so two incident regions agree. Any two
approaches in that region enter through this patch and hence have
the same entry edge.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- At a vertex with one half-edge, two regions whose closures contain
the vertex agree. The normal leaf patch meets both regions. -/
theorem region_eq_of_leaf_in_closures
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (hcard : Nat.card (halfEdges Γ γ v) = 1)
    {r r' : Set S} (hr : r ∈ Γ.R) (hr' : r' ∈ Γ.R)
    (hvr : v ∈ closure r) (hvr' : v ∈ closure r') : r = r' := by
  obtain ⟨N, X, hN, hvN, _, _, _, hXZ, hcover⟩ :=
    leafEntryPatch S hS hConn Γ γ hγ v hv hcard r hr hvr
  obtain ⟨z, hzN, hzr'⟩ := mem_closure_iff.mp hvr' N hN hvN
  have hzoff : z ∉ Γ.U := region_subset hr' hzr'
  have hzv : z ∉ ({v} : Set S) := fun hz => hzoff (hz ▸ Γ.V_subset_U hv)
  have hzr : z ∈ r := (hXZ (hcover ⟨hzN, hzoff⟩)).resolve_right hzv
  exact region_eq_of_mem hr hr' hzr hzr'

/-- Two continuous normal approaches to a leaf have the same entry
edge. This handles the one-corner case in the restriction step of
XII (2.1), without any relation between their parameterizations. -/
theorem entersLike_edge_eq_at_leaf
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v w : S} (hv : v ∈ Γ.V) (hcard : Nat.card (halfEdges Γ γ v) = 1)
    {r e e' : Set S} (hr : r ∈ Γ.R) (hw : w ∈ r ∩ K.V)
    (he : e ∈ K.E) (he' : e' ∈ K.E)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a c b d : ℝ} (hac : a < c) (hbd : b < d)
    (hfc : f c = v) (hgd : g d = v)
    (hfr : ∀ z ∈ Ioo a c, f z ∈ r) (hgr : ∀ z ∈ Ioo b d, g z ∈ r)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike g b d e' r v w) : e = e' := by
  have hccl : c ∈ closure (Ioo a c) := by
    rw [closure_Ioo hac.ne]
    exact ⟨hac.le, le_rfl⟩
  have hvr : v ∈ closure r := by
    rw [← hfc]
    exact closure_mono (image_subset_iff.mpr hfr)
      (image_closure_subset_closure_image hf ⟨c, hccl, rfl⟩)
  obtain ⟨N, X, hN, hvN, hvX, hX, hpuncture, hXZ, hcover⟩ :=
    leafEntryPatch S hS hConn Γ γ hγ v hv hcard r hr hvr
  exact entersLike_edge_eq_of_normal_patch hS hConn hK hr hv hw he he'
    hN hvN hvX hX hXZ hpuncture hcover hf hg hac hbd hfc hgd hfr hgr hentry hentry'

end GraphMinor.GM12
