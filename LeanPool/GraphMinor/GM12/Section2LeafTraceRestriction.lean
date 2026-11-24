/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2LeafEntryEquality
public import LeanPool.GraphMinor.GM12.Section2TraceGerms
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.Walks

/-!
# Trace restriction at a leaf

For XII (2.1), pages 243--244, consider an entry edge of the
restricted curve at a leaf visited by the original trace. Locate
an incoming recorded visit of the original trace. Both approach
regions have the leaf in their closure, so they agree. Their hubs
agree as well. The one-corner entry comparison identifies the edges,
which proves edge containment at this vertex.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem approach_mem_closure
    {S : Type*} [TopologicalSpace S] {f : ℝ → S} (hf : Continuous f)
    {a b : ℝ} (hab : a < b) {r : Set S} (hfr : ∀ t ∈ Ioo a b, f t ∈ r) :
    f b ∈ closure r := by
  have hb : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  exact closure_mono (image_subset_iff.mpr hfr)
    (image_closure_subset_closure_image hf ⟨b, hb, rfl⟩)

/-- Every entry edge of another normal curve at a visited leaf is
already in the original trace. No shared parameterization of the
two approaches is required. -/
theorem traceSteps_mem_edges_of_entry_at_leaf
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (hcard : Nat.card (halfEdges Γ γ v) = 1)
    {f g : ℝ → S} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} {u z : S} (W : GraphWalk K.toGraph u z)
    (hW : TraceSteps Γ K f a b W) {s : ℝ} (hs : s ∈ Ioc a b) (hfs : f s = v)
    {c d : ℝ} (hcd : c < d) (hgd : g d = v)
    {r e : Set S} {w : S} (hr : r ∈ Γ.R) (hw : w ∈ r ∩ K.V)
    (he : e ∈ K.E) (hgr : ∀ t ∈ Ioo c d, g t ∈ r)
    (hentry : EntersLike g c d e r v w) : e ∈ W.edges := by
  obtain ⟨p, w₀, r₀, e₀, _, hps, hw₀, hr₀, hw₀r, he₀W, hfr₀, hentry₀⟩ :=
    traceSteps_exists_incoming_germ W hW hs (hfs.symm ▸ hv)
  rw [hfs] at hentry₀
  have hvr : v ∈ closure r := hgd ▸ approach_mem_closure hg hcd hgr
  have hvr₀ : v ∈ closure r₀ := hfs ▸ approach_mem_closure hf hps hfr₀
  have hrr := region_eq_of_leaf_in_closures hS hConn hγ hv hcard hr₀ hr hvr₀ hvr
  subst r₀
  have hww := hub_unique (show PreRad (.drawing Γ) K from ⟨hK.1, hK.2.1⟩)
    hr hw.1 hw.2 hw₀r hw₀
  subst w
  have he₀ : e₀ ∈ K.E := (walkDrawing_isSubdrawing K W).2 (by
    rw [walkDrawing_E]
    exact he₀W)
  have heq := entersLike_edge_eq_at_leaf hS hConn hK hγ hv hcard hr
    ⟨hw₀r, hw₀⟩ he he₀ hg hf hcd hps hgd hfs hgr hfr₀ hentry hentry₀
  exact heq.symm ▸ he₀W

/-- The leaf part of trace restriction for closed-curve traces:
any entry at a leaf in the original curve image uses a recorded edge. -/
theorem trace_mem_edges_of_entry_at_leaf
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (hcard : Nat.card (halfEdges Γ γ v) = 1)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hvφ : v ∈ range φ)
    {g : ℝ → S} (hg : Continuous g) {c d : ℝ} (hcd : c < d) (hgd : g d = v)
    {r e : Set S} {w : S} (hr : r ∈ Γ.R) (hw : w ∈ r ∩ K.V)
    (he : e ∈ K.E) (hgr : ∀ t ∈ Ioo c d, g t ∈ r)
    (hentry : EntersLike g c d e r v w) : e ∈ W.edges := by
  obtain ⟨z, hz⟩ := hvφ
  rcases hW.2 with ⟨_, _, _, r₀, hr₀, hφr₀, _⟩ | ⟨_, _, a, hsteps⟩
  · exact (region_subset hr₀ (hφr₀ (mem_range_self z))
      (hz.symm ▸ Γ.V_subset_U hv)).elim
  · obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn a).surjOn (mem_univ z)
    have hfs : periodicCurve φ s = v := (congrArg φ hsz).trans hz
    have hex : ∃ t ∈ Ioc a (a + 1), periodicCurve φ t = v := by
      by_cases hsa : s = a
      · have hp := traceSteps_parameters W hsteps
        refine ⟨a + 1, ⟨by linarith, le_rfl⟩, ?_⟩
        exact hp.2.2.2.1.trans (hp.2.1.symm.trans (hsa ▸ hfs))
      · exact ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hsa), hs.2.le⟩, hfs⟩
    obtain ⟨t, ht, hft⟩ := hex
    exact traceSteps_mem_edges_of_entry_at_leaf hS hConn hK hγ hv hcard
      (periodicCurve_continuous φ) hg W hsteps ht hft hcd hgd hr hw he hgr hentry

end GraphMinor.GM12
