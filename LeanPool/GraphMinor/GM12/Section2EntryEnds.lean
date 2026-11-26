/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM12.Section2SpokePaths

/-!
# The endpoints of an entry edge

In XII's trace definition, page 243, an entry curve follows the approach
to a vertex and then traces a radial edge to a region hub. Continuity
puts both points in the closure of that edge. The radial endpoint
properties identify them as its two graph ends. This allows entry
existence to construct actual two-edge graph-walk steps.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The joining vertex and terminal hub of an entry curve lie in the
closure of the edge it traces. -/
theorem entryCurve_ends_mem_closure {S : Type*} [TopologicalSpace S]
    {f : ℝ → S} {h c : ℝ} {e : Set S} {v w : S} {ξ : Curve S}
    (hfc : f c = v) (hξ : IsEntryCurve f h c e w ξ) :
    v ∈ closure e ∧ w ∈ closure e := by
  obtain ⟨s, hs, hs1, hfirst, _, himage, hlast⟩ := hξ
  have hξs : ξ s = v := by
    have hh := hfirst s le_rfl
    have hs0 : s.val ≠ 0 := ne_of_gt (show (0 : ℝ) < s.val from hs)
    simpa only [div_self hs0, one_mul, add_sub_cancel, hfc] using hh
  have hmap : ∀ t ∈ closure (Ioo s (1 : unitInterval)), ξ t ∈ closure e := by
    intro t ht
    exact map_mem_closure ξ.continuous ht (t := e) fun u hu => himage ▸ mem_image_of_mem ξ hu
  have hscl : s ∈ closure (Ioo s (1 : unitInterval)) := by
    rw [closure_Ioo hs1.ne]
    exact ⟨le_rfl, hs1.le⟩
  have h1cl : (1 : unitInterval) ∈ closure (Ioo s (1 : unitInterval)) := by
    rw [closure_Ioo hs1.ne]
    exact ⟨hs1.le, le_rfl⟩
  exact ⟨hξs ▸ hmap s hscl, hlast ▸ hmap 1 h1cl⟩

/-- An entry edge has precisely the original vertex and the region
hub as its two graph ends. This recovers the graph-link data from the
curve form of the entry definition in XII, page 243. -/
theorem entersLike_isLink {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : PreRad (.drawing Γ) K) {r e : Set S} (hr : r ∈ Γ.R)
    {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ r) (hwV : w ∈ K.V) (he : e ∈ K.E)
    {f : ℝ → S} {a c : ℝ} (hfc : f c = v)
    (hentry : EntersLike f a c e r v w) : K.toGraph.IsLink e v w := by
  obtain ⟨h, _, ξ, _, hξ, _, _⟩ := hentry
  obtain ⟨hve, hwe⟩ := entryCurve_ends_mem_closure hfc hξ
  have her := spoke_subset_region hS hrad hr he hw hwV hwe
  have : Nonempty S := ⟨v⟩
  obtain ⟨η, hη⟩ := exists_edgePar K
  obtain ⟨b, hb⟩ := exists_end_eq hη he (radial_V hrad hv) hve
  let i : halfEdges K η v := ⟨(e, b), he, hb⟩
  have hpoint : spoke η i.val 1 ∈ r := her (spoke_mem_edge hη (x := i.val) he one_pos)
  have hcap := spoke_ends_of_halfEdge_point hS hrad hη hv i hr hw hwV one_pos hpoint
  exact ⟨he, radial_V hrad hv, hwV, hcap⟩

/-- The same graph-endpoint conclusion for the outgoing edge, obtained
by reversing the real parameter as in the leaving-edge definition. -/
theorem leavesLike_isLink {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : PreRad (.drawing Γ) K) {r e : Set S} (hr : r ∈ Γ.R)
    {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ r) (hwV : w ∈ K.V) (he : e ∈ K.E)
    {f : ℝ → S} {a c : ℝ} (hfa : f a = v)
    (hentry : LeavesLike f a c e r v w) : K.toGraph.IsLink e v w := by
  exact entersLike_isLink hS hrad hr hv hw hwV he
    (by simpa only [neg_neg] using hfa) hentry

end GraphMinor.GM12
