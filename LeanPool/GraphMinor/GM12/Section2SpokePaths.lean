/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialFaces

/-!
# Paths along radial spokes

For the entry definition of XII page 243, an edge must be traced once
from the boundary vertex to the hub. A radial edge has distinct ends,
so XI's full edge parametrization is injective. Its open parameter
interval maps exactly to the edge, and every positive point lies in
the hub's region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- An injective parametrization of an edge closure with its two ends
as endpoints maps the open interval exactly onto the edge. -/
theorem path_interior_image_of_edge_closure {S : Type*} [TopologicalSpace S]
    {K : Drawing S} {e : Set S} (he : e ∈ K.E) {v c : S}
    (hcap : closure e ∩ K.V = {v, c}) (hv : v ∈ K.V) (hc : c ∈ K.V)
    (β : Path v c) (hinj : Function.Injective β) (hrange : range β = closure e) :
    β '' Ioo (0 : I) 1 = e := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, ht, rfl⟩
    have hcl : β t ∈ closure e := hrange ▸ mem_range_self t
    have hnot : β t ∉ K.V := by
      intro hV
      have hm : β t ∈ ({v, c} : Set S) := hcap ▸ ⟨hcl, hV⟩
      rcases hm with h | h
      · exact ht.1.ne' (hinj (h.trans β.source.symm))
      · exact ht.2.ne (hinj (h.trans β.target.symm))
    exact (K.closure_diff_V he).subset ⟨hcl, hnot⟩
  · intro x hx
    have hxcl : x ∈ range β := hrange.symm ▸ subset_closure hx
    obtain ⟨t, rfl⟩ := hxcl
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · apply unitInterval.pos_iff_ne_zero.mpr
      intro ht
      rw [ht, β.source] at hx
      exact edge_notMem_V he hx hv
    · apply unitInterval.lt_one_iff_ne_one.mpr
      intro ht
      rw [ht, β.target] at hx
      exact edge_notMem_V he hx hc

/-- A radial edge incident with the hub of a region lies in that region. -/
theorem spoke_subset_region {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : PreRad (.drawing Γ) K) {r e : Set S} (hr : r ∈ Γ.R)
    (he : e ∈ K.E) {c : S} (hc : c ∈ r) (hcV : c ∈ K.V)
    (hce : c ∈ closure e) : e ⊆ r := by
  obtain ⟨v, hv, r', hr', w, hw, hwV, hcap, her⟩ := spoke_ends hrad hS he
  have hm : c ∈ ({v, w} : Set S) := hcap ▸ ⟨hce, hcV⟩
  have hcw : c = w := by
    rcases hm with h | h
    · exact (notMem_V_of_mem_region hr hc (h.symm ▸ hv)).elim
    · exact h
  have hrr : r' = r := region_eq_of_mem hr' hr (hcw ▸ hw) hc
  exact hrr ▸ her

/-- A half-edge at the original vertex extends to an injective spoke
path to the hub. The supplied half-edge is its first half. -/
theorem exists_spoke_path_from_halfEdge {S : Type*} [TopologicalSpace S] [T2Space S]
    {K : Drawing S} {η : Set S → I → S} (hη : EdgePar K η)
    {v c : S} (i : halfEdges K η v) (hvc : v ≠ c) (hc : c ∈ K.V)
    (hcap : closure i.val.1 ∩ K.V = {v, c}) :
    ∃ β : Path v c, Function.Injective β ∧ range β = closure i.val.1 ∧
      β '' Ioo (0 : I) 1 = i.val.1 ∧ ∀ t, spoke η i.val t = β (halfT t) := by
  have hce : c ∈ closure i.val.1 := by
    have hm : c ∈ closure i.val.1 ∩ K.V := hcap.symm ▸ (Or.inr rfl)
    exact hm.1
  obtain ⟨G, hG, hGi, hG0, hG1, hGrange, hGspoke⟩ := exists_edge_path hη i hvc hc hce
  let β : Path v c := ⟨⟨G, hG⟩, hG0, hG1⟩
  have hv : v ∈ K.V := i.property.2 ▸ end_mem_V hη i.property.1 i.val.2
  exact ⟨β, hGi, hGrange,
    path_interior_image_of_edge_closure i.property.1 hcap hv hc β hGi hGrange, hGspoke⟩

/-- The sector of a positive half-edge point determines the hub end of
that radial edge. The other end is its original vertex. -/
theorem spoke_ends_of_halfEdge_point {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : PreRad (.drawing Γ) K) {η : Set S → I → S} (hη : EdgePar K η)
    {v c : S} (hv : v ∈ Γ.V) (i : halfEdges K η v)
    {r : Set S} (hr : r ∈ Γ.R) (hc : c ∈ r) (hcV : c ∈ K.V)
    {t : I} (ht : 0 < t) (htr : spoke η i.val t ∈ r) :
    closure i.val.1 ∩ K.V = {v, c} := by
  obtain ⟨v', hv', r', hr', w, hw, hwV, hcap, her⟩ := spoke_ends hrad hS i.property.1
  have hpoint : spoke η i.val t ∈ i.val.1 := spoke_mem_edge hη i.property.1 ht
  have hrr : r' = r := region_eq_of_mem hr' hr (her hpoint) htr
  subst r'
  have hwc : w = c := hub_unique hrad hr hc hcV hw hwV
  subst w
  have hvcl : v ∈ closure i.val.1 := by
    have hm := end_mem_closure hη i.property.1 i.val.2
    rw [i.property.2] at hm
    exact hm
  have hvm : v ∈ ({v', c} : Set S) := hcap ▸ ⟨hvcl, radial_V hrad hv⟩
  have hvv : v = v' := by
    rcases hvm with h | h
    · exact h
    · exact (notMem_V_of_mem_region hr hc (h ▸ hv)).elim
  exact hvv ▸ hcap

/-- Read a spoke path in the region with its initial vertex added.
The underlying parametrization, its injectivity, and its edge image are
preserved. -/
theorem exists_path_in_region_vertex {S : Type*} [TopologicalSpace S]
    {r : Set S} {v c : S} (hc : c ∈ r) (β : Path v c)
    (hβ : ∀ t, 0 < t → β t ∈ r) :
    ∃ q : Path (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)) ⟨c, Or.inl hc⟩,
      ∀ t, (q t).val = β t := by
  have hmem : ∀ t, β t ∈ r ∪ {v} := by
    intro t
    by_cases ht : t = 0
    · right
      rw [ht, β.source]
      exact mem_singleton _
    · exact Or.inl (hβ t (unitInterval.pos_iff_ne_zero.mpr ht))
  exact ⟨{
    toFun := fun t => ⟨β t, hmem t⟩
    continuous_toFun := β.continuous.subtype_mk _
    source' := Subtype.ext β.source
    target' := Subtype.ext β.target }, fun _ => rfl⟩

/-- Every positive point of a path parametrizing an edge in a region
lies in the region, provided its terminal endpoint does too. -/
theorem path_positive_in_region {S : Type*} [TopologicalSpace S]
    {r e : Set S} {v c : S} (β : Path v c) (hc : c ∈ r)
    (hinterior : β '' Ioo (0 : I) 1 = e) (her : e ⊆ r) :
    ∀ t, 0 < t → β t ∈ r := by
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1, β.target]
    exact hc
  · exact her (hinterior ▸ mem_image_of_mem β ⟨ht, unitInterval.lt_one_iff_ne_one.mpr ht1⟩)

end GraphMinor.GM12
