/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM14.Section3

import LeanPool.GraphMinor.GM11.RadialFacts

/-!
# Radial regions relative to a zone boundary

In the planar Menger step of XVI (8.1), a radial region containing
an edge inside the zone stays inside it. A radial region containing
an edge outside the zone closure stays outside. A region crossing
the zone boundary would contain a second old edge, contrary to the
unique-edge property of radial regions.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- A radial region containing an old edge away from a zone boundary
cannot meet that boundary. This is the local separation fact used in
the radial form of the planar Menger argument in XVI (8.1). -/
theorem radial_region_disjoint_zone_boundary {H K : Drawing S}
    {d : Set S → Set S → ℕ} {γ : ℕ} {z Λ r e : Set S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hS : IsClosedSurface S)
    (hZone : IsLambdaZoneAround H d γ z Λ) (hr : r ∈ K.R) (he : e ∈ H.E)
    (heR : e ⊆ r) (heBd : Disjoint e (subBd Λ)) : Disjoint r (subBd Λ) := by
  have hFacts := regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 ⟨e, he⟩
  apply disjoint_left.mpr
  intro x hxr hxbd
  have hxNotHV : x ∉ H.V := fun hxV => region_subset hr hxr (K.V_subset_U (hK.2.1.2.1 hxV))
  obtain ⟨f, hf, hxf⟩ := H.exists_edge_of_mem (hZone.bd_subset_U hxbd) hxNotHV
  have hfK : Disjoint f K.U := by
    apply disjoint_left.mpr
    intro p hpf hpK
    have hU : H.U ∩ K.U = H.V := hK.2.1.1
    have hpHV : p ∈ H.V := hU ▸ ⟨(hf.2.1 hpf).1, hpK⟩
    exact (hf.2.1 hpf).2 hpHV
  have hfR : f ⊆ r := subset_region hr hf.2.2.1.isConnected.isPreconnected hfK hxf hxr
  have hef : e = f := hFacts.2.1 r hr e he f hf heR hfR
  exact heBd.notMem_of_mem_left (hef.symm ▸ hxf) hxbd

/-- An edge inside a zone has its entire radial region inside that zone. -/
theorem radial_region_subset_zone {H K : Drawing S}
    {d : Set S → Set S → ℕ} {γ : ℕ} {z Λ r e : Set S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hS : IsClosedSurface S)
    (hZone : IsLambdaZoneAround H d γ z Λ) (hr : r ∈ K.R) (he : e ∈ H.E)
    (heR : e ⊆ r) (heΛ : e ⊆ Λ) : r ⊆ Λ := by
  have hΛBd := (isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1).1
  have hrBd := radial_region_disjoint_zone_boundary hK hS hZone hr he heR
    (hΛBd.mono heΛ Subset.rfl)
  have hrFr : Disjoint r (frontier (closure Λ)) := hrBd.mono_right (by
    rw [subBd_eq_frontier]; exact frontier_closure_subset)
  obtain ⟨x, hxe⟩ := he.1
  have hrCl : r ⊆ closure Λ :=
    (subset_or_disjoint_of_frontier isClosed_closure (region_isPreconnected hr) hrFr).resolve_right
      (fun hd => hd.notMem_of_mem_left (heR hxe) (subset_closure (heΛ hxe)))
  intro x hxr
  obtain ⟨_, hcl⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  have hx := hrCl hxr
  rw [hcl] at hx
  exact hx.resolve_right (hrBd.notMem_of_mem_left hxr)

/-- An edge outside a zone closure has its radial region outside it. -/
theorem radial_region_disjoint_zone_closure {H K : Drawing S}
    {d : Set S → Set S → ℕ} {γ : ℕ} {z Λ r e : Set S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hS : IsClosedSurface S)
    (hZone : IsLambdaZoneAround H d γ z Λ) (hr : r ∈ K.R) (he : e ∈ H.E)
    (heR : e ⊆ r) (heΛ : Disjoint e (closure Λ)) : Disjoint r (closure Λ) := by
  have hrBd := radial_region_disjoint_zone_boundary hK hS hZone hr he heR
    (heΛ.mono_right (fun _ h => h.1))
  have hrFr : Disjoint r (frontier (closure Λ)) := hrBd.mono_right (by
    rw [subBd_eq_frontier]; exact frontier_closure_subset)
  obtain ⟨x, hxe⟩ := he.1
  exact (subset_or_disjoint_of_frontier isClosed_closure (region_isPreconnected hr)
    hrFr).resolve_left
    (fun hsub => heΛ.notMem_of_mem_left hxe (hsub (heR hxe)))

end GraphMinor.GM16
