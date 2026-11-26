/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM16.Section9RadialRegions
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks

import LeanPool.GraphMinor.GM11.RadialFacts

/-!
# The radial boundary of an annular separation

The separator in XVI (8.1), Claim (10), separates the inner disc
from the outside of the battlefield. Mark the radial regions that
contain edges on its inner side. Their boundary stays in the outer
disc closure and misses the inner open disc. Both assertions follow
by looking at an incident radial region on the appropriate side.
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- The boundary drawing of a family of regions lies in every closed
set containing those regions. -/
theorem boundaryDrawing_U_subset_closed (hS : IsClosedSurface S) (K : Drawing S)
    {Z : Set (Set S)} {A : Set S} (hA : IsClosed A)
    (hZA : ∀ r ∈ Z, r ⊆ A) : (boundaryDrawing K Z).U ⊆ A := by
  have hV : (boundaryDrawing K Z).V ⊆ A := by
    intro x hx
    obtain ⟨⟨r, hrZ, hxr⟩, _⟩ := (mem_boundaryDrawing_V hS).mp hx
    exact closure_minimal (hZA r hrZ) hA hxr.2.2
  have hE : ∀ e ∈ (boundaryDrawing K Z).E, closure e ⊆ A := by
    intro e he
    obtain ⟨⟨r, hrZ, hir⟩, _⟩ := mem_boundaryDrawing_E.mp he
    have heR := edge_subset_closure_of_incident hS hir.1 hir.2.1 hir.2.2
    have heA : e ⊆ A := heR.trans (closure_minimal (hZA r hrZ) hA)
    exact closure_minimal heA hA
  rw [(boundaryDrawing K Z).U_eq]
  exact union_subset hV (iUnion₂_subset hE)

omit [T2Space S] [ConnectedSpace S] in
/-- An old edge is contained in a region of its radial drawing. -/
theorem radial_region_of_edge {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {e : Set S} (he : e ∈ H.E) :
    ∃ r ∈ K.R, e ⊆ r := by
  obtain ⟨x, hxe⟩ := he.1
  have hDis : Disjoint e K.U := by
    apply disjoint_left.mpr
    intro p hpe hpK
    have hEq : H.U ∩ K.U = H.V := hK.2.1.1
    exact (he.2.1 hpe).2 (hEq ▸ ⟨(he.2.1 hpe).1, hpK⟩)
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (hDis.notMem_of_mem_left hxe)
  exact ⟨r, hr, subset_region hr he.2.2.1.isConnected.isPreconnected hDis hxe hxr⟩

/-- The radial boundary of an inner separation side stays inside the
outer zone closure and outside the inner open zone. These are the
geometric conditions in the planar Menger step of XVI (8.1). -/
theorem radial_boundary_in_annulus (hS : IsClosedSurface S)
    {H K : Drawing S} {d : Set S → Set S → ℕ} {γ γ' : ℕ}
    {z Λ M : Set S} {A B : Hypergraph S (Set S)}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    (hE : H.E.Nonempty)
    (hΛ : IsLambdaZoneAround H d γ z Λ) (hM : IsLambdaZoneAround H d γ' z M)
    (hSep : H.toHypergraph.IsSeparation A B)
    (hOuter : ∀ e ∈ A.edgeSet, e ⊆ Λ)
    (hInner : ∀ e ∈ H.E, e ⊆ closure M → e ∈ A.edgeSet) :
    (boundaryDrawing K (PaintingOrDrawing.regionsIncludingEdge K A)).U ⊆ closure Λ ∧
    Disjoint (boundaryDrawing K (PaintingOrDrawing.regionsIncludingEdge K A)).U M := by
  have hFacts := regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  let ZA := PaintingOrDrawing.regionsIncludingEdge K A
  let ZB := PaintingOrDrawing.regionsIncludingEdge K B
  have hZA : ∀ r ∈ ZA, r ⊆ closure Λ := by
    rintro r ⟨hr, e, heA, heR⟩
    have heH : e ∈ H.E := hSep.left_le.2 heA
    exact (radial_region_subset_zone hK hS hΛ hr heH heR (hOuter e heA)).trans subset_closure
  have hZB : ∀ r ∈ ZB, r ⊆ univ \ M := by
    rintro r ⟨hr, e, heB, heR⟩
    have heH : e ∈ H.E := hSep.right_le.2 heB
    have heDis : Disjoint e (closure M) := by
      apply disjoint_left.mpr
      intro x hxe hxM
      have heCl := zone_atom_subset_closure hM (Or.inl (Or.inr heH)) ⟨x, hxe, hxM⟩
      exact hSep.notMem_edgeSet_right (hInner e heH heCl) heB
    have hrDis := radial_region_disjoint_zone_closure hK hS hM hr heH heR heDis
    exact fun x hx => ⟨mem_univ _, fun hxM => hrDis.notMem_of_mem_left hx (subset_closure hxM)⟩
  refine ⟨boundaryDrawing_U_subset_closed hS K isClosed_closure hZA, ?_⟩
  have hZA_R : ZA ⊆ K.R := fun _ h => h.1
  have hComp : K.R \ ZA = ZB := compl_regions hFacts hSep
  have hEq : boundaryDrawing K ZA = boundaryDrawing K ZB := by
    rw [← hComp]
    exact (boundaryDrawing_compl hZA_R).symm
  have hOut := boundaryDrawing_U_subset_closed hS K
    (isClosed_univ.sdiff hM.isOpenDisc.1) hZB
  rw [← hEq] at hOut
  exact disjoint_left.mpr fun x hxN hxM => (hOut hxN).2 hxM

end GraphMinor.GM16
