/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM11.Section4b
import LeanPool.GraphMinor.GM12.Section3HomeoWalks
public import LeanPool.GraphMinor.GM12.Section3Components

/-!
# Boundary vertices and connections of feasible forests

The reduction of XII (3.1), page 245, uses a forest feasible by VII
(7.5). Forest homotopy preserves its boundary vertex set and which
boundary vertices are connected. The definition uses simple paths;
removing repeated vertices from a walk gives the same connection
relation for arbitrary walks. A homeomorphism fixing the boundary
also preserves the boundary vertex set.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM07 GM11

/-- A homeomorphism fixing the surface boundary does not change the
boundary vertex set of a drawing. -/
theorem mapDrawingHomeo_boundary_vertices {S : Type*} [TopologicalSpace S]
    (α : S ≃ₜ S) (H : Drawing S) (hfix : ∀ x ∈ bd S, α x = x) :
    (mapDrawingHomeo α H).V ∩ bd S = H.V ∩ bd S := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hxBd⟩
    have hyEq : y = x := α.injective (hyx.trans (hfix x hxBd).symm)
    exact ⟨hyEq ▸ hy, hxBd⟩
  · rintro ⟨hxV, hxBd⟩
    exact ⟨⟨x, hxV, hfix x hxBd⟩, hxBd⟩

/-- Homoplastic forests have the same boundary vertices. This is the
boundary-set part of the feasible-forest reduction in XII (3.1). -/
theorem forestsHomoplastic_boundary_vertices {S : Type*} [TopologicalSpace S]
    {H H' : Drawing S} (h : ForestsHomoplastic H H') :
    H.V ∩ bd S = H'.V ∩ bd S := by
  obtain ⟨α, hfix, hhom⟩ := h
  exact (mapDrawingHomeo_boundary_vertices α H hfix).symm.trans hhom.2.2.2.2.1

/-- Forest homotopy preserves boundary connectivity expressed by
arbitrary graph walks. The definition gives simple paths, and every
walk has a simple subwalk with the same ends. -/
theorem forestsHomotopic_walk_iff {S : Type*} [TopologicalSpace S]
    {H H' : Drawing S} (h : ForestsHomotopic H H')
    {s t : S} (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) :
    Nonempty (GraphWalk H.toGraph s t) ↔ Nonempty (GraphWalk H'.toGraph s t) := by
  classical
  have hbd := h.2.2.2.2.1
  by_cases hst : s = t
  · subst t
    have hs' : s ∈ H'.V ∩ bd S := hbd ▸ hs
    exact iff_of_true ⟨.nil hs.1⟩ ⟨.nil hs'.1⟩
  have hsimple := (h.2.2.2.2.2 s hs t ht hst).1
  constructor
  · rintro ⟨W⟩
    obtain ⟨P, hP, _, _⟩ := GraphMinor.GM11.GraphWalk.exists_isSimple W
    obtain ⟨Q, _⟩ := hsimple.mp ⟨P, hP⟩
    exact ⟨Q⟩
  · rintro ⟨W⟩
    obtain ⟨P, hP, _, _⟩ := GraphMinor.GM11.GraphWalk.exists_isSimple W
    obtain ⟨Q, _⟩ := hsimple.mpr ⟨P, hP⟩
    exact ⟨Q⟩

/-- Homoplasty preserves the boundary-connection classes of a forest,
including the boundary-fixing homeomorphism in VII's definition. -/
theorem forestsHomoplastic_walk_iff {S : Type*} [TopologicalSpace S]
    {H H' : Drawing S} (h : ForestsHomoplastic H H')
    {s t : S} (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) :
    Nonempty (GraphWalk H.toGraph s t) ↔ Nonempty (GraphWalk H'.toGraph s t) := by
  obtain ⟨α, hfix, hhom⟩ := h
  have hsmap : s ∈ (mapDrawingHomeo α H).V ∩ bd S := by
    rw [mapDrawingHomeo_boundary_vertices α H hfix]
    exact hs
  have htmap : t ∈ (mapDrawingHomeo α H).V ∩ bd S := by
    rw [mapDrawingHomeo_boundary_vertices α H hfix]
    exact ht
  have hmap := walk_mapDrawingHomeo_iff α H (x := s) (y := t)
  rw [hfix s hs.2, hfix t ht.2] at hmap
  exact hmap.symm.trans (forestsHomotopic_walk_iff hhom hsmap htmap)

/-- A feasible forest with the prescribed boundary classes supplies
the connected subdrawings in XII (3.1), page 245. Homoplasty preserves
its classes, and the component-selection theorem makes them disjoint. -/
theorem hasConnectingSubdrawings_of_feasible_forest {S : Type*} [TopologicalSpace S]
    [T1Space S] {Γ H : Drawing S} (hfeasible : IsGFeasible Γ H)
    {p : ℕ} {Zs : Fin p → Set S} (hZs : ∀ j, Zs j ⊆ H.V ∩ bd S)
    (hne : ∀ j, (Zs j).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hclasses : ∀ j, ∀ x ∈ Zs j, ∀ y ∈ H.V ∩ bd S,
      Nonempty (GraphWalk H.toGraph x y) ↔ y ∈ Zs j) :
    HasConnectingSubdrawings Γ (H.V ∩ bd S) Zs := by
  obtain ⟨H', _, hhom, hsub⟩ := hfeasible
  have hboundary := forestsHomoplastic_boundary_vertices hhom
  apply hasConnectingSubdrawings_of_connection_classes hsub
    (fun x hx => (hboundary ▸ hx).1) hZs hne hdis
  intro j x hx y hy
  exact (forestsHomoplastic_walk_iff hhom (hZs j hx) hy).symm.trans (hclasses j x hx y hy)

end GraphMinor.GM12
