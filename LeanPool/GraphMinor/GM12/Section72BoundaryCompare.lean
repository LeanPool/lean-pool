/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2InsideHomotopy
public import LeanPool.GraphMinor.GM12.Section2NormalNoncover
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM07.Section11c

/-!
# A region deformation preserves the drawing inside the boundary

In XII (7.2), page 260, replacing the boundary by its two-spoke circle
leaves the part of the original drawing in the selected disc unchanged.
The deformation uses only the region and its boundary vertex. Away
from that vertex it avoids every drawing point. A point outside both
selected discs supplies the second omitted point for the inside
comparison from (2.1).
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

/-- Equal intersections with the point set of a drawing give equal
intersection hypergraphs, including all incidence data. -/
theorem inter_eq_of_drawing_inter_eq
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {D E : Set S}
    (h : Γ.U ∩ D = Γ.U ∩ E) :
    (PaintingOrDrawing.drawing Γ).inter D = (PaintingOrDrawing.drawing Γ).inter E := by
  have hx : ∀ x ∈ Γ.U, x ∈ D ↔ x ∈ E := by
    intro x hx
    exact ⟨fun hD => (h.subset ⟨hx, hD⟩).2,
      fun hE => (h.superset ⟨hx, hE⟩).2⟩
  have he : ∀ e ∈ Γ.E, e ⊆ D ↔ e ⊆ E := by
    intro e he
    exact ⟨fun hs x hxe => (hx x (he.2.1 hxe).1).mp (hs hxe),
      fun hs x hxe => (hx x (he.2.1 hxe).1).mpr (hs hxe)⟩
  apply Hypergraph.ext
  · ext x
    change (x ∈ Γ.V ∧ x ∈ D) ↔ x ∈ Γ.V ∧ x ∈ E
    exact and_congr_right (fun hv => hx x (Γ.V_subset_U hv))
  · ext e
    change (e ∈ Γ.E ∧ e ⊆ D) ↔ e ∈ Γ.E ∧ e ⊆ E
    exact and_congr_right (he e)
  · funext e x
    apply propext
    change (Γ.toHypergraph.Inc e x ∧ e ⊆ D ∧ x ∈ D) ↔
      Γ.toHypergraph.Inc e x ∧ e ⊆ E ∧ x ∈ E
    apply and_congr_right
    intro hi
    exact and_congr (he e hi.1) (hx x (Γ.V_subset_U hi.2.1))

/-- Equality on drawing points and on boundary points also preserves
intersection with the closed outside. -/
theorem drawing_inter_outside_eq_of_boundary_eq
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {D E : Set S}
    (h : Γ.U ∩ D = Γ.U ∩ E)
    (hb : Γ.U ∩ frontier D = Γ.U ∩ frontier E) :
    Γ.U ∩ closure (univ \ D) = Γ.U ∩ closure (univ \ E) := by
  have hx : ∀ x ∈ Γ.U, x ∈ D ↔ x ∈ E := by
    intro x hx
    exact ⟨fun hD => (h.subset ⟨hx, hD⟩).2,
      fun hE => (h.superset ⟨hx, hE⟩).2⟩
  have hbx : ∀ x ∈ Γ.U, x ∈ frontier D ↔ x ∈ frontier E := by
    intro x hx
    exact ⟨fun hD => (hb.subset ⟨hx, hD⟩).2,
      fun hE => (hb.superset ⟨hx, hE⟩).2⟩
  have hint : ∀ x ∈ Γ.U, x ∈ interior D ↔ x ∈ interior E := by
    intro x hxU
    have hd := hx x hxU
    have hb' := hbx x hxU
    constructor
    · intro hxD
      have hxE := hd.mp (interior_subset hxD)
      by_contra hxEi
      have hfrontE : x ∈ frontier E := ⟨subset_closure hxE, hxEi⟩
      exact ((hb'.mpr hfrontE).2) hxD
    · intro hxE
      have hxD := hd.mpr (interior_subset hxE)
      by_contra hxDi
      have hfrontD : x ∈ frontier D := ⟨subset_closure hxD, hxDi⟩
      exact ((hb'.mp hfrontD).2) hxE
  simp only [← compl_eq_univ_sdiff, closure_compl]
  ext x
  exact and_congr_right (fun hxU => not_congr (hint x hxU))

/-- The equality of drawing points inside two selected boundary discs
in the single-region deformation of XII (7.2), page 260. -/
theorem drawing_inter_disc_eq_of_region_deformation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    {φ ψ : C(Circle, S)} (hφ : IsEmbedding φ) (hψ : IsEmbedding ψ)
    {r D E : Set S} {v : S} (hr : r ∈ Γ.R)
    (hvφ : v ∈ range φ) (hvψ : v ∈ range ψ)
    (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbdD : subBd D = range φ) (hbdE : subBd E = range ψ)
    (hnφ : Γ.IsNormal (range φ)) (hnψ : Γ.IsNormal (range ψ))
    (hmD : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hmE : ((PaintingOrDrawing.drawing Γ).inter E,
      (PaintingOrDrawing.drawing Γ).interOutside E) ∈ T)
    (hh : ClosedCurvesHomotopicIn (r ∪ {v}) φ ψ) :
    Γ.U ∩ D = Γ.U ∩ E := by
  have hnDf : (PaintingOrDrawing.drawing Γ).IsNormal (frontier D) := by
    rw [← subBd_eq_frontier, hbdD]
    exact hnφ
  have hnEf : (PaintingOrDrawing.drawing Γ).IsNormal (frontier E) := by
    rw [← subBd_eq_frontier, hbdE]
    exact hnψ
  obtain ⟨q, hqΓ, hqD, hqE⟩ := exists_support_point_outside_two_small_sides
    (Γ := .drawing Γ) hT hD.isCompact.isClosed hE.isCompact.isClosed hnDf hnEf hmD hmE
  have hvD : v ∈ D := hD.isCompact.isClosed.closure_subset_iff.mpr subset_rfl
    ((hbdD.symm ▸ hvφ).1)
  have hvE : v ∈ E := hE.isCompact.isClosed.closure_subset_iff.mpr subset_rfl
    ((hbdE.symm ▸ hvψ).1)
  have hqZ : q ∉ r ∪ {v} := by
    rintro (hqr | hqv)
    · exact region_subset hr hqr hqΓ
    · exact hqD (mem_singleton_iff.mp hqv ▸ hvD)
  have hmem : ∀ x ∈ Γ.U, x ∈ D ↔ x ∈ E := by
    intro x hx
    by_cases hxv : x = v
    · subst x
      exact iff_of_true hvD hvE
    · have hZpair : r ∪ {v} ⊆ ({x, q} : Set S)ᶜ := by
        intro y hy hpair
        rcases hpair with hyx | hyq
        · subst y
          rcases hy with hxr | hxv'
          · exact region_subset hr hxr hx
          · exact hxv hxv'
        · exact hqZ (hyq ▸ hy)
      exact mem_disc_iff_of_boundary_homotopy hS hφ hψ hD hE hbdD hbdE hqD hqE
        (hh.mono hZpair)
  ext x
  exact and_congr_right (hmem x)

end GraphMinor.GM12
