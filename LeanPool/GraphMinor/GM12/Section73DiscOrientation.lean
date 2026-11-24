/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73Tangle
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Theorem64
import LeanPool.GraphMinor.GM11.Theorem61
import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Orienting a disc separation after vertex deletion

In XII (7.3), page 261, a disc bounded by a short normal circle in
the deleted drawing must have its inside on the small side. Otherwise
an old tangle member lifts the reverse orientation. XI (6.4) gives a
non-null circle in its large side avoiding the separator. This circle
avoids the deleted vertex and every edge incident with it, so it lies
in the new inside disc, a contradiction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- A circle in a drawing that avoids a vertex survives deletion of
that vertex, including all its edge points. This is the survival step
in the respectful-tangle argument of XII (7.3), page 261. -/
theorem oArc_subset_underlying_delete_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {Γ : Drawing S} {A : Hypergraph S (Set S)} (hA : A ≤ Γ.toHypergraph)
    {F : Set S} {v : S} (hF : IsOArc F) (hFA : F ⊆ PaintingOrDrawing.underlying A)
    (hvF : v ∉ F) : F ⊆ PaintingOrDrawing.underlying (A.deleteVertices {v}) := by
  have hFΓ : F ⊆ Γ.U := by
    intro x hx
    rcases hFA hx with hxA | ⟨e, he, hxe⟩
    · exact Γ.V_subset_U (hA.vertexSet_subset hxA)
    · exact ((hA.edgeSet_subset he).2.1 hxe).1
  intro x hxF
  rcases hFA hxF with hxA | ⟨e, he, hxe⟩
  · exact Or.inl ⟨hxA, fun hxv => hvF (mem_singleton_iff.mp hxv ▸ hxF)⟩
  · have heΓ : e ∈ Γ.E := hA.edgeSet_subset he
    have heF : e ⊆ F := edge_subset_of_oArc hF hFΓ heΓ ⟨x, hxe, hxF⟩
    have hno : ∀ w ∈ ({v} : Set S), ¬ A.Inc e w := by
      intro w hw hi
      have hwcl : w ∈ closure e := (inc_of_le hA hi).2.2
      have hwF : w ∈ F := closure_minimal heF (isCompact_of_isOArc hF).isClosed hwcl
      exact hvF (mem_singleton_iff.mp hw ▸ hwF)
    exact Or.inr ⟨e, ⟨he, hno⟩, hxe⟩

/-- The disc orientation in XII (7.3), page 261, on a surface other
than the sphere. Every short normal circle that bounds a disc has
that disc selected by the deleted-vertex tangle. -/
theorem disc_orientation_after_vertex_deletion
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T) {v : S} (hv : v ∈ Γ.V)
    {D : Set S} (hD : IsClosedDisc D)
    (hn : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsNormal (frontier D))
    (hcard : (frontier D ∩ (deleteVertices Γ {v}).V).ncard < θ - 1) :
    ((PaintingOrDrawing.drawing (deleteVertices Γ {v})).inter D,
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).interOutside D) ∈
        deleteVerticesTangle Γ.toHypergraph {v} T θ := by
  let Γ' := deleteVertices Γ {v}
  let A' := (PaintingOrDrawing.drawing Γ').inter D
  let B' := (PaintingOrDrawing.drawing Γ').interOutside D
  have hnew := theorem_7_3_tangle hθ hT.2.1 hv
  have hsep : Γ'.toHypergraph.IsSeparation A' B' := isSeparation_inter hD.isClosed hn
  have hord : separationOrder A' B' < θ - 1 := by
    apply lt_of_le_of_lt _ hcard
    exact ncard_le_ncard (fun x hx => inter_outside_subset hx)
      (Γ'.finite_V.subset inter_subset_right)
  apply (hnew.axiom1 hsep hord).resolve_right
  intro hrev
  obtain ⟨⟨A, B⟩, hm, hvAB, hAdel, hBdel⟩ := hrev.2.2
  have hpret : IsPretangle Γ.toHypergraph θ T :=
    ⟨hT.2.1.one_le, hT.2.1.isSeparation, hT.2.1.order_lt, hT.2.1.axiom1, hT.2.1.axiom2⟩
  have hsepOld := hT.2.1.isSeparation hm
  have hordOld := hT.2.1.order_lt hm
  obtain ⟨F, hF, hFB, hnon⟩ :=
    ((GM11.theorem_6_4_proof hS hns hT.1 hpret hT.2.2).1 A B hsepOld hordOld).2.mp hm
  have hvA : v ∈ A.vertexSet := (hvAB (mem_singleton v)).1
  have hvF : v ∉ F := fun hvF => (hFB hvF).2 (Or.inl hvA)
  have hsurvive := oArc_subset_underlying_delete_vertex hsepOld.right_le hF
    (hFB.trans sdiff_subset) hvF
  rw [hBdel] at hsurvive
  have hFD : F ⊆ D := by
    intro x hx
    rcases hsurvive hx with hxA | ⟨e, he, hxe⟩
    · exact hxA.2
    · exact he.2 hxe
  exact hnon (isNullHomotopicOArcIn_of_subset_disc hF (subset_univ D) hD hFD)

end GraphMinor.GM12
