/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM12.Section74CornerRegions
import LeanPool.GraphMinor.GM12.Section74CornerEdges
import LeanPool.GraphMinor.GM12.Section74FiniteGluing
import LeanPool.GraphMinor.GM12.Section74LeafTwoCell
import LeanPool.GraphMinor.GM12.Section74VertexWalk
import LeanPool.GraphMinor.GM12.Section78
import LeanPool.GraphMinor.GM10.TangleLemmas
import LeanPool.GraphMinor.GM11.Section4b
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Cellularity in the base case of XII (7.4)

The first paragraph of the proof on pages 262--263 excludes a
selected normal one-vertex disc containing an edge. The sector
argument then makes the corner regions distinct. The tangle has
at least two vertices, so connectedness supplies a non-loop edge
at the deleted vertex. This edge has one half-edge there. The
cyclic order and distinct corner regions force all other edges
to have one half-edge as well. The finite gluing leaves the
chosen edge as a leaf; deleting that leaf preserves two-cellularity.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14

private theorem exists_nonloop_edge_at_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    (hpre : IsPreconnected Γ.U) {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hwv : w ≠ v) :
    ∃ (e : Set S) (u : S), e ∈ Γ.E ∧ u ∈ Γ.V ∧ u ≠ v ∧
      closure e ∩ Γ.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  obtain ⟨W⟩ := exists_walk_of_isPreconnected_U hpre hv hw
  obtain ⟨P, hP, _, _⟩ := GraphWalk.exists_isSimple W
  cases P with
  | nil _ => exact (hwv rfl).elim
  | @cons _ u _ e hl R =>
    have hvu : v ≠ u := by
      intro heq
      exact (List.nodup_cons.mp hP).1
        ((congrArg (fun x => x ∈ R.support) heq.symm).mp R.start_mem_support)
    refine ⟨e, u, hl.1, hl.2.2.1, hvu.symm, ?_, ?_⟩
    · exact hl.2.2.2.trans (pair_comm v u)
    · exact Surface.IsLineWithEnds.symm (isLine_closure hl.1 hvu hl.2.2.2)

/-- The cellularity assertion in the first paragraph of the
proof of XII (7.4), pages 262--263. It is proved by the actual
sector argument, finite edge gluing, and final leaf deletion. -/
theorem isTwoCell_delete_vertex_of_no_selected_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (hno : ∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
      ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ D) :
    (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell := by
  have hcard := hd.1.2.1.order_le_ncard_vertexSet
  change θ ≤ Γ.V.ncard at hcard
  have hother : ∃ w ∈ Γ.V, w ≠ v := by
    by_contra h
    push Not at h
    have hsub : Γ.V ⊆ {v} := fun w hw => h w hw
    have hle := ncard_le_ncard hsub (finite_singleton v)
    rw [ncard_singleton] at hle
    omega
  obtain ⟨w, hw, hwv⟩ := hother
  obtain ⟨e, u, he, _, huv, hcap, hLine⟩ := exists_nonloop_edge_at_vertex
    (isPreconnected_U_of_isTwoCell hS hd.1.1) hv hw hwv
  let : Nonempty S := ⟨v⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  obtain ⟨b, hb⟩ := exists_end_eq hγ he hv hvCap.1
  let keep : halfEdges Γ γ v := ⟨(e, b), he, hb⟩
  have hkeep : ∀ k : halfEdges Γ γ v, k.1.1 = keep.1.1 → k = keep :=
    fun k hk => halfedge_eq_of_same_nonloop_edge hγ keep k huv hcap hk
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ v)
  · obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS Γ hγ hv h2
    have hρ := corner_regions_injective_in_theorem_7_4_base hS hθ hd.1 hv hno hsec
    have hEdges := corner_edges_injective_of_single_fibre hsec.corners hρ keep hkeep
    exact isTwoCell_delete_vertex_of_corner_data hS hd.1.1 hγ hv hsec.corners hρ hEdges keep huv
      hcap hLine
  · let α := halfEdges Γ γ v
    let : Finite α := (finite_halfEdges Γ γ v).to_subtype
    let : Nonempty α := ⟨keep⟩
    have hpos : 0 < Nat.card α := Nat.card_pos
    have hOne : Nat.card α = 1 := by change ¬ 2 ≤ Nat.card α at h2; omega
    let : Subsingleton α := (Nat.card_eq_one_iff_unique.mp hOne).1
    have hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f := by
      intro f hf hfe hvf
      obtain ⟨c, hc⟩ := exists_end_eq hγ hf hv hvf
      let k : α := ⟨(f, c), hf, hc⟩
      have hk : k = keep := Subsingleton.elim _ _
      exact hfe (congrArg (fun j : α => j.1.1) hk)
    exact isTwoCell_delete_leaf hS hd.1.1 he huv hcap hLine hleaf

end GraphMinor.GM12
