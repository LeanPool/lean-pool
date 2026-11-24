/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DerivedContraction
public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution
public import LeanPool.GraphMinor.GM12.SurfaceDualContractDefs
import LeanPool.GraphMinor.GM12.Section73SupportedRadialContraction
import LeanPool.GraphMinor.GM12.Section73WalkLiftEdges
import LeanPool.GraphMinor.GM12.Section73WalkInside
import LeanPool.GraphMinor.GM12.Section73HubInside
import LeanPool.GraphMinor.GM12.Section73Representativity
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.Theorem61

/-!
# Constructing the new metric with the walk inside comparisons

For XII (7.3), pages 261--262, choose the supported radial star
collapse and clean its image. Prove representativity of the new
drawing and respectfulness of the deleted tangle, then derive
its inside function and metric. Each short new walk now has an
actual old lift with the stated length, inside containment, and
preservation of the enclosed merged hub. No walk-comparison step
is assumed in this construction.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- Construct the supported radial star contraction, the new radial
metric, and the lifted-walk inside comparisons used for both bounds
of XII (7.3), pages 261--262, exposing `(D, f, H, J)` as an
`IsStarContraction`. -/
theorem exists_starContraction_with_vertex_deletion_walk_comparison
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    {ins : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    ∃ (D : Set S) (f : C(S, S)) (H J : Drawing S) (ins' : Drawing S → Set S),
      IsStarContraction K v r' D f H J ∧
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J ∧
      IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins' ∧
      HasTangleMetric (deleteVertices Γ {v}) (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ)
        (tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1)) ∧ v ∈ J.V ∧
      ∀ (a : S) (W : GraphWalk J.toGraph a a), W.length < 2 * (θ - 1) →
        ∃ W' : GraphWalk K.toGraph a a,
          W'.length = W.length + 2 * walkVertexCount v W ∧
          insWalk ins' J W ⊆ insWalk ins K W' ∪ r' ∧
          (v ∈ insWalk ins' J W → v ∈ insWalk ins K W') := by
  obtain ⟨B, f, H, J, hB, hBr, hAB, hsurj, hfixB, hfix, hcollapse, hfibre,
      hHU, hHV, hHE, hJH, hJV, hJ⟩ :=
    exists_supported_radial_star_contraction hS hK hE hv htwo hE' hunique hr' hvr'
  have hc : IsStarContraction K v r' B f H J :=
    ⟨hB, hBr, hfixB, hcollapse, hfibre, hHU, hHV, hJH, hJV⟩
  have hpret : IsPretangle Γ.toHypergraph θ T :=
    ⟨hT.2.1.one_le, hT.2.1.isSeparation, hT.2.1.order_lt, hT.2.1.axiom1, hT.2.1.axiom2⟩
  have hs := GM14.isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γ) (Γ'
    := K) hS hpret hK.2.1.1 hins
  have hJV' : J.V = f '' K.V := hJV.trans hHV
  have hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} := fun _ he =>
    hHE ▸ hJH.2 he
  have hrep := isRepresentative_of_radial_star_contraction hS hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV' hJE hJ.2.1 hs hJ hE'
  have hresp := isRespectful_after_vertex_deletion_of_representative hS hθ hT hv htwo hrep
  obtain ⟨ins', hins'⟩ := exists_derivedSlope hS hresp.2.2 hJ.2.1
  have hm : HasTangleMetric (deleteVertices Γ {v}) (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ)
      (tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1)) :=
    ⟨hresp, J, ins', hJ, hins', fun _ _ _ _ => rfl⟩
  have hvJ : v ∈ J.V := hJV'.symm ▸ ⟨v, hK.2.1.2.1 hv, hcollapse v (Or.inl rfl)⟩
  refine ⟨B, f, H, J, ins', hc, hJ, hins', hm, hvJ, ?_⟩
  intro a W hshort
  obtain ⟨W', hlen, _, hpoints, hedges⟩ := exists_closed_walk_lift_with_edges hS hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV' hJE hJ.2.1 hunique W
  refine ⟨W', hlen, ?_, ?_⟩
  · exact theorem_7_3_claim_1_short_walk hS hθ hT.2.1 hins hins' hK hE hv hr' hvr'
      f hfix hcollapse hfibre hJV' hJE hJ hB hBr hAB hfixB W W' hshort hpoints hedges
  · exact hub_mem_inside_lifted_walk hS hθ hT.2.1 hins hins' hK hE hv hr' hvr'
      f hfix hcollapse hfibre hJV' hJE hJ W W' hshort hpoints hedges

/-- Construct the new radial metric and the lifted-walk inside
comparisons used for both bounds of XII (7.3), pages 261--262.
The only local reduction condition is uniqueness of the old star
spokes, which is supplied by the selected-disc reduction. -/
theorem exists_metric_with_vertex_deletion_walk_comparison
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    {ins : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    ∃ (J : Drawing S) (ins' : Drawing S → Set S),
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J ∧
      IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins' ∧
      HasTangleMetric (deleteVertices Γ {v}) (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ)
        (tangleMetric (deleteVertices Γ {v}) J ins' (θ - 1)) ∧ v ∈ J.V ∧
      ∀ (a : S) (W : GraphWalk J.toGraph a a), W.length < 2 * (θ - 1) →
        ∃ W' : GraphWalk K.toGraph a a,
          W'.length = W.length + 2 * walkVertexCount v W ∧
          insWalk ins' J W ⊆ insWalk ins K W' ∪ r' ∧
          (v ∈ insWalk ins' J W → v ∈ insWalk ins K W') := by
  obtain ⟨_, _, _, J, ins', _, hJ, hins', hm, hvJ, hcomp⟩ :=
    exists_starContraction_with_vertex_deletion_walk_comparison
      hS hθ hT hins hK hE hv htwo hE' hunique hr' hvr'
  exact ⟨J, ins', hJ, hins', hm, hvJ, hcomp⟩

end GraphMinor.GM12
