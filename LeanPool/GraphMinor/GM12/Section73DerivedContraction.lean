/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RadialContraction
public import LeanPool.GraphMinor.GM12.Section73Respectfulness
import LeanPool.GraphMinor.GM12.Section73Representativity
import LeanPool.GraphMinor.GM14.DiscSlope
import LeanPool.GraphMinor.GM11.Theorem61

/-!
# The derived inside function after radial star contraction

For XII (7.3), page 261, construct the radial drawing after
vertex deletion, prove representativity with the lifted short
walks, and select the discs of the deleted tangle. Its derived
inside function then exists for this same radial drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- The radial construction in XII (7.3), page 261, together with
respectfulness and the new derived inside function. The geometric
contraction and the old inside function supply all the hypotheses
of the representativity proof. -/
theorem exists_derivedSlope_after_radial_star_contraction
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
    ∃ (f : C(S, S)) (H J : Drawing S) (ins' : Drawing S → Set S), Function.Surjective f ∧
      (∀ x ∉ r', f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} ∧
      J.IsSubdrawing H ∧ J.V = H.V ∧
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J ∧
      IsRespectfulDrawingTangle (deleteVertices Γ {v}) (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ) ∧
      IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
        (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins' ∧
      (∀ (a : S) (W : GraphWalk J.toGraph a a),
        ∃ W' : GraphWalk K.toGraph a a,
          W'.length = W.length + 2 * walkVertexCount v W ∧
          f '' (walkDrawing K W').U = (walkDrawing J W).U ∧
          (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r') := by
  obtain ⟨f, H, J, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE, hJH, hJV, hJrad, hlift⟩ :=
    exists_radial_star_contraction hS hK hE hv htwo hE' hunique hr' hvr'
  have hpret : IsPretangle Γ.toHypergraph θ T :=
    ⟨hT.2.1.one_le, hT.2.1.isSeparation, hT.2.1.order_lt, hT.2.1.axiom1, hT.2.1.axiom2⟩
  have hs := GM14.isSlope_of_derived (Γ := PaintingOrDrawing.drawing Γ) (Γ'
    := K) hS hpret hK.2.1.1 hins
  have hJV' : J.V = f '' K.V := hJV.trans hHV
  have hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} := fun _ he =>
    hHE ▸ hJH.2 he
  have hrep := isRepresentative_of_radial_star_contraction hS hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV' hJE hJrad.2.1 hs hJrad hE'
  have hresp := isRespectful_after_vertex_deletion_of_representative hS hθ hT hv htwo hrep
  obtain ⟨ins', hins'⟩ := exists_derivedSlope hS hresp.2.2 hJrad.2.1
  exact ⟨f, H, J, ins', hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE, hJH, hJV,
    hJrad, hresp, hins', hlift⟩

end GraphMinor.GM12
