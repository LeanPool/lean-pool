/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73PreRadialContraction
public import LeanPool.GraphMinor.GM12.Section73WalkLift
import LeanPool.GraphMinor.GM12.Section73RadialMaximal

/-!
# The radial drawing and lifted walks after deletion

This assembles the radial-star construction of XII (7.3), page 261.
Contract the spokes at the deleted vertex, remove empty parallel
bigons, and verify global maximality. Each closed walk in the new
radial drawing lifts to the old one with the stated length increase
and with the same point set outside the merged region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The radial-star construction and lifted walks in XII (7.3),
page 261, when the deleted drawing has an edge. The endpoint case
of order two is handled by `theorem_7_3_order_two`. -/
theorem exists_radial_star_contraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    ∃ (f : C(S, S)) (H J : Drawing S), Function.Surjective f ∧
      (∀ x ∉ r', f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} ∧
      J.IsSubdrawing H ∧ J.V = H.V ∧
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J ∧
      (∀ (a : S) (W : GraphWalk J.toGraph a a),
        ∃ W' : GraphWalk K.toGraph a a,
          W'.length = W.length + 2 * walkVertexCount v W ∧
          f '' (walkDrawing K W').U = (walkDrawing J W).U ∧
          (walkDrawing K W').U \ r' = (walkDrawing J W).U \ r') := by
  obtain ⟨f, H, J, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE,
      hJH, hJV, hJtwo, hJpre, hJface⟩ :=
    exists_cleaned_radial_star_contraction hS hK hE hv hunique hr' hvr'
  have hJrad := isRadial_of_twoCell_unique_edges hS htwo hE' hJpre hJtwo hJface
  refine ⟨f, H, J, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE, hJH, hJV, hJrad, ?_⟩
  intro a W
  have hJV' : J.V = f '' K.V := hJV.trans hHV
  have hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} := fun _ he =>
    hHE ▸ hJH.2 he
  exact exists_closed_walk_lift hS hK hE hv hr' hvr' f hfix hcollapse hfibre hJV' hJE hJpre W

end GraphMinor.GM12
