/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73OldSpoke
import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.GM12.Section73RadialStarDrawing

/-!
# Edges forced into a two-edge spoke lift

For XII (7.3), Claim (1), page 262, a surviving old spoke must
occur in any walk whose collapsed image contains its new edge.
Its interior misses the collapsed star, so each interior point
has a unique preimage. A two-edge lift from the deleted vertex
then also uses the unique star spoke to the old region hub.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A surviving old edge occurs in a lifted walk if its image is
contained in the walk's image. Its interior has singleton fibres
under the star collapse. This supplies the surviving spoke in
XII (7.3), Claim (1), page 262. -/
theorem old_edge_mem_lift_of_image
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    {g : Set S} (hg : g ∈ K.E) (hvg : v ∉ closure g)
    (f : S → S)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    {a b : S} (W : GraphWalk K.toGraph a b)
    (himage : f '' g ⊆ f '' (walkDrawing K W).U) : g ∈ W.edges := by
  obtain ⟨x, hxg⟩ := hg.1
  have hxnot : x ∉ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e := by
    intro hxA
    exact (hg.2.1 hxg).2
      ((radial_edge_inter_star hS hK hv hg hvg).2 ⟨subset_closure hxg, hxA⟩)
  obtain ⟨y, hy, hfy⟩ := himage ⟨x, hxg, rfl⟩
  have hxy : x = y := ((hfibre x y).mp hfy.symm).resolve_right (fun h => hxnot h.1)
  have hxW : x ∈ (walkDrawing K W).U := hxy.symm ▸ hy
  have hgW : g ∈ (walkDrawing K W).E := by
    by_contra hgnot
    exact disjoint_left.mp (edge_disjoint_U (walkDrawing_isSubdrawing K W) hg hgnot) hxg hxW
  rw [walkDrawing_E] at hgW
  exact hgW

/-- A two-edge lift from the deleted vertex uses the unique star
edge to the middle vertex of its surviving spoke. This records
the other edge of each replacement path in XII (7.3), Claim (1). -/
theorem star_edge_mem_two_edge_lift
    {S : Type*} [TopologicalSpace S] {K : Drawing S} {v x u : S} {g k : Set S}
    (hkg : K.toGraph.IsLink g u x) (hvg : v ∉ closure g)
    (hunique : ∀ e ∈ K.E, K.toGraph.IsLink e v u → e = k)
    (W : GraphWalk K.toGraph v x) (hlen : W.length = 2) (hgW : g ∈ W.edges) :
    k ∈ W.edges := by
  cases hcase : W with
  | nil h => rw [hcase, GraphWalk.length_nil] at hlen; omega
  | @cons _ y _ e he R =>
    cases hR : R with
    | nil h => rw [hcase, hR, GraphWalk.length_cons, GraphWalk.length_nil] at hlen; omega
    | @cons _ z _ f hf Q =>
      cases hQ : Q with
      | nil h =>
        rw [hcase, hR, hQ] at hgW
        have hgcases : g = e ∨ g = f := by
          simpa only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_cons,
            List.not_mem_nil, or_false] using hgW
        rcases hgcases with hge | hgf
        · have he' : K.toGraph.IsLink g v y := hge.symm ▸ he
          exact (hvg (he'.2.2.2.superset (Or.inl rfl)).1).elim
        · have hf' : K.toGraph.IsLink g y x := hgf.symm ▸ hf
          have hyu : y = u := hf'.left_unique hkg
          have hek : e = k := hunique e he.1 (hyu ▸ he)
          exact List.mem_cons.mpr (Or.inl hek.symm)
      | cons h R' =>
        rw [hcase, hR, hQ, GraphWalk.length_cons, GraphWalk.length_cons,
          GraphWalk.length_cons] at hlen
        omega

end GraphMinor.GM12
