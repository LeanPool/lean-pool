/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallModel
public import LeanPool.GraphMinor.GM16.HypergraphImageTangle
public import LeanPool.GraphMinor.GM10.Defs2
import LeanPool.GraphMinor.GM16.ModelContractionMaps
import LeanPool.GraphMinor.GM16.GraphIsoImage
import LeanPool.GraphMinor.GM10.Section6
import LeanPool.GraphMinor.GM10.Section7

/-!
# The grid-induced tangle in the wall

In Claim (1) of XVI (4.2), page 53, contract the horizontal pairs of
the wall to obtain a square grid. X (7.3) supplies its tangle. Relabel
that tangle by the actual contraction maps, then apply X (6.1) to
induce a tangle of the same order in the wall. All the maps remain
explicit, so the chosen row edges can be compared in the next step.
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GM10

/-- The contracted pair sets distinguish the grid vertices. -/
theorem sphereWallPair_injective (θ : ℕ) : Function.Injective (sphereWallPair θ) := by
  intro u v heq
  by_contra hne
  have hx : sphereWallPairVertex θ u 0 ∈ sphereWallPair θ u := mem_insert _ _
  have hy : sphereWallPairVertex θ u 0 ∈ sphereWallPair θ v := heq ▸ hx
  exact (disjoint_left.mp (sphereWallPair_disjoint hne)) hx hy

/-- The induced tangle construction in XVI (4.2), Claim (1), page 53.
The literal minor has the given pair sets and chosen edge names. -/
theorem exists_induced_wall_tangle (θ : ℕ) (hθ : 2 ≤ θ) :
    ∃ (N₂ : Graph (Set (Fin (2 * θ + 1) × Fin θ))
        (Sym2 (Fin (2 * θ + 1) × Fin θ)))
      (hV₂ : V(N₂).Finite) (hE₂ : E(N₂).Finite),
      IsMinor N₂ (sphereWallGraph θ) ∧
      Hypergraph.ofGraph N₂ hV₂ hE₂ = imageHypergraph (sphereWallPair θ)
        (sphereWallGridEdge θ) (gridHypergraph θ) ∧
      IsTangle (Hypergraph.ofGraph N₂ hV₂ hE₂) θ
        (imageHypergraphTangle (sphereWallPair θ) (sphereWallGridEdge θ) (gridTangle θ)) ∧
      IsTangle (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _)) θ
        (inducedTangle (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _))
          (Hypergraph.ofGraph N₂ hV₂ hE₂)
          (imageHypergraphTangle (sphereWallPair θ) (sphereWallGridEdge θ) (gridTangle θ)) θ) := by
  classical
  obtain ⟨G', hG', C, hC, φ, hv, he⟩ := exists_contraction_realizing_model (sphereWall_grid_model θ)
  let N₂ := contract G' C
  have hV₂ : V(N₂).Finite := by
    let : Finite (V(GM01.gridGraph θ)) := Set.toFinite _ |>.to_subtype
    let : Finite (V(N₂)) := Finite.of_equiv _ φ.vertexEquiv
    exact Set.toFinite _
  have hE₂ : E(N₂).Finite := by
    let : Finite (E(GM01.gridGraph θ)) := Set.toFinite _ |>.to_subtype
    let : Finite (E(N₂)) := Finite.of_equiv _ φ.edgeEquiv
    exact Set.toFinite _
  have hMinor : IsMinor N₂ (sphereWallGraph θ) := ⟨G', hG', C, hC, rfl⟩
  have hImage : Hypergraph.ofGraph N₂ hV₂ hE₂ =
      imageHypergraph (sphereWallPair θ) (sphereWallGridEdge θ) (gridHypergraph θ) := by
    exact (imageHypergraph_of_iso (Set.toFinite _) (Set.toFinite _) hV₂ hE₂ φ
      (sphereWallPair θ) (sphereWallGridEdge θ) hv he).symm
  have hT₂ : IsTangle (Hypergraph.ofGraph N₂ hV₂ hE₂) θ
      (imageHypergraphTangle (sphereWallPair θ) (sphereWallGridEdge θ) (gridTangle θ)) := by
    rw [hImage]
    exact isTangle_imageHypergraphTangle _ _ (sphereWallPair_injective θ)
      (sphereWallGridEdge_injective θ) (GM10.theorem_7_3_proof hθ)
  exact ⟨N₂, hV₂, hE₂, hMinor, hImage, hT₂,
    GM10.theorem_6_1_proof (Set.toFinite _) (Set.toFinite _) hV₂ hE₂ hMinor hθ hT₂⟩

end GraphMinor.GM16
