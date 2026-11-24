/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallRows
public import LeanPool.GraphMinor.GM16.Section4WallTangle
import LeanPool.GraphMinor.GM10.Section7

/-!
# Rows and the contraction in XVI (4.2)

The surviving edges of a contracted horizontal row come from the
corresponding wall row. A small side of the induced grid tangle cannot
contain a full wall row, since its image would contain a grid column.
X (7.1) then supplies a grid row on that same small side, a contradiction.
-/

public section
namespace GraphMinor.GM16
open Set Graph Hypergraph GM10

/-- Each chosen edge of a horizontal grid path belongs to the same
horizontal wall row. -/
theorem sphereWallGridEdge_col_subset_row (θ : ℕ) (j : Fin θ) :
    sphereWallGridEdge θ '' (gridColPath θ j).edgeSet ⊆ E(sphereWallRow θ j) := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨u, v, b, c, heq, hEnds⟩ := sphereWallGridEdge_ends θ e
  have hAdj : (SimpleGraph.pathGraph θ □ SimpleGraph.pathGraph θ).Adj u v := by
    have hmem := he.1
    rw [heq] at hmem
    exact hmem
  have hu : u.2 = j := he.2 u (by rw [heq]; exact gridHypergraph_inc_sym2.mpr ⟨hAdj, Or.inl rfl⟩)
  have hv : v.2 = j := he.2 v (by rw [heq]; exact gridHypergraph_inc_sym2.mpr ⟨hAdj, Or.inr rfl⟩)
  have hWall := sphereWallGridEdge_mem he.1
  refine ⟨sphereWallPairVertex θ u b, sphereWallPairVertex θ v c, ?_, hu, hv⟩
  exact ⟨hEnds, hWall⟩

/-- A small side of the grid-induced wall tangle includes no complete
horizontal row, as used in XVI (4.2), Claim (1), page 53. -/
theorem induced_wall_tangle_no_small_row {θ : ℕ} (hθ : 2 ≤ θ)
    {N₂ : Graph (Set (Fin (2 * θ + 1) × Fin θ))
      (Sym2 (Fin (2 * θ + 1) × Fin θ))}
    (hV₂ : V(N₂).Finite) (hE₂ : E(N₂).Finite)
    (hImage : Hypergraph.ofGraph N₂ hV₂ hE₂ = imageHypergraph (sphereWallPair θ)
      (sphereWallGridEdge θ) (gridHypergraph θ))
    {A B : Hypergraph (Fin (2 * θ + 1) × Fin θ) (Sym2 (Fin (2 * θ + 1) × Fin θ))}
    (hAB : (A, B) ∈ inducedTangle
      (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _))
      (Hypergraph.ofGraph N₂ hV₂ hE₂)
      (imageHypergraphTangle (sphereWallPair θ) (sphereWallGridEdge θ) (gridTangle θ)) θ)
    (j : Fin θ) : ¬ E(sphereWallRow θ j) ⊆ A.edgeSet := by
  intro hRow
  obtain ⟨p, hp, hEdge⟩ := hAB.2.2
  obtain ⟨⟨A₀, B₀⟩, hGrid, hEq⟩ := hp
  have hA := congrArg Prod.fst hEq
  have hAE : sphereWallGridEdge θ '' A₀.edgeSet = A.edgeSet ∩ E(N₂) :=
    (congrArg Hypergraph.edgeSet hA).trans hEdge
  have hEN : E(N₂) = sphereWallGridEdge θ '' (gridHypergraph θ).edgeSet :=
    congrArg Hypergraph.edgeSet hImage
  have hCol : (gridColPath θ j).edgeSet ⊆ A₀.edgeSet := by
    intro e he
    have hInA : sphereWallGridEdge θ e ∈ A.edgeSet :=
      hRow (sphereWallGridEdge_col_subset_row θ j ⟨e, he, rfl⟩)
    have hInN : sphereWallGridEdge θ e ∈ E(N₂) := hEN.symm ▸ ⟨e, he.1, rfl⟩
    obtain ⟨e₀, he₀, hMap⟩ := hAE.symm ▸ (show sphereWallGridEdge θ e ∈ A.edgeSet ∩ E(N₂) from
      ⟨hInA, hInN⟩)
    exact sphereWallGridEdge_injective θ hMap ▸ he₀
  have hSmall : IsSmallEdgeSet θ A₀.edgeSet := hGrid.2.2
  obtain ⟨i, hi⟩ := (GM10.theorem_7_1_proof hθ hGrid.1.left_le.edgeSet_subset hSmall.1).mpr ⟨j,
    hCol⟩
  exact hSmall.2 i hi

end GraphMinor.GM16
