/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4Wall
public import LeanPool.GraphMinor.GM16.ConnectedSeparationSide

/-!
# Uncut rows of the wall in XVI (4.2)

The horizontal rows are connected and have disjoint vertex sets.
A separator with fewer than `θ` vertices therefore misses some row.
That row, including all its edges, is on one side of the separation.
This is the row-selection step for the tangle in Claim (1), page 53.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Hypergraph

/-- The path `P_j` in the proof of XVI (4.2), page 53. -/
def sphereWallRow (θ : ℕ) (j : Fin θ) :
    Graph (Fin (2 * θ + 1) × Fin θ) (Sym2 (Fin (2 * θ + 1) × Fin θ)) :=
  (sphereWallGraph θ).induce {x | x.2 = j}

/-- Every horizontal row is a subgraph of the wall. -/
theorem sphereWallRow_le (θ : ℕ) (j : Fin θ) : sphereWallRow θ j ≤ sphereWallGraph θ :=
  (sphereWallGraph θ).induce_le (subset_univ _)

/-- Horizontal rows remain connected after the alternating deletions. -/
theorem sphereWallRow_connected (θ : ℕ) (j : Fin θ) : GraphConnected (sphereWallRow θ j) := by
  refine ⟨⟨(⟨0, by omega⟩, j), rfl⟩, ?_⟩
  intro x hx y hy
  change x.2 = j at hx
  change y.2 = j at hy
  have hwalk (i k : Fin (2 * θ + 1)) :
      Relation.ReflTransGen (sphereWallRow θ j).Adj (i,j) (k,j) := by
    obtain ⟨w⟩ := preconnected_pathGraph (2 * θ + 1) i k
    induction w with
    | nil => exact .refl
    | @cons a b c hab w ih =>
      apply Relation.ReflTransGen.trans ?_ ih
      refine .single ⟨s((a,j),(b,j)), ?_⟩
      exact ⟨⟨rfl, Or.inl ⟨rfl, pathGraph_adj.mp hab⟩⟩, rfl, rfl⟩
  have h := hwalk x.1 y.1
  have hxEq : (x.1, j) = x := Prod.ext rfl hx.symm
  have hyEq : (y.1, j) = y := Prod.ext rfl hy.symm
  rw [hxEq, hyEq] at h
  exact h

/-- A set of fewer than `θ` wall vertices misses a horizontal row. -/
theorem exists_sphereWallRow_disjoint {θ : ℕ}
    (Z : Set (Fin (2 * θ + 1) × Fin θ)) (hZ : Z.ncard < θ) :
    ∃ j : Fin θ, Disjoint V(sphereWallRow θ j) Z := by
  have hImage : (Prod.snd '' Z).ncard < (Set.univ : Set (Fin θ)).ncard := by
    simpa only [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Set.ncard_image_le (f := Prod.snd) (Set.toFinite Z)).trans_lt hZ
  obtain ⟨j, _, hj⟩ := exists_mem_notMem_of_ncard_lt_ncard hImage
  refine ⟨j, disjoint_left.mpr ?_⟩
  intro x hx hz
  exact hj ⟨x, hz, hx⟩

/-- Every separation of order less than `θ` has an uncut row on one side. -/
theorem sphereWall_separation_has_row {θ : ℕ}
    {A B : Hypergraph (Fin (2 * θ + 1) × Fin θ)
      (Sym2 (Fin (2 * θ + 1) × Fin θ))}
    (hSep : (Hypergraph.ofGraph (sphereWallGraph θ) (Set.toFinite _) (Set.toFinite _)).IsSeparation
      A B)
    (hOrd : separationOrder A B < θ) :
    ∃ j : Fin θ, (E(sphereWallRow θ j) ⊆ A.edgeSet) ∨
      (E(sphereWallRow θ j) ⊆ B.edgeSet) := by
  obtain ⟨j, hj⟩ := exists_sphereWallRow_disjoint (A.vertexSet ∩ B.vertexSet) hOrd
  refine ⟨j, ?_⟩
  rcases connected_subgraph_in_one_side (Set.toFinite _) (Set.toFinite _) hSep
      (sphereWallRow_le θ j) (sphereWallRow_connected θ j) hj with hA | hB
  · exact Or.inl hA.2
  · exact Or.inr hB.2

end GraphMinor.GM16
