/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallContraction
import Mathlib.Combinatorics.Graph.Subgraph

/-!
# The smaller grid as a minor of the wall

This verifies the contraction in XVI (4.2), Claim (1), page 53.
The branch sets are the horizontal pairs, and the edge map is the
parity choice from `Section4WallContraction`. The internal pair edge
is different from every chosen grid edge. Thus each pair remains
connected after all chosen edges are removed.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph

private theorem simpleGraph_inc_iff {α : Type*} (K : SimpleGraph α) (e : Sym2 α) (v : α) :
    (Graph.ofSimpleGraph K).Inc e v ↔ e ∈ K.edgeSet ∧ v ∈ e := by
  constructor
  · rintro ⟨w, he, hmem⟩
    exact ⟨hmem, he ▸ Sym2.mem_mk_left v w⟩
  · rintro ⟨hmem, hv⟩
    obtain ⟨w, he⟩ := Sym2.mem_iff_exists.mp hv
    exact ⟨w, he, hmem⟩

/-- Each vertex in a pair has that pair's quotient coordinate. -/
theorem sphereWallPair_projection {θ : ℕ} {v : Fin θ × Fin θ}
    {x : Fin (2 * θ + 1) × Fin θ} (hx : x ∈ sphereWallPair θ v) :
    sphereWallPairProjection θ x = v := by
  rcases hx with rfl | hx
  · exact sphereWallPairProjection_vertex θ v 0
  · rw [mem_singleton_iff] at hx
    subst x
    exact sphereWallPairProjection_vertex θ v 1

/-- The chosen wall edge joins one vertex of each pair indexed by its
original grid ends. -/
theorem sphereWallGridEdge_ends (θ : ℕ) (e : Sym2 (Fin θ × Fin θ)) :
    ∃ (u v : Fin θ × Fin θ) (b c : Fin 2),
      e = s(u,v) ∧ sphereWallGridEdge θ e =
        s(sphereWallPairVertex θ u b, sphereWallPairVertex θ v c) := by
  induction e with
  | h u v =>
    rw [sphereWallGridEdge_mk]
    unfold sphereWallEdgePair
    split_ifs
    · exact ⟨u, v, 1, 0, rfl, rfl⟩
    · exact ⟨u, v, 0, 1, rfl, rfl⟩
    · exact ⟨u, v, _, _, rfl, rfl⟩

private theorem pairVertex_mem (θ : ℕ) (v : Fin θ × Fin θ) (b : Fin 2) :
    sphereWallPairVertex θ v b ∈ sphereWallPair θ v := by
  have hb : b = 0 ∨ b = 1 := by
    have := b.isLt
    rcases Nat.eq_zero_or_pos b.val with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by omega))
  rcases hb with rfl | rfl
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_singleton _)

private theorem wallGrid_inc_iff {θ : ℕ} {e : Sym2 (Fin θ × Fin θ)}
    (he : e ∈ E(GM01.gridGraph θ)) (v : Fin θ × Fin θ) :
    (GM01.gridGraph θ).Inc e v ↔ ∃ x ∈ sphereWallPair θ v,
      (sphereWallGraph θ).Inc (sphereWallGridEdge θ e) x := by
  obtain ⟨u, w, b, c, heq, hEnds⟩ := sphereWallGridEdge_ends θ e
  have hWall := sphereWallGridEdge_mem he
  change (Graph.ofSimpleGraph (pathGraph θ □ pathGraph θ)).Inc e v ↔ _
  rw [simpleGraph_inc_iff]
  constructor
  · rintro ⟨_, hv⟩
    rw [heq, Sym2.mem_iff] at hv
    rcases hv with hv | hv
    · subst v
      refine ⟨sphereWallPairVertex θ u b, pairVertex_mem θ u b, ?_⟩
      exact (simpleGraph_inc_iff _ _ _).mpr ⟨hWall, hEnds ▸ Sym2.mem_mk_left _ _⟩
    · subst v
      refine ⟨sphereWallPairVertex θ w c, pairVertex_mem θ w c, ?_⟩
      exact (simpleGraph_inc_iff _ _ _).mpr ⟨hWall, hEnds ▸ Sym2.mem_mk_right _ _⟩
  · rintro ⟨x, hx, hinc⟩
    refine ⟨he, ?_⟩
    have hmem := ((simpleGraph_inc_iff _ _ _).mp hinc).2
    rw [hEnds, Sym2.mem_iff] at hmem
    have hproj := sphereWallPair_projection hx
    rw [heq, Sym2.mem_iff]
    rcases hmem with rfl | rfl
    · exact Or.inl ((sphereWallPairProjection_vertex θ u b).symm.trans hproj).symm
    · exact Or.inr ((sphereWallPairProjection_vertex θ w c).symm.trans hproj).symm

/-- The explicit pair contraction used in XVI (4.2), Claim (1), page 53.
The smaller square grid is a minor of the wall. -/
theorem sphereWall_grid_model (θ : ℕ) :
    IsMinorModel (GM01.gridGraph θ) (sphereWallGraph θ)
      (sphereWallPair θ) (sphereWallGridEdge θ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v _
    exact ⟨sphereWallPairVertex θ v 0, mem_insert _ _⟩
  · intro v _
    exact subset_univ _
  · intro e he
    exact sphereWallGridEdge_mem he
  · intro u _ v _ hne
    exact sphereWallPair_disjoint hne
  · exact (sphereWallGridEdge_injective θ).injOn
  · intro v _ e he
    exact wallGrid_inc_iff he v
  · intro v _ e he
    have hnot : ¬ (GM01.gridGraph θ).IsLoopAt e v := by
      rintro ⟨heq, hmem⟩
      change e ∈ (pathGraph θ □ pathGraph θ).edgeSet at hmem
      rw [heq] at hmem
      have hadj : (pathGraph θ □ pathGraph θ).Adj v v := hmem
      exact hadj.ne rfl
    refine ⟨fun h => (hnot h).elim, ?_⟩
    intro hall
    obtain ⟨u, w, b, c, heq, hEnds⟩ := sphereWallGridEdge_ends θ e
    have hw := sphereWallGridEdge_mem he
    have hU := sphereWallPair_projection (hall _
      ((simpleGraph_inc_iff _ _ _).mpr ⟨hw, hEnds ▸ Sym2.mem_mk_left _ _⟩))
    have hW := sphereWallPair_projection (hall _
      ((simpleGraph_inc_iff _ _ _).mpr ⟨hw, hEnds ▸ Sym2.mem_mk_right _ _⟩))
    rw [sphereWallPairProjection_vertex] at hU hW
    have huw : u = w := hU.trans hW.symm
    have hmem : e ∈ (pathGraph θ □ pathGraph θ).edgeSet := he
    rw [heq, huw] at hmem
    have hadj : (pathGraph θ □ pathGraph θ).Adj w w := hmem
    exact (hadj.ne rfl).elim
  · intro v _
    let K := (sphereWallGraph θ).induce (sphereWallPair θ v)
    have hKle : K ≤ (sphereWallGraph θ).deleteEdges
        (sphereWallGridEdge θ '' E(GM01.gridGraph θ)) := by
      refine ⟨?_, ?_⟩
      · exact subset_univ _
      · intro e x y hlink
        refine ⟨hlink.1, ?_⟩
        intro hchosen
        have hx := sphereWallPair_projection hlink.2.1
        have hy := sphereWallPair_projection hlink.2.2
        obtain ⟨e₀, he₀, heq⟩ := hchosen
        have hexy : e = s(x,y) := hlink.1.1
        have hproj := congrArg (Sym2.map (sphereWallPairProjection θ)) heq
        rw [sphereWallGridEdge_projection, hexy, Sym2.map_mk, hx, hy] at hproj
        change e₀ ∈ (pathGraph θ □ pathGraph θ).edgeSet at he₀
        rw [hproj] at he₀
        have hadj : (pathGraph θ □ pathGraph θ).Adj v v := he₀
        exact hadj.ne rfl
    have hVK : V(K) = sphereWallPair θ v := rfl
    refine ⟨K, hKle, hVK, ?_⟩
    refine ⟨⟨sphereWallPairVertex θ v 0, hVK.symm ▸ mem_insert _ _⟩, ?_⟩
    intro x hx y hy
    rw [hVK] at hx hy
    have hxy : K.Adj (sphereWallPairVertex θ v 0) (sphereWallPairVertex θ v 1) := by
      refine ⟨s(sphereWallPairVertex θ v 0, sphereWallPairVertex θ v 1), ?_⟩
      exact ⟨⟨rfl, sphereWallPairVertex_adj θ v⟩, pairVertex_mem θ v 0, pairVertex_mem θ v 1⟩
    simp only [sphereWallPair, mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact .refl
    · exact .single hxy
    · exact .single hxy.symm
    · exact .refl

end GraphMinor.GM16
