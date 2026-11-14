/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Finset.Max

/-!
# Walks entering and leaving a vertex region

The vertex and edge nodes of an incidence walk need different treatment when locating
boundary crossings. These facts depend only on the walk and the vertex region.
Supplying the index predicate decisions lets finite and classical callers reuse
their own finite index sets directly.
Adapted from the walk-index arguments in Wesley Pegden's Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour.WalkVertexRegion

variable {V E : Type*} {graph : SimpleGraph (Sum V E)} {start finish : Sum V E}

/-- Positions at which a walk visits a vertex outside the region. -/
def outsideIndices (walk : graph.Walk start finish) (region : Set V)
    [DecidablePred fun index : Fin (walk.length + 1) =>
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∉ region] :
    Finset (Fin (walk.length + 1)) :=
  Finset.univ.filter fun index =>
    ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∉ region

/-- An outside vertex in the support supplies an outside position. -/
theorem outsideIndices_nonempty (walk : graph.Walk start finish) (region : Set V)
    [DecidablePred fun index : Fin (walk.length + 1) =>
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∉ region]
    {vertex : V} (outside : vertex ∉ region) (member : Sum.inl vertex ∈ walk.support) :
    (outsideIndices walk region).Nonempty := by
  classical
  obtain ⟨index, atVertex, bound⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp member
  exact ⟨⟨index, by omega⟩, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, vertex, atVertex, outside⟩⟩

/-- Every vertex visited before the first outside position is in the region. -/
theorem mem_before_firstOutside (walk : graph.Walk start finish) (region : Set V)
    [DecidablePred fun index : Fin (walk.length + 1) =>
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∉ region]
    (nonempty : (outsideIndices walk region).Nonempty)
    {index : Fin (walk.length + 1)}
    (before : index.val < ((outsideIndices walk region).min' nonempty).val)
    {vertex : V} (atVertex : walk.getVert index.val = Sum.inl vertex) : vertex ∈ region := by
  classical
  by_contra outside
  have member : index ∈ outsideIndices walk region :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, vertex, atVertex, outside⟩
  have bound := Finset.min'_le (outsideIndices walk region) index member
  exact (not_lt_of_ge bound) before

/-- If the starting vertex is inside, the first outside position is positive. -/
theorem firstOutside_pos {root : V} (walk : graph.Walk (Sum.inl root) finish)
    (region : Set V) (inside : root ∈ region)
    [DecidablePred fun index : Fin (walk.length + 1) =>
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∉ region]
    (nonempty : (outsideIndices walk region).Nonempty) :
    0 < ((outsideIndices walk region).min' nonempty).val := by
  classical
  obtain ⟨vertex, atVertex, outside⟩ :=
    (Finset.mem_filter.mp (Finset.min'_mem (outsideIndices walk region) nonempty)).2
  by_contra notPositive
  have zero : ((outsideIndices walk region).min' nonempty).val = 0 := by omega
  rw [zero, walk.getVert_zero] at atVertex
  exact outside (Sum.inl.inj atVertex ▸ inside)

/-- A walk ending inside reaches its first outside vertex strictly before the end. -/
theorem firstOutside_lt_length {root : V} (walk : graph.Walk start (Sum.inl root))
    (region : Set V) (inside : root ∈ region)
    [DecidablePred fun index : Fin (walk.length + 1) =>
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∉ region]
    (nonempty : (outsideIndices walk region).Nonempty) :
    ((outsideIndices walk region).min' nonempty).val < walk.length := by
  classical
  obtain ⟨vertex, atVertex, outside⟩ :=
    (Finset.mem_filter.mp (Finset.min'_mem (outsideIndices walk region) nonempty)).2
  by_contra notBefore
  have bound := ((outsideIndices walk region).min' nonempty).isLt
  have last : ((outsideIndices walk region).min' nonempty).val = walk.length := by omega
  rw [last, walk.getVert_length] at atVertex
  exact outside (Sum.inl.inj atVertex ▸ inside)

/-- Inside positions strictly after a specified position. -/
def laterInsideIndices (walk : graph.Walk start finish) (region : Set V)
    (afterIndex : Fin (walk.length + 1))
    [DecidablePred fun index : Fin (walk.length + 1) => afterIndex.val < index.val ∧
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∈ region] :
    Finset (Fin (walk.length + 1)) :=
  Finset.univ.filter fun index => afterIndex.val < index.val ∧
    ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∈ region

/-- The inside endpoint supplies a later inside position. -/
theorem laterInsideIndices_nonempty {root : V} (walk : graph.Walk start (Sum.inl root))
    (region : Set V) (inside : root ∈ region) (afterIndex : Fin (walk.length + 1))
    [DecidablePred fun index : Fin (walk.length + 1) => afterIndex.val < index.val ∧
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∈ region]
    (beforeEnd : afterIndex.val < walk.length) :
    (laterInsideIndices walk region afterIndex).Nonempty := by
  classical
  refine ⟨⟨walk.length, by omega⟩, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, beforeEnd, root, ?_, inside⟩⟩
  exact walk.getVert_length

/-- Until its first return, a walk stays outside at every vertex position. -/
theorem not_mem_before_firstReturn (walk : graph.Walk start finish) (region : Set V)
    (afterIndex : Fin (walk.length + 1))
    [DecidablePred fun index : Fin (walk.length + 1) => afterIndex.val < index.val ∧
      ∃ vertex, walk.getVert index.val = Sum.inl vertex ∧ vertex ∈ region] {outsideVertex : V}
    (atOutside : walk.getVert afterIndex.val = Sum.inl outsideVertex)
    (outside : outsideVertex ∉ region)
    (nonempty : (laterInsideIndices walk region afterIndex).Nonempty)
    {index : Fin (walk.length + 1)} (afterOutside : afterIndex.val ≤ index.val)
    (beforeReturn : index.val < ((laterInsideIndices walk region afterIndex).min' nonempty).val)
    {vertex : V} (atVertex : walk.getVert index.val = Sum.inl vertex) : vertex ∉ region := by
  classical
  intro inside
  by_cases same : index = afterIndex
  · have equal : outsideVertex = vertex := Sum.inl.inj (atOutside.symm.trans (same ▸ atVertex))
    exact outside (equal.symm ▸ inside)
  · have afterStrict : afterIndex.val < index.val := by
      have different : index.val ≠ afterIndex.val := fun equal => same (Fin.ext equal)
      omega
    have member : index ∈ laterInsideIndices walk region afterIndex :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, afterStrict, vertex, atVertex, inside⟩
    have bound := Finset.min'_le (laterInsideIndices walk region afterIndex) index member
    exact (not_lt_of_ge bound) beforeReturn

end GoldbergSeymour.WalkVertexRegion

end
