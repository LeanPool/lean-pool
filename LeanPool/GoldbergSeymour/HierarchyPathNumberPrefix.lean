/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.HierarchyPathNumber

/-!
# Path numbers under a terminal prefix

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- A hierarchy with a nonempty tail has a positive path number. -/
theorem TashkinovHierarchy.pathNumber_pos {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input generating phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input tree generating}
    {base : HierarchyBase ett phi} (hierarchy : TashkinovHierarchy ett base)
    (tail : (HierarchyStarredStage hierarchy (Fin.last hierarchy.dividerCount)).length <
      tree.length) : 0 < HierarchyPathNumber hierarchy := by
  classical
  unfold HierarchyPathNumber
  dsimp only
  split_ifs with nonempty
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ nonempty)).1).1
  · exact Nat.sub_pos_of_lt tail

/-- A path number before the tail end forces consecutive endpoints on every later edge. -/
theorem TashkinovHierarchy.consecutive_after_pathNumber {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input generating phi : PartialEdgeColoring E k}
    {tree : TreeSequence G e0} {ett : ExtendedTashkinovTree G k e0 input tree generating}
    {base : HierarchyBase ett phi} (hierarchy : TashkinovHierarchy ett base)
    (short : HierarchyPathNumber hierarchy < tree.length -
      (HierarchyStarredStage hierarchy (Fin.last hierarchy.dividerCount)).length)
    (index : Fin tree.length)
    (after : (HierarchyStarredStage hierarchy (Fin.last hierarchy.dividerCount)).length +
      HierarchyPathNumber hierarchy ≤ index.val) :
    G.ends (tree.edge index) = s(tree.vertex index.castSucc, tree.vertex index.succ) := by
  classical
  let stage := HierarchyStarredStage hierarchy (Fin.last hierarchy.dividerCount)
  change HierarchyPathNumber hierarchy < tree.length - stage.length at short
  let candidates := (Finset.Icc 1 (tree.length - stage.length)).filter fun position =>
    ∀ index : Fin tree.length, stage.length + position ≤ index.val →
      G.ends (tree.edge index) = s(tree.vertex index.castSucc, tree.vertex index.succ)
  have value : HierarchyPathNumber hierarchy =
      (if nonempty : candidates.Nonempty then candidates.min' nonempty
        else tree.length - stage.length) := rfl
  have nonempty : candidates.Nonempty := by
    by_contra empty
    rw [dite_eq_right empty] at value
    omega
  have minimum : candidates.min' nonempty = HierarchyPathNumber hierarchy := by
    simpa only [dite_eq_left nonempty] using value.symm
  have consecutive := (Finset.mem_filter.mp (Finset.min'_mem candidates nonempty)).2
  rw [minimum] at consecutive
  exact consecutive index after

/-- Restricting the terminal tree cannot increase the first path position after a common offset. -/
theorem TashkinovHierarchy.pathNumber_le_of_prefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {e0 : E} {k l : ℕ} {T B : TreeSequence G e0}
    {input generating phi : PartialEdgeColoring E k}
    {otherInput otherGenerating otherPhi : PartialEdgeColoring E l}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
    {otherETT : ExtendedTashkinovTree G l e0 otherInput B otherGenerating}
    {otherBase : HierarchyBase otherETT otherPhi}
    (original : TashkinovHierarchy ett base) (restricted : TashkinovHierarchy otherETT otherBase)
    (sameStarLength :
      (HierarchyStarredStage restricted (Fin.last restricted.dividerCount)).length =
        (HierarchyStarredStage original (Fin.last original.dividerCount)).length)
    (segment : TreeSequenceInitialSegment B T)
    (aboveStar :
      (HierarchyStarredStage original (Fin.last original.dividerCount)).length < B.length) :
    HierarchyPathNumber restricted ≤ HierarchyPathNumber original := by
  classical
  let A := HierarchyStarredStage original (Fin.last original.dividerCount)
  change A.length < B.length at aboveStar
  have positiveTail : A.length < T.length := lt_of_lt_of_le aboveStar segment.1
  let ell := T.length - A.length
  let tailB := B.length - A.length
  let candidatesT := (Finset.Icc 1 ell).filter fun i =>
    ∀ t : Fin T.length, A.length + i ≤ t.val →
      G.ends (T.edge t) = s(T.vertex t.castSucc, T.vertex t.succ)
  let candidatesB := (Finset.Icc 1 tailB).filter fun i =>
    ∀ t : Fin B.length, A.length + i ≤ t.val →
      G.ends (B.edge t) = s(B.vertex t.castSucc, B.vertex t.succ)
  have htail : 1 ≤ tailB := by dsimp [tailB]; omega
  have htailT : 1 ≤ ell := by dsimp [ell]; omega
  have htmem : ell ∈ candidatesT := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htailT, le_rfl⟩, ?_⟩
    intro t ht
    have hAT := le_of_lt positiveTail
    have := t.isLt
    dsimp [ell] at ht
    omega
  have hbmem : tailB ∈ candidatesB := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨htail, le_rfl⟩, ?_⟩
    intro t ht
    have := t.isLt
    dsimp [tailB] at ht
    omega
  have hnT : candidatesT.Nonempty := ⟨ell, htmem⟩
  have hnB : candidatesB.Nonempty := ⟨tailB, hbmem⟩
  have hmT := Finset.min'_mem candidatesT hnT
  have hbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hmT).1
  have hminB : candidatesB.min' hnB ≤ candidatesT.min' hnT := by
    by_cases ht : candidatesT.min' hnT ≤ tailB
    · apply Finset.min'_le
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbounds.1, ht⟩, ?_⟩
      intro t hpos
      have he := (Finset.mem_filter.mp hmT).2 (Fin.castLE segment.1 t) hpos
      have hv0 := segment.2.1 t.castSucc
      have hv1 := segment.2.1 t.succ
      have hi0 : (Fin.castLE segment.1 t).castSucc =
          Fin.castLE (Nat.succ_le_succ segment.1) t.castSucc := Fin.ext rfl
      have hi1 : (Fin.castLE segment.1 t).succ =
          Fin.castLE (Nat.succ_le_succ segment.1) t.succ := Fin.ext rfl
      simpa only [segment.2.2, hi0, hi1, hv0, hv1] using he
    · exact le_trans (Finset.min'_le candidatesB tailB hbmem) (by omega)
  unfold HierarchyPathNumber
  simp only [sameStarLength]
  change (if h : candidatesB.Nonempty then candidatesB.min' h else tailB) ≤
    (if h : candidatesT.Nonempty then candidatesT.min' h else ell)
  rw [dite_eq_left hnB, dite_eq_left hnT]
  exact hminB

end GoldbergSeymour

end
