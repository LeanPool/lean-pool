/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CommonMissingColorsAtUncoloredEndpoints
public import LeanPool.GoldbergSeymour.HierarchyBase

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment

/-!
# Parallel Base Four Common Missing Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem ParallelBaseFourCommonMissingColors
    {V E : Type*} [Fintype V] [Fintype E]
    [ DecidableEq V] [ DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hdegree : MaximumDegree G + 1 <= k)
    (helem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet base.core)) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    4 <= (TreeMissingColors phi Tn ∩
      TreeMissingColors phi base.closure).card := by
  dsimp
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let supportPrefix := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  obtain ⟨hchosen, hclosure, ⟨hunion⟩⟩ := base.parallel hPE
  let j : Fin Tn.length := ⟨0, Tn.positive⟩
  obtain ⟨i, hi⟩ := Tn.attaches j
  have hi0 : i = 0 := Fin.eq_zero i
  subst i
  let x := Tn.vertex j.succ
  let y := Tn.vertex (0 : Fin (Tn.length + 1))
  have hends : G.ends e0 = s(x, y) := by
    rw [← Tn.first_edge]
    convert hi using 1
    simp only [x, y, j]
    congr 2
  have hxTn : x ∈ TreeSequenceVertexSet Tn := by
    rw [TreeSequenceVertexSet]
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨j.succ, Finset.mem_univ _, rfl⟩
  have hyTn : y ∈ TreeSequenceVertexSet Tn := by
    rw [TreeSequenceVertexSet]
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨0, Finset.mem_univ _, rfl⟩
  have hxPrefix : x ∈ TreeSequenceVertexSet supportPrefix := by
    rw [TreeSequenceVertexSet]
    let p : Fin (base.supportPosition.val + 1) :=
      ⟨1, Nat.lt_succ_of_le base.supportPositive⟩
    refine (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨p, Finset.mem_univ _, ?_⟩
    simp [supportPrefix, TreeSequencePrefix, x, j, p]
  have hyPrefix : y ∈ TreeSequenceVertexSet supportPrefix := by
    rw [TreeSequenceVertexSet]
    let p : Fin (base.supportPosition.val + 1) := ⟨0, Nat.zero_lt_succ _⟩
    refine (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨p, Finset.mem_univ _, ?_⟩
    simp [supportPrefix, TreeSequencePrefix, y, p]
  have hprefixSegment :=
    TashkinovAugmentationSequenceInitialSegment phi supportPrefix base.closure hclosure.1
  have prefixInClosure : TreeSequenceVertexSet supportPrefix ⊆
      TreeSequenceVertexSet base.closure := by
    intro z hz
    rw [TreeSequenceVertexSet] at hz ⊢
    obtain ⟨a, -, rfl⟩ :=
      (@Finset.mem_image _ _ (Classical.decEq V)).mp hz
    exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨Fin.castLE (Nat.succ_le_succ hprefixSegment.1) a,
        Finset.mem_univ _, hprefixSegment.2.1 a⟩
  have hxClosure : x ∈ TreeSequenceVertexSet base.closure :=
    prefixInClosure hxPrefix
  have hyClosure : y ∈ TreeSequenceVertexSet base.closure :=
    prefixInClosure hyPrefix
  have hUnionElem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure) := by
    rw [← hunion.vertexSet]
    exact helem
  exact CommonMissingColorsAtUncoloredEndpoints G k e0 phi Tn base.closure
    x y hends hproper hone hdegree hxTn hyTn hxClosure hyClosure hUnionElem

end GoldbergSeymour

end
