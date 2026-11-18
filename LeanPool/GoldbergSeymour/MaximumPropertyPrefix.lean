/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumProperty

/-!
# Maximum Property Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MaximumPropertyPrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (m : ℕ)
    (hmPositive : 1 ≤ m) (hmBefore : m < ett.rounds)
    {restrictedTree : TreeSequence G e0}
    {restrictedColoring : PartialEdgeColoring E k}
    (restricted : ExtendedTashkinovTree G k e0 input
      restrictedTree restrictedColoring)
    (hr : restricted.rounds = m)
    (tree_eq : ∀ i : Fin (restricted.rounds + 2),
      restricted.series.data.tree i =
        ett.series.data.tree (Fin.castLE (by omega) i))
    (data_eq : ∀ i : Fin (restricted.rounds + 1),
      restricted.series.data.coloring i =
          ett.series.data.coloring (Fin.castLE (by omega) i) ∧
      restricted.series.data.connectingEdges i =
          ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
      restricted.series.data.kind i =
          ett.series.data.kind (Fin.castLE (by omega) i) ∧
      TashkinovStoredColors restricted.series.data i =
          TashkinovStoredColors ett.series.data
            (Fin.castLE (by omega) i)) :
    MaximumProperty restricted := by
  unfold MaximumProperty at hMP ⊢
  dsimp only at hMP ⊢
  constructor
  · have htreeOne := tree_eq (⟨1, by omega⟩ : Fin (restricted.rounds + 2))
    have hcastOne : Fin.castLE (by omega)
        (⟨1, by omega⟩ : Fin (restricted.rounds + 2)) =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      rfl
    rw [hcastOne] at htreeOne
    rw [htreeOne]
    exact hMP.1
  · intro i hi hbefore pi seed candidate hproper hone hstable hroute hclosure
    have holdBefore : i < ett.rounds := by omega
    let restrictedIdx : Fin (restricted.rounds + 1) := ⟨i, by omega⟩
    let oldIdx : Fin (ett.rounds + 1) := ⟨i, by omega⟩
    have hcastIdx : Fin.castLE (by omega) restrictedIdx = oldIdx := by
      apply Fin.ext
      rfl
    have hcastTree : Fin.castLE (by omega) restrictedIdx.castSucc =
        oldIdx.castSucc := by
      apply Fin.ext
      rfl
    have hTi : restricted.series.data.tree restrictedIdx.castSucc =
        ett.series.data.tree oldIdx.castSucc := by
      rw [tree_eq]
      rw [hcastTree]
    have hcastNext : Fin.castLE (by omega)
        (⟨i + 1, by omega⟩ : Fin (restricted.rounds + 2)) =
        (⟨i + 1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      rfl
    have hnext : restricted.series.data.tree (⟨i + 1, by omega⟩) =
        ett.series.data.tree (⟨i + 1, by omega⟩) := by
      rw [tree_eq]
      rw [hcastNext]
    rcases data_eq restrictedIdx with ⟨hcolor, hedges, hkind, hstored⟩
    rw [hcastIdx] at hcolor hedges hkind hstored
    have hstableOld : StableColoring
        (ett.series.data.tree oldIdx.castSucc)
        (TashkinovStoredColors ett.series.data oldIdx)
        (ett.series.data.coloring oldIdx) pi := by
      rw [← hTi, ← hstored, ← hcolor]
      exact hstable
    have hrouteOld :
        ((ett.series.data.kind oldIdx = some TashkinovExtensionKind.PE ∧
            seed = ett.series.data.tree oldIdx.castSucc) ∨
          ((ett.series.data.kind oldIdx = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind oldIdx = some TashkinovExtensionKind.RE) ∧
            ∃ f : E, ett.series.data.connectingEdges oldIdx = {f} ∧
              TreeSequenceAdjoinEdge
                (ett.series.data.tree oldIdx.castSucc) f seed)) := by
      rw [← hTi, ← hedges, ← hkind]
      exact hroute
    have bound := hMP.2 i hi holdBefore pi seed candidate hproper hone
      hstableOld hrouteOld hclosure
    rw [hnext]
    exact bound

end GoldbergSeymour

end
