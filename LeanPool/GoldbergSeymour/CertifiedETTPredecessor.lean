/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTreePrefix
public import LeanPool.GoldbergSeymour.MaximumPropertyPrefix

/-!
# Certified ETTPredecessor

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem CertifiedETTPredecessor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hrounds : 1 < ett.rounds) :
    ∃ predecessor : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree ⟨ett.rounds, by omega⟩)
        (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩),
      ∃ hr : predecessor.rounds = ett.rounds - 1,
        MaximumProperty predecessor ∧
        (∀ i : Fin (predecessor.rounds + 2),
          predecessor.series.data.tree i =
            ett.series.data.tree (Fin.castLE (by omega) i)) ∧
        (∀ i : Fin (predecessor.rounds + 1),
          predecessor.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
          predecessor.series.data.stored i =
              ett.series.data.stored (Fin.castLE (by omega) i) ∧
          predecessor.series.data.connectingEdges i =
              ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          predecessor.series.data.kind i =
              ett.series.data.kind (Fin.castLE (by omega) i) ∧
          predecessor.series.data.chosenVertex i =
              ett.series.data.chosenVertex (Fin.castLE (by omega) i) ∧
          predecessor.series.data.outsideVertex i =
              ett.series.data.outsideVertex (Fin.castLE (by omega) i) ∧
          predecessor.series.data.delta i =
              ett.series.data.delta (Fin.castLE (by omega) i) ∧
          predecessor.series.data.gamma i =
              ett.series.data.gamma (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors predecessor.series.data i =
              TashkinovStoredColors ett.series.data
                (Fin.castLE (by omega) i) ∧
          HEq (predecessor.series.certified i)
            (ett.series.certified (Fin.castLE (by omega) i))) := by
  have hmPositive : 1 ≤ ett.rounds - 1 := by omega
  have hmBefore : ett.rounds - 1 < ett.rounds := by omega
  have hidx : ett.rounds - 1 + 1 = ett.rounds :=
    Nat.sub_add_cancel (by omega)
  have hprefix := ExtendedTashkinovTreePrefix G k e0 input T generating ett
    (ett.rounds - 1) hmPositive hmBefore
    ⟨ett.rounds, by omega⟩ hidx.symm
    ⟨ett.rounds - 1, by omega⟩ rfl
  obtain ⟨predecessor, hr, tree_eq, full_data_eq⟩ := hprefix
  have data_eq : ∀ i : Fin (predecessor.rounds + 1),
      predecessor.series.data.coloring i =
          ett.series.data.coloring (Fin.castLE (by omega) i) ∧
      predecessor.series.data.connectingEdges i =
          ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
      predecessor.series.data.kind i =
          ett.series.data.kind (Fin.castLE (by omega) i) ∧
      TashkinovStoredColors predecessor.series.data i =
          TashkinovStoredColors ett.series.data
            (Fin.castLE (by omega) i) := by
    intro i
    rcases full_data_eq i with ⟨hc, _, he, hk, _, _, _, _, hs, _⟩
    exact ⟨hc, he, hk, hs⟩
  have hmax : MaximumProperty predecessor :=
    MaximumPropertyPrefix G k e0 input T generating ett hMP
      (ett.rounds - 1) hmPositive hmBefore predecessor hr tree_eq data_eq
  exact ⟨predecessor, hr, hmax, tree_eq, full_data_eq⟩

end GoldbergSeymour

end
