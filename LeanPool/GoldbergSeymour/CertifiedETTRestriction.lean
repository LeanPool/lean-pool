/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumPropertyPrefix
public import LeanPool.GoldbergSeymour.ExtendedTashkinovTreePrefix

/-!
# Certified ETTRestriction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem CertifiedETTRestriction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (r : ℕ)
    (hrPositive : 1 ≤ r) (hrBefore : r < ett.rounds) :
    ∃ restricted : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree ⟨r + 1, by omega⟩)
        (ett.series.data.coloring ⟨r, by omega⟩),
      ∃ hr : restricted.rounds = r,
        MaximumProperty restricted ∧
        (∀ i : Fin (restricted.rounds + 2),
          restricted.series.data.tree i =
            ett.series.data.tree (Fin.castLE (by omega) i)) ∧
        (∀ i : Fin (restricted.rounds + 1),
          restricted.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
          restricted.series.data.stored i =
              ett.series.data.stored (Fin.castLE (by omega) i) ∧
          restricted.series.data.connectingEdges i =
              ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          restricted.series.data.kind i =
              ett.series.data.kind (Fin.castLE (by omega) i) ∧
          restricted.series.data.chosenVertex i =
              ett.series.data.chosenVertex (Fin.castLE (by omega) i) ∧
          restricted.series.data.outsideVertex i =
              ett.series.data.outsideVertex (Fin.castLE (by omega) i) ∧
          restricted.series.data.delta i =
              ett.series.data.delta (Fin.castLE (by omega) i) ∧
          restricted.series.data.gamma i =
              ett.series.data.gamma (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors restricted.series.data i =
              TashkinovStoredColors ett.series.data
                (Fin.castLE (by omega) i) ∧
          HEq (restricted.series.certified i)
            (ett.series.certified (Fin.castLE (by omega) i))) := by
  have hprefix := ExtendedTashkinovTreePrefix G k e0 input T generating ett
    r hrPositive hrBefore
    ⟨r + 1, by omega⟩ rfl
    ⟨r, by omega⟩ rfl
  obtain ⟨restricted, hr, tree_eq, full_data_eq⟩ := hprefix
  have data_eq : ∀ i : Fin (restricted.rounds + 1),
      restricted.series.data.coloring i =
          ett.series.data.coloring (Fin.castLE (by omega) i) ∧
      restricted.series.data.connectingEdges i =
          ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
      restricted.series.data.kind i =
          ett.series.data.kind (Fin.castLE (by omega) i) ∧
      TashkinovStoredColors restricted.series.data i =
          TashkinovStoredColors ett.series.data
            (Fin.castLE (by omega) i) := by
    intro i
    rcases full_data_eq i with ⟨hc, _, he, hk, _, _, _, _, hs, _⟩
    exact ⟨hc, he, hk, hs⟩
  have hmax : MaximumProperty restricted :=
    MaximumPropertyPrefix G k e0 input T generating ett hMP
      r hrPositive hrBefore restricted hr tree_eq data_eq
  exact ⟨restricted, hr, hmax, tree_eq, full_data_eq⟩

end GoldbergSeymour

end
