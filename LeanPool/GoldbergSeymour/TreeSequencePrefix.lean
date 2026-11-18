/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequence

/-!
# Tree Sequence Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The first specified positive number of edges and their vertices, with inherited tree
certificates.
-/
noncomputable def TreeSequencePrefix {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    (T : TreeSequence G e0) (q : ℕ) (hq : 1 ≤ q) (hqt : q ≤ T.length) : TreeSequence G e0 := by
  classical
  refine
    { length := q
      positive := hq
      vertex := fun i => T.vertex (Fin.castLE (Nat.succ_le_succ hqt) i)
      edge := fun i => T.edge (Fin.castLE hqt i)
      vertex_injective := ?_
      edge_injective := ?_
      first_edge := ?_
      attaches := ?_ }
  · intro i j hij
    apply Fin.ext
    simpa only [Fin.castLE] using
      congrArg (fun x => x.val) (T.vertex_injective hij)
  · intro i j hij
    apply Fin.ext
    simpa only [Fin.castLE] using
      congrArg (fun x => x.val) (T.edge_injective hij)
  · simpa only [Fin.castLE] using T.first_edge
  · intro j
    obtain ⟨i, hi⟩ := T.attaches (Fin.castLE hqt j)
    refine ⟨i, ?_⟩
    simpa only [Fin.castLE, Fin.castLT, Fin.succ] using hi

end GoldbergSeymour

end
