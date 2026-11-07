/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.NormalCycleEdge

/-!
# Trunk Rotation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/--
The coloring shift and cyclic trunk-position agreements specifying a rotation of normal triples. -/
def TrunkRotation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E}
  {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k} {T : TreeSequence G e0}
  (N : NormalGlobalMaximumTriple G k e0 phi T) (j : Fin N.height) (e1 : E)
  (psi : PartialEdgeColoring E k) (T' : TreeSequence G e1)
  (N' : NormalGlobalMaximumTriple G k e1 psi T') : Prop :=
 1 ≤ j.val ∧
  e1 = NormalCycleEdge N j ∧
   psi e1 = none ∧
    (∀ i : Fin j.val,
      psi (NormalCycleEdge N (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
       phi
        (NormalCycleEdge N
         ⟨i.val + 1, by
          have hi := i.isLt
          have hj := j.isLt
          omega⟩)) ∧
     (∀ f : E,
       (∀ i : Fin (j.val + 1), f ≠ NormalCycleEdge N (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
        psi f = phi f) ∧
      T'.length = T.length ∧
       N'.height = N.height ∧
        TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
         (∀ r : Fin (T'.length + 1),
           r.val < N.height →
            ∃ i : Fin N.height,
             i.val = (j.val + r.val) % N.height ∧
              T'.vertex r = T.vertex (Fin.castLE N.height_upper i)) ∧
          (∀ r : Fin (T'.length + 1),
            N.height ≤ r.val → ∃ s : Fin (T.length + 1), s.val = r.val ∧ T'.vertex r = T.vertex s) ∧
           (∀ r : Fin T'.length,
             r.val + 1 < N.height →
              ∃ i : Fin N.height,
               i.val = (j.val + r.val) % N.height ∧ T'.edge r = NormalCycleEdge N i) ∧
            (∀ r : Fin T'.length,
              N.height - 1 ≤ r.val → ∃ s : Fin T.length, s.val = r.val ∧ T'.edge r = T.edge s) ∧
             ∃ pred : Fin N.height,
              pred.val = (j.val + N.height - 1) % N.height ∧ N'.closingEdge = NormalCycleEdge N pred

end GoldbergSeymour

end
