/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDeletedMissingReplacementInternal
public import LeanPool.GoldbergSeymour.ScheideReplacementMissingDeletedInternal

/-!
# Scheide Symmetric Missing Internal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem ScheideSymmetricMissingInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    (∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi R.u1 ∨ alpha ∈ MissingColors G phi R.u2) →
      ∃ f : E, phi f = some alpha ∧
        G.ends f = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1)) ∧
    ∀ alpha : Fin k,
      (alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 0) ∨
        alpha ∈ MissingColors G phi (C.blockVertex (D.gammaIndex d) 1)) →
      ∃ f : E, phi f = some alpha ∧ G.ends f = s(R.u1, R.u2) := by
  exact ⟨ScheideReplacementMissingDeletedInternal G k e0 phi T C D d R,
    ScheideDeletedMissingReplacementInternal G k e0 phi T C D d R⟩

end GoldbergSeymour

end
