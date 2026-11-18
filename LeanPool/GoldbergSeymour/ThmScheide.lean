/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideOrderNineStructuralConfiguration

/-!
# Thm Scheide

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ThmScheide {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (hcritical : Critical G)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hdegree : MaximumDegree G + 2 ≤ ChromaticIndex G)
    (horder : TashkinovOrder G < 11) : Elementary G := by
  classical
  let k := ChromaticIndex G - 1
  have hindex : ChromaticIndex G = k + 1 := by
    dsimp [k]
    omega
  have hkdegree : MaximumDegree G + 1 ≤ k := by
    dsimp [k]
    omega
  by_contra hnonelementary
  obtain ⟨e0, phi, T, ⟨C⟩⟩ :=
    ScheideOrderNineStructuralConfiguration G k hcritical hindex hkdegree
      hnoisolated hnonelementary horder
  exact hnonelementary (ScheideStructuralLemma G k e0 phi T C)

end GoldbergSeymour

end
