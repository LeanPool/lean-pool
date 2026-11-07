/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IncidentVertex

/-!
# Incident Core

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- The multigraph restricted to vertices incident to an edge, retaining every original edge. -/
noncomputable def IncidentCore {V E : Type*} (G : LooplessMultigraph V E) :
    LooplessMultigraph (IncidentVertex G) E := by
  classical
  let coreEnds : E → Sym2 (IncidentVertex G) := fun e =>
    s(⟨(G.ends e).out.1, e, Sym2.out_fst_mem (G.ends e)⟩,
      ⟨(G.ends e).out.2, e, Sym2.out_snd_mem (G.ends e)⟩)
  refine ⟨coreEnds, ?_⟩
  intro e v hloop
  apply G.loopless e v.1
  have hmapped := congrArg (Sym2.map (fun x : IncidentVertex G => x.1)) hloop
  have hout : Sym2.map (fun x : IncidentVertex G => x.1) (coreEnds e) = G.ends e := by
    simp only [coreEnds]
    exact (G.ends e).out_eq
  rw [hout] at hmapped
  exact hmapped

end GoldbergSeymour

end
