/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.IncidentCoreIncidence

/-!
# Incident Core Degree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreDegree {V E : Type*} [Finite V] [Fintype E]
    (G : LooplessMultigraph V E) (x : IncidentVertex G) :
    Degree (IncidentCore G) x = Degree G x.1 := by
  classical
  let _ := Fintype.ofFinite V
  unfold Degree
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact IncidentCoreIncidence G x e

end GoldbergSeymour

end
