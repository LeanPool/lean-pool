/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DensityLowerBound
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.IncidentCoreChromaticIndex
public import LeanPool.GoldbergSeymour.IncidentCoreDensity

/-!
# Incident Core Elementary Transfer

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreElementaryTransfer {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) (hcore : Elementary (IncidentCore G)) :
    Elementary G := by
  unfold Elementary at hcore ⊢
  apply Nat.le_antisymm
  · calc
      ChromaticIndex G = ChromaticIndex (IncidentCore G) :=
        (IncidentCoreChromaticIndex G).1.symm
      _ = DensityCeil (IncidentCore G) := hcore
      _ ≤ DensityCeil G := IncidentCoreDensity G
  · exact DensityLowerBound G

end GoldbergSeymour

end
