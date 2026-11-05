/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.GoldbergSeymour.IncidentCoreIncidence
public import LeanPool.GoldbergSeymour.IncidentVertexFintype
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.RestrictEdges

/-!
# Incident Core Coloring Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem IncidentCoreColoringTransport {V E : Type*} [Finite V] [Finite E]
    (G : LooplessMultigraph V E) :
    (∀ e f : E, AdjacentEdges (IncidentCore G) e f ↔ AdjacentEdges G e f) ∧
    (∀ (k : ℕ) (phi : PartialEdgeColoring E k),
      IsProperEdgeColoring (IncidentCore G) phi ↔ IsProperEdgeColoring G phi) ∧
    (∀ (F : Finset E) (e f : {e // e ∈ F}),
      AdjacentEdges (RestrictEdges (IncidentCore G) F) e f ↔
        AdjacentEdges (RestrictEdges G F) e f) ∧
    (∀ (F : Finset E) (k : ℕ) (phi : PartialEdgeColoring {e // e ∈ F} k),
      IsProperEdgeColoring (RestrictEdges (IncidentCore G) F) phi ↔
        IsProperEdgeColoring (RestrictEdges G F) phi) := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  have hadj : ∀ e f : E,
      AdjacentEdges (IncidentCore G) e f ↔ AdjacentEdges G e f := by
    intro e f
    unfold AdjacentEdges
    constructor
    · rintro ⟨x, hxe, hxf⟩
      exact ⟨x.1, (IncidentCoreIncidence G x e).1 hxe,
        (IncidentCoreIncidence G x f).1 hxf⟩
    · rintro ⟨v, hve, hvf⟩
      let x : IncidentVertex G := ⟨v, e, hve⟩
      exact ⟨x, (IncidentCoreIncidence G x e).2 hve,
        (IncidentCoreIncidence G x f).2 hvf⟩
  have hproper : ∀ (k : ℕ) (phi : PartialEdgeColoring E k),
      IsProperEdgeColoring (IncidentCore G) phi ↔ IsProperEdgeColoring G phi := by
    intro k phi
    unfold IsProperEdgeColoring
    constructor
    · intro hp e f c hne haf he hf
      exact hp hne ((hadj e f).2 haf) he hf
    · intro hp e f c hne haf he hf
      exact hp hne ((hadj e f).1 haf) he hf
  have hadjF : ∀ (F : Finset E) (e f : {e // e ∈ F}),
      AdjacentEdges (RestrictEdges (IncidentCore G) F) e f ↔
        AdjacentEdges (RestrictEdges G F) e f := by
    intro F e f
    unfold AdjacentEdges
    constructor
    · rintro ⟨x, hxe, hxf⟩
      refine ⟨x.1, ?_, ?_⟩
      · change Incident G x.1 e.1
        exact (IncidentCoreIncidence G x e.1).1 hxe
      · change Incident G x.1 f.1
        exact (IncidentCoreIncidence G x f.1).1 hxf
    · rintro ⟨v, hve, hvf⟩
      let x : IncidentVertex G := ⟨v, e.1, by
        change Incident G v e.1 at hve
        exact hve⟩
      refine ⟨x, ?_, ?_⟩
      · change Incident (IncidentCore G) x e.1
        apply (IncidentCoreIncidence G x e.1).2
        exact hve
      · change Incident (IncidentCore G) x f.1
        apply (IncidentCoreIncidence G x f.1).2
        exact hvf
  have hproperF :
    ∀ (F : Finset E) (k : ℕ) (phi : PartialEdgeColoring {e // e ∈ F} k), IsProperEdgeColoring
        (RestrictEdges (IncidentCore G) F) phi ↔ IsProperEdgeColoring (RestrictEdges G F) phi := by
    intro F k phi
    unfold IsProperEdgeColoring
    constructor
    · intro hp e f c hne haf he hf
      exact hp hne ((hadjF F e f).2 haf) he hf
    · intro hp e f c hne haf he hf
      exact hp hne ((hadjF F e f).1 haf) he hf
  exact ⟨hadj, hproper, hadjF, hproperF⟩

end GoldbergSeymour

end
