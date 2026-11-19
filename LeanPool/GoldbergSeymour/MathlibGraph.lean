/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import LeanPool.GoldbergSeymour.ThmGS

/-!
# Mathlib multigraph interface

The imported development uses total endpoint pairs on vertex and edge types.
Mathlib uses vertex and edge sets in ambient types. Restricting to these sets
preserves edge identities, incidence, and isolated vertices. This conversion
API connects Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 to Mathlib’s set-based graph vocabulary.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

variable {V E : Type*}

/-- The unordered endpoints of an active Mathlib edge, in its active vertex type. -/
noncomputable def graphEndpointPair (G : Graph V E) (e : G.edgeSet) :
    Sym2 G.vertexSet :=
  let witness := G.exists_isLink_of_mem_edgeSet e.property
  let link := witness.choose_spec.choose_spec
  s(⟨witness.choose, link.left_mem⟩, ⟨witness.choose_spec.choose, link.right_mem⟩)

/-- Endpoint pairs characterize Mathlib links, independently of their chosen ordering. -/
theorem graphEndpointPair_eq_iff (G : Graph V E) (e : G.edgeSet)
    (x y : G.vertexSet) : graphEndpointPair G e = s(x, y) ↔ G.IsLink e.val x.val y.val := by
  classical
  let witness := G.exists_isLink_of_mem_edgeSet e.property
  have link := witness.choose_spec.choose_spec
  constructor
  · intro h
    have endpoints := congrArg (Sym2.map Subtype.val) h
    exact link.isLink_iff_sym2_eq.mpr endpoints
  · intro h
    apply Sym2.eq_iff.mpr
    rcases link.eq_and_eq_or_eq_and_eq h with h | h
    · exact Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · exact Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩

/-- Convert a Mathlib loopless multigraph using its actual vertex and edge sets as types. -/
noncomputable def LooplessMultigraph.ofGraph (G : Graph V E) [G.Loopless] :
    LooplessMultigraph G.vertexSet G.edgeSet where
  ends := graphEndpointPair G
  loopless e v h := ((graphEndpointPair_eq_iff G e v v).mp h).ne rfl

/-- Conversion preserves incidence and keeps each original edge identity. -/
@[simp] theorem LooplessMultigraph.ofGraph_incident (G : Graph V E) [G.Loopless]
    (v : G.vertexSet) (e : G.edgeSet) :
    Incident (LooplessMultigraph.ofGraph G) v e ↔ G.Inc e.val v.val := by
  change v ∈ graphEndpointPair G e ↔ ∃ w, G.IsLink e.val v.val w
  rw [Sym2.mem_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.val, (graphEndpointPair_eq_iff G e v w).mp hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨⟨w, hw.right_mem⟩, (graphEndpointPair_eq_iff G e v ⟨w, hw.right_mem⟩).mpr hw⟩

/-- The Goldberg–Seymour bound applies to every Mathlib loopless graph with finite active sets. -/
theorem goldbergSeymour_ofGraph (G : Graph V E) [G.Loopless]
    [Fintype G.vertexSet] [Fintype G.edgeSet] :
    ChromaticIndex (LooplessMultigraph.ofGraph G) ≤
      max (MaximumDegree (LooplessMultigraph.ofGraph G) + 1)
        (DensityCeil (LooplessMultigraph.ofGraph G)) :=
  ThmGS (LooplessMultigraph.ofGraph G)

end GoldbergSeymour

end
