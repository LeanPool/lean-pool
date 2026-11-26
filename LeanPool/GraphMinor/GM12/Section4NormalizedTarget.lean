/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Statement
import LeanPool.GraphMinor.GM12.Section4TargetReplacement
import LeanPool.GraphMinor.GM12.Section4FiniteLabels
import LeanPool.GraphMinor.GM12.Section4IsoIncidence
import LeanPool.GraphMinor.Minor.Basic

/-!
# A finite labelled drawable replacement of the target

The first reduction in XII (4.3), page 249, replaces the target
by a drawable loopless graph with at least two incident edges at
each vertex. Build that replacement, enumerate its vertices and
edges, and carry the drawing across the enumeration isomorphism.
The original graph remains a minor of the labelled replacement.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The complete target reduction in XII (4.3), page 249, when a
drawing of the original abstract graph is supplied. -/
theorem exists_normalized_target_replacement
    {α β S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {G : Graph α β} (D : GraphDrawing G S) :
    ∃ (p t : ℕ) (L : Graph (Fin p) (Fin t)) (_D' : GraphDrawing L S),
      L.vertexSet = univ ∧ L.edgeSet = univ ∧ IsIsoMinor G L ∧
        (∀ e v, ¬ L.IsLink e v v) ∧
        ∀ v ∈ L.vertexSet, ∃ e f, e ≠ f ∧ L.Inc e v ∧ L.Inc f v := by
  obtain ⟨H, hminor, hloop, htwo⟩ := exists_loopless_minimum_degree_two_minor hS D.drawing
  have hGminor : IsIsoMinor G H.toGraph := D.iso.isIsoMinor_left hminor
  obtain ⟨p, t, L, hLV, hLE, ⟨φ⟩⟩ := exists_finite_labels H.toGraph H.finite_V H.finite_edges
  exact ⟨p, t, L, ⟨H, φ⟩, hLV, hLE, Iso.isIsoMinor_right hGminor φ.symm,
    loopless_of_iso φ hloop, two_incident_edges_of_iso φ htwo⟩

end GraphMinor.GM12
