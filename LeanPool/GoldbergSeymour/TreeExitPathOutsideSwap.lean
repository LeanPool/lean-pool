/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TreeExitPathTransport
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# Exit paths under outside-tree color swaps

General boundary and path transport facts extracted from Wesley Pegden's Trellis formalization
at 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. The statements require no hierarchy or criticality.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Every color missing on a closed tree is individually closed there. -/
theorem ColoredVertexSetClosed.treeColorSetClosed {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    (closed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) {c : Fin k}
    (missing : c ∈ TreeMissingColors phi T) : TreeColorSetClosed G phi T {c} := by
  classical
  intro color member
  obtain rfl := Finset.mem_singleton.mp member
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f member
  obtain ⟨v, inside, missing⟩ := Finset.mem_biUnion.mp missing
  exact closed (Finset.mem_filter.mp member).1 inside (Finset.mem_filter.mp member).2 missing

/-- An edge incident to an inside and an outside vertex crosses the actual set boundary. -/
theorem BoundaryEdges.mem_of_incident {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {X : Finset V} {f : E} {v w : V}
    (inside : v ∈ X) (outside : w ∉ X) (first : Incident G v f) (second : Incident G w f) :
    f ∈ BoundaryEdges G X := by
  classical
  have different : v ≠ w := by rintro rfl; exact outside inside
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    v, inside, w, outside, (Sym2.mem_and_mem_iff different).mp ⟨first, second⟩⟩

/-- A tree-incident edge on an exit path is a boundary edge. -/
theorem TreeExitPath.incident_mem_boundaryEdges {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} {a b : Fin k} {u v : V}
    {P : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl v)}
    (exit : TreeExitPath T phi a b u v P) {f : E}
    (member : Sum.inr f ∈ P.support) (incident : TreeIncidentEdge T f) :
    f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
  obtain ⟨x, inside, first⟩ := incident
  obtain ⟨w, _, outside, second⟩ := exit.edge_has_outside_vertex T phi a b P f member
  exact BoundaryEdges.mem_of_incident inside outside first second

/-- A boundary edge cannot carry the specified closed color. -/
theorem TreeColorSetClosed.color_ne_of_boundary {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} {c : Fin k}
    (closed : TreeColorSetClosed G phi T {c}) {f : E}
    (boundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet T)) : phi f ≠ some c := by
  intro color
  have member : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) c :=
    Finset.mem_filter.mpr ⟨boundary, color⟩
  rw [closed c (Finset.mem_singleton_self c)] at member
  exact Finset.notMem_empty f member

/-- The outside swap fixes every edge incident to the tree. -/
theorem OutsideTreeColorSwap.eq_of_incident {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a c : Fin k)
    {f : E} (incident : TreeIncidentEdge T f) : OutsideTreeColorSwap T phi a c f = phi f := by
  classical
  simp [OutsideTreeColorSwap, incident]

/-- A third color is unchanged by an outside swap. -/
theorem OutsideTreeColorSwap.other_color_iff {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a c d : Fin k)
    (first : a ≠ d) (second : c ≠ d) (f : E) :
    OutsideTreeColorSwap T phi a c f = some d ↔ phi f = some d := by
  classical
  by_cases incident : TreeIncidentEdge T f
  · simp [OutsideTreeColorSwap, incident]
  · by_cases color : phi f = some a
    · simp [OutsideTreeColorSwap, incident, color, first, second]
    · by_cases other : phi f = some c
      · have different : c ≠ a := by intro equal; exact color (other.trans (congrArg some equal))
        simp [OutsideTreeColorSwap, incident, other, different, first, second]
      · simp [OutsideTreeColorSwap, incident, color, other]

/-- Outside the tree, the new first color comes from the old first color. -/
theorem OutsideTreeColorSwap.old_color_of_new {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a c : Fin k)
    {f : E} (outside : ¬TreeIncidentEdge T f)
    (color : OutsideTreeColorSwap T phi a c f = some c) : phi f = some a := by
  classical
  by_cases first : phi f = some a
  · exact first
  · by_cases second : phi f = some c
    · have equal : a = c := Option.some.inj (by
        have different : c ≠ a := by
          intro equal
          exact first (second.trans (congrArg some equal))
        simpa [OutsideTreeColorSwap, outside, second, different] using color)
      exact second.trans (congrArg some equal.symm)
    · simp [OutsideTreeColorSwap, outside, first, second] at color

/-- An outside missing endpoint remains missing after swapping a closed new color. -/
theorem OutsideTreeColorSwap.missing_of_outside {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a c d : Fin k)
    (first : a ≠ d) (second : c ≠ d) (closed : TreeColorSetClosed G phi T {c})
    {u : V} (outside : u ∉ TreeSequenceVertexSet T)
    (missing : a ∈ MissingColors G phi u ∨ d ∈ MissingColors G phi u) :
    c ∈ MissingColors G (OutsideTreeColorSwap T phi a c) u ∨
      d ∈ MissingColors G (OutsideTreeColorSwap T phi a c) u := by
  classical
  rcases missing with left | right
  · left
    have absent : a ∉ PresentColors G phi u := by simpa [MissingColors] using left
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro present
    obtain ⟨f, incident, color⟩ : ∃ f, Incident G u f ∧
        OutsideTreeColorSwap T phi a c f = some c := by simpa [PresentColors] using present
    by_cases tree : TreeIncidentEdge T f
    · obtain ⟨v, inside, other⟩ := tree
      exact closed.color_ne_of_boundary
        (BoundaryEdges.mem_of_incident inside outside other incident)
        ((OutsideTreeColorSwap.eq_of_incident T phi a c ⟨v, inside, other⟩).symm.trans color)
    · exact absent (by simpa [PresentColors] using
        (show ∃ f, Incident G u f ∧ phi f = some a from
          ⟨f, incident, OutsideTreeColorSwap.old_color_of_new T phi a c tree color⟩))
  · right
    have absent : d ∉ PresentColors G phi u := by simpa [MissingColors] using right
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro present
    obtain ⟨f, incident, color⟩ : ∃ f, Incident G u f ∧
        OutsideTreeColorSwap T phi a c f = some d := by simpa [PresentColors] using present
    exact absent (by simpa [PresentColors] using
      (show ∃ f, Incident G u f ∧ phi f = some d from
        ⟨f, incident, (OutsideTreeColorSwap.other_color_iff T phi a c d first second f).mp color⟩))

/-- Every actual exit-path edge remains in the incidence graph after the outside swap. -/
theorem TreeExitPath.outsideSwap_edges {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} {a c d : Fin k} {u v : V}
    {P : (TwoColorIncidenceGraph G phi a d).Walk (Sum.inl u) (Sum.inl v)}
    (exit : TreeExitPath T phi a d u v P) (first : a ≠ d) (second : c ≠ d)
    (closed : TreeColorSetClosed G phi T {a}) :
    ∀ z ∈ P.edges, z ∈ (TwoColorIncidenceGraph G (OutsideTreeColorSwap T phi a c) c d).edgeSet := by
  classical
  have preserve {w : V} {f : E} (member : Sum.inr f ∈ P.support)
      (adjacent : (TwoColorIncidenceGraph G phi a d).Adj (Sum.inl w) (Sum.inr f)) :
      (TwoColorIncidenceGraph G (OutsideTreeColorSwap T phi a c) c d).Adj
        (Sum.inl w) (Sum.inr f) := by
    refine ⟨adjacent.1, ?_⟩
    by_cases incident : TreeIncidentEdge T f
    · exact Or.inr ((OutsideTreeColorSwap.eq_of_incident T phi a c incident).trans
        (adjacent.2.resolve_left (closed.color_ne_of_boundary
          (exit.incident_mem_boundaryEdges member incident))))
    · rcases adjacent.2 with color | color
      · exact Or.inl (by simp [OutsideTreeColorSwap, incident, color])
      · exact Or.inr ((OutsideTreeColorSwap.other_color_iff T phi a c d first second f).mpr color)
  intro z member
  induction z using Sym2.inductionOn with
  | _ x y =>
    have adjacent := (SimpleGraph.mem_edgeSet _).mp (P.edges_subset_edgeSet member)
    have left := P.fst_mem_support_of_mem_edges member
    have right := P.snd_mem_support_of_mem_edges member
    apply (SimpleGraph.mem_edgeSet _).mpr
    cases x with
    | inl w =>
      cases y with
      | inl z => exact adjacent.elim
      | inr f => exact preserve right adjacent
    | inr f =>
      cases y with
      | inl w => exact (preserve left adjacent.symm).symm
      | inr g => exact adjacent.elim

/-- Transport an exit path to a smaller tree through an outside swap, preserving support and
length. Only the actual trees, coloring, closed colors and endpoint are needed. -/
theorem TreeExitPath.outsideSwap {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (S T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (a c d : Fin k)
    (subset : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet T)
    (first : a ≠ d) (second : c ≠ d)
    (closedFirst : TreeColorSetClosed G phi T {a}) (closedNew : TreeColorSetClosed G phi T {c})
    {u v : V} (P : (TwoColorIncidenceGraph G phi a d).Walk (Sum.inl u) (Sum.inl v))
    (exit : TreeExitPath T phi a d u v P) (inside : v ∈ TreeSequenceVertexSet S) :
    ∃ Q : (TwoColorIncidenceGraph G (OutsideTreeColorSwap T phi a c) c d).Walk
        (Sum.inl u) (Sum.inl v),
      TreeExitPath S (OutsideTreeColorSwap T phi a c) c d u v Q ∧
        Q.support = P.support ∧ Q.length = P.length := by
  have edges := exit.outsideSwap_edges first second closedFirst
  let Q := P.transfer _ edges
  have support : Q.support = P.support := P.support_transfer edges
  have length : Q.length = P.length := P.length_transfer edges
  refine ⟨Q, ⟨exit.1.transfer edges, ?_, ?_, inside, ?_, ?_⟩, support, length⟩
  · exact length ▸ exit.2.1
  · exact fun member => exit.2.2.1 (subset member)
  · exact OutsideTreeColorSwap.missing_of_outside T phi a c d first second closedNew
      exit.2.2.1 exit.2.2.2.2.1
  · intro w member
    rw [support]
    exact exit.2.2.2.2.2 w (subset member)

end GoldbergSeymour

end
