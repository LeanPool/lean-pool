/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Induced
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM12.Section4Theorem43
import LeanPool.GraphMinor.GM12.Section4ExternalPathBranches
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# The identity embedding for an induced tangle

XII Section 4, page 248, induces a tangle from a drawn subgraph to
its ambient graph by intersecting separations with that subgraph.
When vertex and edge names are already shared, the drawing
embedding is the identity. Its restricted separations are exactly
those intersections. Thus the induced tangle satisfies the control
relation used in the embedded versions of (4.3) and (4.4).
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM10 GM14 GM15

/-- For a literal graph inclusion of the drawing, the induced
tangle is a controlling tangle for the identity embedding. -/
theorem exists_identity_embedding_induced_tangle
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S) {G : Graph S (Set S)}
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) (hΓG : Γ.toGraph ≤ G)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsTangle Γ.toHypergraph θ T) :
    ∃ η : SpanEmbedding Γ G, η.imageGraph = Γ.toGraph ∧ (∀ x, η.vMap x = x) ∧ (∀ e, η.eMap e = e) ∧
      IsControllingTangle G Γ η θ θ
        (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T) T := by
  let η : SpanEmbedding Γ G := {
    imageGraph := Γ.toGraph
    vMap := id
    eMap := id
    imageGraph_le := hΓG
    bijOn_v := bijOn_id _
    bijOn_e := bijOn_id _
    inc_iff := by
      intro e he v hv
      have h := congrArg (fun H : Hypergraph S (Set S) => H.Inc e v)
        (drawing_hypergraph_eq_ofGraph Γ).symm
      change Γ.toGraph.Inc e v = Γ.toHypergraph.Inc e v at h
      change Γ.toGraph.Inc e v ↔ v ∈ closure e
      rw [h]
      exact ⟨fun hi => hi.2.2, fun hi => ⟨he, hv, hi⟩⟩ }
  have hsub : Γ.toHypergraph ≤ Hypergraph.ofGraph G hV hE := by
    rw [drawing_hypergraph_eq_ofGraph Γ]
    exact ofGraph_le_of_subgraph hV hE hΓG
  have hTstar : IsGraphTangle G θ
      (inducedBySubgraph (Hypergraph.ofGraph G hV hE) Γ.toHypergraph θ T) :=
    ⟨hV, hE, inducedBySubgraph_isTangle hsub hT⟩
  refine ⟨η, rfl, fun _ => rfl, fun _ => rfl, ⟨le_rfl, hTstar, hT, ?_⟩⟩
  intro A B hsep hord AH BH hRestr
  have hAV := hRestr.2.1
  have hAE := hRestr.2.2.1
  have hBV := hRestr.2.2.2.1
  have hBE := hRestr.2.2.2.2
  change id '' AH.vertexSet = A.vertexSet ∩ Γ.V at hAV
  change id '' AH.edgeSet = A.edgeSet ∩ Γ.E at hAE
  change id '' BH.vertexSet = B.vertexSet ∩ Γ.V at hBV
  change id '' BH.edgeSet = B.edgeSet ∩ Γ.E at hBE
  rw [image_id] at hAV hAE hBV hBE
  have hAH : AH = A ∩ Γ.toHypergraph :=
    eq_of_le_of_vertexSet_eq_of_edgeSet_eq hRestr.1.left_le
      (inter_le_right hsep.left_le hsub) hAV hAE
  have hBH : BH = B ∩ Γ.toHypergraph :=
    eq_of_le_of_vertexSet_eq_of_edgeSet_eq hRestr.1.right_le
      (inter_le_right hsep.right_le hsub) hBV hBE
  constructor
  · intro hmem
    rw [hAH, hBH]
    exact hmem.2.2
  · intro hmem
    refine ⟨hsep, hord, ?_⟩
    rwa [← hAH, ← hBH]

end GraphMinor.GM12
