/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.GM12.Section4EndPartition
import LeanPool.GraphMinor.GM12.Section4CliqueEdges
import LeanPool.GraphMinor.GM12.Section4IsoIncidence
import LeanPool.GraphMinor.GM12.Section4TargetOrientation

/-!
# Labelling and orienting the clique edges

XII (4.4), pages 251--252, indexes the paths by the pairs of clique
vertices. Relabel the complete graph's edges with those indices and
orient them arbitrarily. When there are at least three vertices,
each vertex receives endpoints from two distinct indexed edges.
These two points supply the control bound at the end of the proof.
-/

public section

namespace GraphMinor.GM12

open Set Graph

/-- Each clique vertex has two distinct incident edges when the
clique has at least three vertices. -/
theorem completeGraph_two_incident_edges {p : ℕ} (hp : 3 ≤ p) :
    ∀ v ∈ (GM16.completeGraph p).vertexSet,
      ∃ e f, e ≠ f ∧ (GM16.completeGraph p).Inc e v ∧ (GM16.completeGraph p).Inc f v := by
  intro v _
  obtain ⟨w, z, hwv, hzv, hwz⟩ := exists_two_other_clique_vertices hp v
  refine ⟨s(v, w), s(v, z), ?_, ⟨w, ⟨hwv.symm, rfl⟩⟩, ⟨z, ⟨hzv.symm, rfl⟩⟩⟩
  intro heq
  rcases Sym2.eq_iff.mp heq with ⟨_, hwz'⟩ | ⟨hvz, _⟩
  · exact hwz hwz'
  · exact hzv hvz.symm

/-- A clique with finitely indexed oriented edges and the two-edge
end witnesses needed in XII (4.4), page 252. -/
theorem exists_oriented_clique_labels {p : ℕ} (hp : 3 ≤ p) :
    ∃ (K : Graph (Fin p) (Fin (p * (p - 1) / 2)))
      (κ : Fin (p * (p - 1) / 2) × Bool → Fin p),
      K.vertexSet = univ ∧ K.edgeSet = univ ∧ Nonempty (Iso K (GM16.completeGraph p)) ∧
      (∀ e v, ¬ K.IsLink e v v) ∧
      (∀ e u v, K.IsLink e u v →
        (κ (e, true) = u ∧ κ (e, false) = v) ∨
        (κ (e, true) = v ∧ κ (e, false) = u)) ∧
      ∀ v ∈ K.vertexSet, ∃ i j, i ≠ j ∧
        ∃ c d : Bool, κ (i, c) = v ∧ κ (j, d) = v := by
  let ε := cliqueEdgeEnumeration p
  let K : Graph (Fin p) (Fin (p * (p - 1) / 2)) := {
    vertexSet := univ
    edgeSet := univ
    IsLink := fun e u v => (GM16.completeGraph p).IsLink (ε e).val u v
    isLink_symm := by intro e he; exact ⟨fun _ _ h => h.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y v w hxy hvw
      exact (GM16.completeGraph p).eq_or_eq_of_isLink_of_isLink hxy hvw
    edge_mem_iff_exists_isLink := by
      intro e
      exact ⟨fun _ => (GM16.completeGraph p).exists_isLink_of_mem_edgeSet (ε e).property,
        fun _ => mem_univ e⟩
    left_mem_of_isLink := by intro e x y h; exact mem_univ x }
  let eEquiv : K.edgeSet ≃ (GM16.completeGraph p).edgeSet := {
    toFun := fun e => ε e.val
    invFun := fun e => ⟨ε.symm e, mem_univ _⟩
    left_inv := fun e => Subtype.ext (ε.symm_apply_apply e.val)
    right_inv := fun e => ε.apply_symm_apply e }
  let φ : Iso K (GM16.completeGraph p) := {
    vertexEquiv := Equiv.refl _
    edgeEquiv := eEquiv
    isLink_iff := fun _ _ _ => Iff.rfl }
  have hloop : ∀ e v, ¬ K.IsLink e v v := by
    intro e v h
    exact h.1 rfl
  have htwo := two_incident_edges_of_iso φ (completeGraph_two_incident_edges hp)
  obtain ⟨κ, hassign, hslots⟩ := exists_target_end_assignment K rfl hloop htwo
  exact ⟨K, κ, rfl, rfl, ⟨φ⟩, hloop, hassign, hslots⟩

end GraphMinor.GM12
