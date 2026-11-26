/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM12.Section4Distance
import LeanPool.GraphMinor.GM12.Section4Separation
import LeanPool.GraphMinor.GM12.Section4PathFacts
import LeanPool.GraphMinor.GM11.Section6

/-!
# Graph Minors XII, (4.1): paths on a small side

Move the path edges to the small side using X (2.9). By XII (1.1), each
edge is enclosed by a short radial circuit whose original vertices lie
in the separator. Their closed insides cover the nontrivial path.
The circuit-chain calculation bounds the distance by twice the separator
size. The zero-length case follows from the metric's value on the diagonal.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 GM14 Hypergraph

universe u

/-- Graph Minors XII, (4.1), page 248. A path whose vertices lie on a
small side has endpoint distance at most twice the separation order. -/
theorem theorem_4_1_proof {S : Type u} [TopologicalSpace S] [T2Space S]
    (Γ P : Drawing S) (θ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (A B : Hypergraph S (Set S)) (u v : S)
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (hMetric : HasTangleMetric Γ θ T d)
    (hu : u ∈ Γ.V) (hv : v ∈ Γ.V)
    (hP : P.IsPathBetween u v) (hPs : P.IsSubdrawing Γ)
    (hAB : (A, B) ∈ T) (hPV : P.V ⊆ A.vertexSet) :
    d {u} {v} ≤ 2 * separationOrder A B := by
  classical
  let : ConnectedSpace S := hConn
  by_cases huv : u = v
  · subst v
    rw [metric_self hMetric (Or.inl (Or.inl ⟨u, hu, rfl⟩))]
    exact Nat.zero_le _
  obtain ⟨hResp, K, ins, hK, hd, heq⟩ := hMetric
  have hE : Γ.E.Nonempty := by
    obtain ⟨W, _, _, hPE⟩ := hP
    cases W with
    | nil _ => exact (huv rfl).elim
    | @cons a b c e h r =>
      exact ⟨e, hPs.2 (hPE ▸ List.mem_cons_self)⟩
  have hmove := tangle_move_subhypergraph hResp.2.1 hAB
    (subdrawing_toHypergraph_le hPs) hPV
  let A' := A ∪ P.toHypergraph
  let B' := B.deleteEdges P.E
  have hm : (A', B') ∈ T := hmove.1
  have horder : separationOrder A' B' = separationOrder A B := hmove.2
  have hcircuits := (theorem_1_1_proof hS hResp hE hK hd
    (hResp.2.1.isSeparation hm) (hResp.2.1.order_lt hm)).mp hm
  have hex : ∀ e : P.E, ∃ C : Drawing S,
      C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length < 2 * θ ∧
        C.V ∩ Γ.V ⊆ (A' ∩ B').vertexSet ∧ (e : Set S) ⊆ ins C := by
    intro e
    exact hcircuits e.val (Or.inr e.property)
  choose C hC using hex
  have : Finite P.E := P.finite_edges.to_subtype
  have hcover : P.U ⊆ ⋃ e, ins (C e) := path_subset_edge_cover hP huv
    (fun e => ins (C e)) (fun e => (hd _ (hC e).1 (hC e).2.1 (hC e).2.2.1).1.isClosed)
    (fun e => (hC e).2.2.2.2)
  have hpre : IsPreconnected P.U := by
    obtain ⟨f, _⟩ := isLine_of_isPathBetween hP huv
    have h_eq : P.U = (fun z => (f z).val) '' univ := by
      ext x
      exact ⟨fun hx => ⟨f.symm ⟨x, hx⟩, mem_univ _, by simp⟩,
        fun ⟨z, _, hz⟩ => hz ▸ (f z).property⟩
    rw [h_eq]
    exact isPreconnected_univ.image _ (continuous_subtype_val.comp f.continuous).continuousOn
  have huP : u ∈ P.U := by
    obtain ⟨W, _, hV, _⟩ := hP
    apply P.V_subset_U
    rw [hV]
    exact W.start_mem_support
  have hvP : v ∈ P.U := by
    obtain ⟨W, _, hV, _⟩ := hP
    apply P.V_subset_U
    rw [hV]
    exact W.end_mem_support
  have hbound := distance_le_twice_separator_of_circuit_cover
    (⟨hResp.2.1.one_le, hResp.2.1.isSeparation, hResp.2.1.order_lt,
      hResp.2.1.axiom1, hResp.2.1.axiom2⟩ : IsPretangle Γ.toHypergraph θ T)
    hK hd C (fun e => (hC e).1) (fun e => (hC e).2.1)
    (fun e => (hC e).2.2.1) (A' ∩ B').vertexSet_finite (fun e => (hC e).2.2.2.1)
    hpre hcover huP hvP hu hv
  rw [heq {u} (Or.inl (Or.inl ⟨u, hu, rfl⟩)) {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
  exact hbound.trans_eq (congrArg (2 * ·) horder)

end GraphMinor.GM12
