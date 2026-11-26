/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Section4
import Mathlib.Algebra.BigOperators.Fin

/-!
# Traversing a chain of radial circuits

For the first distance inequality of XII (4.1), page 248, the circuit
costs may be added by traversing their boundaries. Insert a circuit walk
at a vertex shared with the walk already built. No edge traversal is
added except those of the new circuit, so the lengths add exactly.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- Insert a closed walk at a vertex of another closed walk. The result
contains both drawings and has the sum of their lengths. -/
theorem splice_closed_walks {K : Drawing S} {u v : S}
    (W : GraphWalk K.toGraph u u) (V : GraphWalk K.toGraph v v)
    (hv : v ∈ W.support) :
    ∃ R : GraphWalk K.toGraph u u, R.length = W.length + V.length ∧
      (walkDrawing K W).IsSubdrawing (walkDrawing K R) ∧
      (walkDrawing K V).IsSubdrawing (walkDrawing K R) := by
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hv
  refine ⟨W₁.append (V.append W₂), ?_, ?_, ?_⟩
  · simp only [GraphWalk.length_append]
    omega
  · constructor
    · intro x hx
      simp only [walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append] at hx ⊢
      exact hx.elim Or.inl (fun h => Or.inr (Or.inr h))
    · intro e he
      simp only [walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append] at he ⊢
      exact he.elim Or.inl (fun h => Or.inr (Or.inr h))
  · constructor
    · intro x hx
      simp only [walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append] at hx ⊢
      exact Or.inr (Or.inl hx)
    · intro e he
      simp only [walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append] at he ⊢
      exact Or.inr (Or.inl he)

/-- A circuit can be traversed once from any of its vertices, as a walk
of the ambient drawing. -/
theorem circuit_walk_at {K C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing K) {x : S} (hx : x ∈ C.V) :
    ∃ W : GraphWalk K.toGraph x x, walkDrawing K W = C ∧ W.length = C.length := by
  obtain ⟨W₀, ⟨_, hnd⟩, _, hV, hE⟩ := exists_walk_at hC hx
  obtain ⟨W, hs, he⟩ := hCs.exists_walk_up W₀
  refine ⟨W, Drawing.ext_of_V_E ?_ ?_, ?_⟩
  · rw [walkDrawing_V, hs, hV]
  · rw [walkDrawing_E, he, hE]
  · rw [Drawing.length, hE, ← he]
    have heq : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by
      ext e
      simp
    rw [heq, ncard_coe_finset, List.toFinset_card_of_nodup (he ▸ hnd)]
    rfl

/-- Traverse each circuit of a chain once. Adjacent boundaries share a
vertex, so insertion gives one closed walk covering every circuit. -/
theorem closed_walk_covering_circuit_chain {K : Drawing S} {n : ℕ}
    (C : Fin (n + 1) → Drawing S)
    (hC : ∀ i, (C i).IsCircuit) (hs : ∀ i, (C i).IsSubdrawing K)
    (hmeet : ∀ i : Fin n, ((C i.castSucc).V ∩ (C i.succ).V).Nonempty) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u),
      W.length = ∑ i, (C i).length ∧
      ∀ i, (C i).IsSubdrawing (walkDrawing K W) := by
  induction n with
  | zero =>
    obtain ⟨u, W₀, _, _, hV, _⟩ := hC 0
    have hu : u ∈ (C 0).V := hV ▸ W₀.start_mem_support
    obtain ⟨W, hW, hlen⟩ := circuit_walk_at (hC 0) (hs 0) hu
    refine ⟨u, W, ?_, ?_⟩
    · simpa using hlen
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rw [hW]
      exact ⟨subset_rfl, subset_rfl⟩
  | succ n ih =>
    obtain ⟨u, W, hlen, hcover⟩ := ih (fun i => C i.succ)
      (fun i => hC i.succ) (fun i => hs i.succ) (fun i => hmeet i.succ)
    obtain ⟨x, hx, hx'⟩ := hmeet 0
    have hxW : x ∈ W.support := by
      simpa only [walkDrawing_V, mem_ofPred_eq] using (hcover 0).1 hx'
    obtain ⟨V, hV, hVlen⟩ := circuit_walk_at (hC 0) (hs 0) hx
    obtain ⟨R, hRlen, hWR, hVR⟩ := splice_closed_walks W V hxW
    refine ⟨u, R, ?_, ?_⟩
    · rw [hRlen, hlen, hVlen]
      conv_rhs => rw [Fin.sum_univ_succ]
      exact Nat.add_comm _ _
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [← hV]
        exact hVR
      · exact ⟨(hcover j).1.trans hWR.1, (hcover j).2.trans hWR.2⟩

end GraphMinor.GM12
