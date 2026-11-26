/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Restricting a minor model to a copy of a simple graph

The wall in XVI (4.2) is a subgraph of the large square grid.
Keep the branch sets for its vertices and the chosen edges for its
edges. Deleting fewer chosen edges preserves the connected branch
graphs. Thus the grid minor model restricts to a wall minor model.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Function
universe u v w x

private theorem simple_inc {α : Type*} (H : SimpleGraph α) (e : Sym2 α) (v : α) :
    (Graph.ofSimpleGraph H).Inc e v ↔ e ∈ H.edgeSet ∧ v ∈ e := by
  constructor
  · rintro ⟨w, he, hm⟩
    exact ⟨hm, he ▸ Sym2.mem_mk_left _ _⟩
  · rintro ⟨hm, hv⟩
    obtain ⟨w, he⟩ := Sym2.mem_iff_exists.mp hv
    exact ⟨w, he, hm⟩

private theorem simple_no_loop {α : Type*} (H : SimpleGraph α) (e : Sym2 α) (v : α) :
    ¬ (Graph.ofSimpleGraph H).IsLoopAt e v := by
  rintro ⟨he, hm⟩
  rw [he] at hm
  exact (show H.Adj v v from hm).ne rfl

/-- Restrict a simple graph's minor model along an injective graph map. -/
theorem IsMinorModel.restrict_simpleGraph_copy
    {α : Type u} {β : Type v} {ν : Type w} {ξ : Type x}
    {H : SimpleGraph ν} {K : SimpleGraph ξ} {G : Graph α β}
    {ηv : ξ → Set α} {ηe : Sym2 ξ → β}
    (h : IsMinorModel (Graph.ofSimpleGraph K) G ηv ηe)
    (f : ν → ξ) (hf : Injective f)
    (hAdj : ∀ a b, H.Adj a b → K.Adj (f a) (f b)) :
    IsMinorModel (Graph.ofSimpleGraph H) G (ηv ∘ f) (ηe ∘ Sym2.map f) := by
  have hEdges : ∀ e ∈ H.edgeSet, Sym2.map f e ∈ K.edgeSet := by
    intro e he
    induction e with
    | h a b => exact hAdj a b he
  have hInc (e : Sym2 ν) (he : e ∈ H.edgeSet) (a : ν) :
      (Graph.ofSimpleGraph H).Inc e a ↔
        (Graph.ofSimpleGraph K).Inc (Sym2.map f e) (f a) := by
    rw [simple_inc, simple_inc]
    have hMem : f a ∈ Sym2.map f e ↔ a ∈ e := by
      induction e with
      | h b c => simp only [Sym2.map_mk, Sym2.mem_iff, hf.eq_iff]
    rw [hMem]
    exact and_congr (iff_of_true he (hEdges e he)) Iff.rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a _
    exact h.vertex_nonempty (f a) (mem_univ _)
  · intro a _
    exact h.vertex_subset (f a) (mem_univ _)
  · intro e he
    exact h.edge_mem _ (hEdges e he)
  · intro a _ b _ hab
    exact h.vertex_disjoint _ (mem_univ _) _ (mem_univ _) (fun hEq => hab (hf hEq))
  · intro e he e' he' hEq
    exact Sym2.map.injective hf (h.edge_injOn (hEdges e he) (hEdges e' he') hEq)
  · intro a _ e he
    exact (hInc e he a).trans (h.inc_iff (f a) (mem_univ _) (Sym2.map f e) (hEdges e he))
  · intro a _ e he
    refine ⟨fun hl => (simple_no_loop H e a hl).elim, ?_⟩
    intro hall
    have hl := (h.isLoopAt_iff (f a) (mem_univ _) (Sym2.map f e) (hEdges e he)).mpr hall
    exact (simple_no_loop K _ _ hl).elim
  · intro a _
    obtain ⟨L, hL, hVL, hConn⟩ := h.connected (f a) (mem_univ _)
    refine ⟨L, hL.trans ?_, hVL, hConn⟩
    have hImage : (ηe ∘ Sym2.map f) '' E(Graph.ofSimpleGraph H) ⊆ ηe '' E(Graph.ofSimpleGraph K)
      := by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨Sym2.map f e, hEdges e he, rfl⟩
    refine ⟨subset_rfl, ?_⟩
    intro e x y hl
    exact ⟨hl.1, fun he => hl.2 (hImage he)⟩

end GraphMinor.GM16
