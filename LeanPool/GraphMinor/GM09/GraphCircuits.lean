/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Joining and splitting graph circuits

Two paths with the same ends form a circuit when their interiors and edges are disjoint.
Two distinct vertices split a circuit into such paths.
-/

public section

namespace GraphMinor.GM09

open Set Graph Surface

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Circuit Splitting and Joining on `Graph α β` -/

/-- Two internally disjoint and edge-disjoint paths in `G` with the same distinct ends `a, b` form a
circuit `subgraphUnion G P Q` in `G`. -/
theorem isGraphCircuit_subgraphUnion {G P Q : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hQ : IsGraphPathWithEnds G Q a b) (hab : a ≠ b)
    (hV : V(P) ∩ V(Q) = {a, b}) (hE : Disjoint E(P) E(Q)) :
    IsGraphCircuit G (subgraphUnion G P Q) := by
  obtain ⟨hPG, W₁, hW₁, hV₁, hE₁⟩ := hP
  obtain ⟨hQG, W₂, hW₂, hV₂, hE₂⟩ := hQ
  have hl := le_subgraphUnion_left hPG hQG
  have hr := le_subgraphUnion_right hPG hQG
  obtain ⟨X₁, hs₁, he₁⟩ := exists_walk_up_of_le hl W₁
  obtain ⟨X₂, hs₂, he₂⟩ := exists_walk_up_of_le hr W₂.reverse
  have hmem₂ : ∀ x, x ∈ X₂.support ↔ x ∈ W₂.support := by
    intro x
    rw [hs₂, GraphWalk.support_reverse, List.mem_reverse]
  have hmemE₂ : ∀ e, e ∈ X₂.edges ↔ e ∈ W₂.edges := by
    intro e
    rw [he₂, GraphWalk.edges_reverse, List.mem_reverse]
  have hsc := GraphWalk.isSimpleClosed_append_of_lifts hW₁ hW₂ hs₁ hs₂ he₁ he₂
    (by simpa only [hV₁, hV₂] using hV) (by simpa only [hE₁, hE₂] using hE)
  refine ⟨subgraphUnion_le hPG hQG, a, X₁.append X₂, hsc, ?_, ?_, ?_⟩
  · rw [GraphWalk.length_append]
    have : X₁.length ≠ 0 := fun h => hab (GraphWalk.eq_of_length_eq_zero h)
    omega
  · rw [vertexSet_subgraphUnion, hV₁, hV₂]
    ext x
    simp only [mem_union, mem_ofPred_eq, GraphWalk.mem_support_append, hmem₂, hs₁]
  · rw [edgeSet_subgraphUnion hPG hQG, hE₁, hE₂]
    ext e
    simp only [mem_union, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append, hmemE₂, he₁]

/-- Any circuit `C` in `G` and any two distinct vertices `a, b ∈ V(C)` decompose `C` into two
edge-disjoint paths `Q₁, Q₂` between `a` and `b` with `V(Q₁) ∩ V(Q₂) = {a, b}`, nonempty edge
sets, and `subgraphUnion G Q₁ Q₂ = C`. -/
theorem IsGraphCircuit.exists_two_paths {G C : Graph α β} (hC : IsGraphCircuit G C)
    {a b : α} (ha : a ∈ V(C)) (hb : b ∈ V(C)) (hab : a ≠ b) :
    ∃ Q₁ Q₂ : Graph α β,
      Q₁ ≤ C ∧ Q₂ ≤ C ∧
      IsGraphPathWithEnds G Q₁ a b ∧ IsGraphPathWithEnds G Q₂ a b ∧
      E(Q₁).Nonempty ∧ E(Q₂).Nonempty ∧
      V(Q₁) ∩ V(Q₂) = {a, b} ∧ Disjoint E(Q₁) E(Q₂) ∧
      subgraphUnion G Q₁ Q₂ = C := by
  obtain ⟨hCG, u, W, ⟨hnd, hed⟩, -, hV, hE⟩ := hC
  rw [hV] at ha hb
  obtain ⟨R₁, R₂, hS₁, hS₂, htail, hedR, hmemRot, hmemE⟩ :=
    GraphWalk.exists_circuit_split W hnd hed ha hb hab
  have hdisjT := List.nodup_append.mp htail
  have hedD := List.nodup_append.mp hedR
  let Q₁ := walkSubgraph R₁
  let Q₂ := walkSubgraph R₂.reverse
  have hQ₁C : Q₁ ≤ C := walkSubgraph_le R₁
  have hQ₂C : Q₂ ≤ C := walkSubgraph_le R₂.reverse
  have hQ₁_path : IsGraphPathWithEnds G Q₁ a b :=
    (isGraphPathWithEnds_walkSubgraph hS₁).mono hCG
  have hQ₂_path : IsGraphPathWithEnds G Q₂ a b :=
    (isGraphPathWithEnds_walkSubgraph hS₂.reverse).mono hCG
  have hE_ne : ∀ {x y : α} (R : GraphWalk C x y), x ≠ y → E(walkSubgraph R).Nonempty := by
    intro x y R hxy
    have hne : R.edges ≠ [] := by
      intro h
      have : R.length = 0 := by simp [GraphWalk.length, h]
      exact hxy (GraphWalk.eq_of_length_eq_zero this)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨e, by rw [edgeSet_walkSubgraph]; exact he⟩
  refine ⟨Q₁, Q₂, hQ₁C, hQ₂C, hQ₁_path, hQ₂_path, hE_ne R₁ hab, hE_ne R₂.reverse hab, ?_, ?_, ?_⟩
  · rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph]
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [R₁.support_eq_cons] at h₁
      rw [R₂.support_eq_cons] at h₂
      rcases List.mem_cons.mp h₁ with h₁ | h₁
      · exact Or.inl h₁
      · rcases List.mem_cons.mp h₂ with h₂ | h₂
        · exact Or.inr h₂
        · exact (hdisjT.2.2 x h₁ x h₂ rfl).elim
    · rintro (rfl | rfl)
      · exact ⟨R₁.start_mem_support, R₂.end_mem_support⟩
      · exact ⟨R₁.end_mem_support, R₂.start_mem_support⟩
  · rw [edgeSet_walkSubgraph, edgeSet_walkSubgraph]
    refine disjoint_left.mpr fun e he₁ he₂ => ?_
    simp only [mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse] at he₁ he₂
    exact hedD.2.2 e he₁ e he₂ rfl
  · refine (Compatible.of_le_le (subgraphUnion_le (hQ₁C.trans hCG) (hQ₂C.trans hCG)) hCG).ext ?_ ?_
    · rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph, vertexSet_walkSubgraph, hV]
      ext x
      simp only [mem_union, mem_ofPred_eq, GraphWalk.support_reverse, List.mem_reverse]
      rw [← hmemRot x, GraphWalk.mem_support_append]
    · rw [edgeSet_subgraphUnion (hQ₁C.trans hCG) (hQ₂C.trans hCG), edgeSet_walkSubgraph,
        edgeSet_walkSubgraph, hE]
      ext e
      simp only [mem_union, mem_ofPred_eq, GraphWalk.edges_reverse, List.mem_reverse]
      rw [← hmemE e, GraphWalk.edges_append, List.mem_append]

end GraphMinor.GM09
