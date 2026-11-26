/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4PathTruncation
import LeanPool.GraphMinor.GM12.Section4BranchUnions
import LeanPool.GraphMinor.GM12.Section4AttachedBranches
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Absorbing external paths into the clique branches

XII (4.4), page 252, retains the terminal edge of each external
path and attaches the remaining path to its first branch. The
remaining path meets the drawn subgraph only at its first endpoint.
It therefore avoids every other branch. Disjointness of the
external paths keeps all attached pieces disjoint. The retained
edges then join the enlarged branches, and are distinct.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface Hypergraph GM09 GM10 GM14

/-- A graph inclusion preserves its finite incidence hypergraph. -/
theorem ofGraph_le_of_subgraph
    {α β : Type*} {G Q : Graph α β} (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hQ : Q ≤ G) :
    Hypergraph.ofGraph Q (hV.subset hQ.vertexSet_mono) (hE.subset hQ.edgeSet_mono) ≤
      Hypergraph.ofGraph G hV hE := by
  refine ⟨hQ.vertexSet_mono, hQ.edgeSet_mono, ?_⟩
  intro e he
  ext x
  change G.Inc e x ↔ Q.Inc e x
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨y, (hQ.isLink_iff he).mpr hxy⟩
  · rintro ⟨y, hxy⟩
    exact ⟨y, (hQ.isLink_iff he).mp hxy⟩

/-- The enlarged branches and their joining edges in XII (4.4),
page 252, for any assignment of disjoint external paths to branches. -/
theorem exists_branches_from_external_paths
    {α β : Type*} {G F : Graph α β} (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {W E : Type*} [Finite E] (A : W → Hypergraph α β)
    (hA : ∀ v, A v ≤ Hypergraph.ofGraph G hV hE ∧
      (A v).vertexSet.Nonempty ∧ IsConnectedSub (A v))
    (hAA : ∀ v w, v ≠ w → Disjoint (A v).vertexSet (A w).vertexSet)
    (hAF : ∀ v, (A v).vertexSet ⊆ F.vertexSet)
    (P : E → Graph α β) (s r : E → α) (left right : E → W)
    (hP : ∀ i, IsHPathWithEnds G F (P i) (s i) (r i))
    (hPP : ∀ i j, i ≠ j → Disjoint (P i).vertexSet (P j).vertexSet)
    (hs : ∀ i, s i ∈ (A (left i)).vertexSet)
    (hr : ∀ i, r i ∈ (A (right i)).vertexSet) :
    ∃ (C : W → Hypergraph α β) (b : E → β),
      (∀ v, C v ≤ Hypergraph.ofGraph G hV hE ∧
        (C v).vertexSet.Nonempty ∧ IsConnectedSub (C v)) ∧
      (∀ v w, v ≠ w → Disjoint (C v).vertexSet (C w).vertexSet) ∧
      (∀ v, A v ≤ C v) ∧ Function.Injective b ∧
      ∀ i, b i ∈ G.edgeSet ∧ ∃ x ∈ (C (left i)).vertexSet,
        ∃ y ∈ (C (right i)).vertexSet, G.IsLink (b i) x y := by
  classical
  have hsplit : ∀ i, ∃ (Q : Graph α β) (b : β) (x : α),
      IsGraphPathWithEnds G Q (s i) x ∧ Q ≤ P i ∧
      Q.vertexSet = (P i).vertexSet \ {r i} ∧ Q.edgeSet = (P i).edgeSet \ {b} ∧
      G.IsLink b x (r i) ∧ b ∈ (P i).edgeSet ∧ r i ∉ Q.vertexSet :=
    fun i => exists_path_without_last_vertex (hP i).2.1 (hP i).2.2.1
  choose Q b x hQ using hsplit
  have hQG : ∀ i, Q i ≤ G := fun i => (hQ i).1.1
  let B : E → Hypergraph α β := fun i =>
    Hypergraph.ofGraph (Q i) (hV.subset (hQG i).vertexSet_mono) (hE.subset (hQG i).edgeSet_mono)
  have hB : ∀ i, B i ≤ Hypergraph.ofGraph G hV hE ∧ IsConnectedSub (B i) := by
    intro i
    exact ⟨ofGraph_le_of_subgraph hV hE (hQG i),
      isConnectedSub_of_graph_path _ _ (hQ i).1⟩
  have hBB : ∀ i j, i ≠ j → Disjoint (B i).vertexSet (B j).vertexSet := by
    intro i j hij
    exact (hPP i j hij).mono (hQ i).2.1.vertexSet_mono (hQ j).2.1.vertexSet_mono
  have hBF : ∀ i, (B i).vertexSet ∩ F.vertexSet = {s i} := by
    intro i
    apply Set.Subset.antisymm
    · rintro z ⟨hzQ, hzF⟩
      have hzP := (hQ i).2.1.vertexSet_mono hzQ
      have hends := (hP i).2.2.2.2.2.1.subset ⟨hzP, hzF⟩
      rcases hends with hzs | hzr
      · exact Set.mem_singleton_iff.mpr hzs
      · exact False.elim ((hQ i).2.2.2.2.2.2 ((Set.mem_singleton_iff.mp hzr) ▸ hzQ))
    · rintro z rfl
      exact ⟨(hQ i).1.left_mem, (hP i).2.2.2.1⟩
  have hmeet : ∀ i, ((A (left i)).vertexSet ∩ (B i).vertexSet).Nonempty :=
    fun i => ⟨s i, hs i, (hQ i).1.left_mem⟩
  have hcross : ∀ i v, v ≠ left i → Disjoint (B i).vertexSet (A v).vertexSet := by
    intro i v hv
    apply Set.disjoint_left.mpr
    intro z hzB hzA
    have hzs := Set.mem_singleton_iff.mp ((hBF i).subset ⟨hzB, hAF v hzA⟩)
    exact Set.disjoint_left.mp (hAA v (left i) hv) hzA (hzs.symm ▸ hs i)
  obtain ⟨C, hC, hCC, hAC, hBC⟩ :=
    exists_branches_with_attached_pieces A B left hA hAA hB hBB hmeet hcross
  refine ⟨C, b, hC, hCC, hAC, ?_, ?_⟩
  · intro i j heq
    by_contra hij
    have hePj : b i ∈ (P j).edgeSet := heq.symm ▸ (hQ j).2.2.2.2.2.1
    have hjlink : (P j).IsLink (b i) (x i) (r i) :=
      ((hP j).2.1.1.isLink_iff hePj).mpr (hQ i).2.2.2.2.1
    exact Set.disjoint_left.mp (hPP i j hij)
      ((hQ i).2.1.vertexSet_mono (hQ i).1.right_mem) hjlink.left_mem
  · intro i
    exact ⟨(hP i).2.1.1.edgeSet_mono (hQ i).2.2.2.2.2.1,
      x i, (hBC i).vertexSet_subset (hQ i).1.right_mem,
      r i, (hAC (right i)).vertexSet_subset (hr i), (hQ i).2.2.2.2.1⟩

end GraphMinor.GM12
