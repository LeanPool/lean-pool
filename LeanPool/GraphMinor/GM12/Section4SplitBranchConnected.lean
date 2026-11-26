/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SplitBranch
public import LeanPool.GraphMinor.Minor.Model
import Mathlib.Combinatorics.Graph.Delete
import LeanPool.GraphMinor.GM12.Section4SplitDrawing

/-!
# The contracted subdivision branches are connected

For the minor recovering the original target in XII (4.3),
page 249, retain the right half of each edge inside the branch
of its right end. Every added midpoint joins directly to that
original vertex. The retained halves avoid every left half, which
will represent the original edges in the minor model.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 Relation

/-- The connected branch graph for contraction of all right
halves in the target replacement of XII (4.3), page 249. -/
theorem splitBranch_connected_subgraph
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {v : S} (hv : v ∈ Γ.V) :
    ∃ K ≤ H.toGraph.deleteEdges (A '' Γ.E),
      K.vertexSet = splitBranch Γ m y v ∧ GraphConnected K := by
  let K := (H.toGraph.deleteEdges (A '' Γ.E)).induce (splitBranch Γ m y v)
  have hcenter : v ∈ splitBranch Γ m y v := Or.inl rfl
  have hreach : ∀ z ∈ splitBranch Γ m y v, ReflTransGen K.Adj v z := by
    rintro z (hzv | ⟨e, ⟨he, hyv⟩, hme⟩)
    · exact hzv ▸ ReflTransGen.refl
    · have hmid : m e ∈ splitBranch Γ m y v :=
        (mem_splitBranch_of_midpoint_iff hd hv he).mpr hyv
      have hl : H.toGraph.IsLink (B e) v (m e) := by
        have h := (splitData_isLink_right hd he).symm
        rwa [hyv] at h
      have hlK : K.IsLink (B e) v (m e) :=
        ⟨⟨hl, split_right_notMem_left_image hd he⟩, hcenter, hmid⟩
      exact hme ▸ ReflTransGen.single ⟨B e, hlK⟩
  refine ⟨K, ?_, rfl, ⟨⟨v, hcenter⟩, ?_⟩⟩
  · apply Graph.induce_le
    exact splitBranch_subset_vertices hd hv
  · intro z hz w hw
    exact (symm (hreach z hz)).trans (hreach w hw)

end GraphMinor.GM12
